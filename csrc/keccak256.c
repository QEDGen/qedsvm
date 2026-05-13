/*
 * Keccak-256 (original Keccak, *not* FIPS-202 SHA-3).
 *
 * Solana uses original Keccak: padding rule `0x01 ... 0x80` (vs SHA-3's
 * `0x06 ... 0x80`). Output is 32 bytes (256 bits), rate = 1088 bits = 136
 * bytes, capacity = 512 bits.
 *
 * Permutation: Keccak-f[1600] (24 rounds, 5x5x64-bit state).
 *
 * Reference: Keccak team spec, https://keccak.team/keccak_specs_summary.html
 * Cross-checked against Firedancer src/ballet/sha3/fd_sha3.c.
 *
 * Public-domain reference style. Pure portable C, no SIMD.
 */

#include <stdint.h>
#include <string.h>
#include <lean/lean.h>

#define KECCAK_ROUNDS 24
#define KECCAK_RATE   136   /* bytes for 256-bit output (1600 - 2*256)/8 */

static const uint64_t keccak_rc[KECCAK_ROUNDS] = {
    0x0000000000000001ULL, 0x0000000000008082ULL,
    0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL,
    0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL,
    0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL,
    0x0000000080000001ULL, 0x8000000080008008ULL
};

static const int keccak_rotc[24] = {
     1,  3,  6, 10, 15, 21, 28, 36, 45, 55,  2, 14,
    27, 41, 56,  8, 25, 43, 62, 18, 39, 61, 20, 44
};

static const int keccak_piln[24] = {
    10,  7, 11, 17, 18,  3,  5, 16,  8, 21, 24,  4,
    15, 23, 19, 13, 12,  2, 20, 14, 22,  9,  6,  1
};

#define ROTL64(x, n) (((x) << (n)) | ((x) >> (64 - (n))))

static uint64_t load64_le(const uint8_t *p) {
    return ((uint64_t)p[0])
         | ((uint64_t)p[1] << 8)
         | ((uint64_t)p[2] << 16)
         | ((uint64_t)p[3] << 24)
         | ((uint64_t)p[4] << 32)
         | ((uint64_t)p[5] << 40)
         | ((uint64_t)p[6] << 48)
         | ((uint64_t)p[7] << 56);
}

static void store64_le(uint8_t *p, uint64_t v) {
    p[0] = (uint8_t)(v);
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
    p[4] = (uint8_t)(v >> 32);
    p[5] = (uint8_t)(v >> 40);
    p[6] = (uint8_t)(v >> 48);
    p[7] = (uint8_t)(v >> 56);
}

static void keccakf(uint64_t st[25]) {
    uint64_t t, bc[5];
    int i, j, r;
    for (r = 0; r < KECCAK_ROUNDS; r++) {
        /* Theta */
        for (i = 0; i < 5; i++)
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        for (i = 0; i < 5; i++) {
            t = bc[(i + 4) % 5] ^ ROTL64(bc[(i + 1) % 5], 1);
            for (j = 0; j < 25; j += 5)
                st[j + i] ^= t;
        }
        /* Rho Pi */
        t = st[1];
        for (i = 0; i < 24; i++) {
            j = keccak_piln[i];
            bc[0] = st[j];
            st[j] = ROTL64(t, keccak_rotc[i]);
            t = bc[0];
        }
        /* Chi */
        for (j = 0; j < 25; j += 5) {
            for (i = 0; i < 5; i++) bc[i] = st[j + i];
            for (i = 0; i < 5; i++)
                st[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
        }
        /* Iota */
        st[0] ^= keccak_rc[r];
    }
}

static void keccak256_raw(const uint8_t *in, size_t inlen, uint8_t out[32]) {
    uint64_t st[25];
    uint8_t buf[KECCAK_RATE];
    size_t i;

    memset(st, 0, sizeof(st));

    /* Absorb full rate-sized blocks */
    while (inlen >= KECCAK_RATE) {
        for (i = 0; i < KECCAK_RATE / 8; i++)
            st[i] ^= load64_le(in + i * 8);
        keccakf(st);
        in += KECCAK_RATE;
        inlen -= KECCAK_RATE;
    }

    /* Final block: copy remaining, append 0x01 (Keccak padding, NOT 0x06),
       zero-fill, set high bit of last byte. */
    memcpy(buf, in, inlen);
    buf[inlen] = 0x01;
    memset(buf + inlen + 1, 0, KECCAK_RATE - inlen - 1);
    buf[KECCAK_RATE - 1] |= 0x80;

    for (i = 0; i < KECCAK_RATE / 8; i++)
        st[i] ^= load64_le(buf + i * 8);

    keccakf(st);

    /* Squeeze first 32 bytes of state, little-endian per lane. */
    for (i = 0; i < 4; i++)
        store64_le(out + i * 8, st[i]);
}

/* Lean FFI entry point.
   Takes a borrowed ByteArray (b_lean_obj_arg → no refcount transfer),
   returns a freshly-allocated 32-byte ByteArray (owned by the caller). */
LEAN_EXPORT lean_obj_res lean_keccak256(b_lean_obj_arg input) {
    size_t inlen = lean_sarray_size(input);
    const uint8_t *in = lean_sarray_cptr(input);
    lean_object *out = lean_alloc_sarray(1, 32, 32);
    keccak256_raw(in, inlen, lean_sarray_cptr(out));
    return out;
}
