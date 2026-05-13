/*
 * BLAKE3 (sequential, portable, no SIMD).
 *
 * Single-chunk and multi-chunk inputs. Default hashing mode only (no
 * keyed_hash, no derive_key). Output is fixed 32 bytes (the standard
 * BLAKE3 output length; XOF / arbitrary-length output not exposed).
 *
 * Implemented from the BLAKE3 specification:
 *   https://github.com/BLAKE3-team/BLAKE3-specs
 * Cross-checked against the official reference_impl.rs. Test vectors
 * for empty / "abc" / 1024 / 1025 / 2048 bytes verified against the
 * `b3sum` CLI (1.8.5).
 *
 * Wired to `sol_blake3` in `Svm/SBPF/Execute.lean`.
 * Public-domain reference style. Portable C, no SIMD.
 */

#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <lean/lean.h>

#define BLAKE3_OUT_LEN     32
#define BLAKE3_BLOCK_LEN   64
#define BLAKE3_CHUNK_LEN   1024

#define CHUNK_START         1u
#define CHUNK_END           2u
#define PARENT              4u
#define ROOT                8u

static const uint32_t BLAKE3_IV[8] = {
    0x6A09E667UL, 0xBB67AE85UL, 0x3C6EF372UL, 0xA54FF53AUL,
    0x510E527FUL, 0x9B05688CUL, 0x1F83D9ABUL, 0x5BE0CD19UL
};

static const uint8_t MSG_PERMUTATION[16] = {
    2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8
};

static uint32_t load32_le(const uint8_t *p) {
    return (uint32_t)p[0]
         | ((uint32_t)p[1] << 8)
         | ((uint32_t)p[2] << 16)
         | ((uint32_t)p[3] << 24);
}

static void store32_le(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)v;
    p[1] = (uint8_t)(v >> 8);
    p[2] = (uint8_t)(v >> 16);
    p[3] = (uint8_t)(v >> 24);
}

static uint32_t rotr32(uint32_t x, int n) {
    return (x >> n) | (x << (32 - n));
}

static void g(uint32_t state[16], int a, int b, int c, int d,
              uint32_t mx, uint32_t my) {
    state[a] = state[a] + state[b] + mx;
    state[d] = rotr32(state[d] ^ state[a], 16);
    state[c] = state[c] + state[d];
    state[b] = rotr32(state[b] ^ state[c], 12);
    state[a] = state[a] + state[b] + my;
    state[d] = rotr32(state[d] ^ state[a], 8);
    state[c] = state[c] + state[d];
    state[b] = rotr32(state[b] ^ state[c], 7);
}

static void round_fn(uint32_t state[16], const uint32_t m[16]) {
    g(state, 0, 4,  8, 12, m[0],  m[1]);
    g(state, 1, 5,  9, 13, m[2],  m[3]);
    g(state, 2, 6, 10, 14, m[4],  m[5]);
    g(state, 3, 7, 11, 15, m[6],  m[7]);
    g(state, 0, 5, 10, 15, m[8],  m[9]);
    g(state, 1, 6, 11, 12, m[10], m[11]);
    g(state, 2, 7,  8, 13, m[12], m[13]);
    g(state, 3, 4,  9, 14, m[14], m[15]);
}

static void permute(uint32_t m[16]) {
    uint32_t tmp[16];
    for (int i = 0; i < 16; i++)
        tmp[i] = m[MSG_PERMUTATION[i]];
    memcpy(m, tmp, sizeof(tmp));
}

static void compress(const uint32_t chaining_value[8],
                     const uint32_t block_words[16],
                     uint64_t counter,
                     uint32_t block_len,
                     uint32_t flags,
                     uint32_t out[16]) {
    uint32_t state[16];
    for (int i = 0; i < 8; i++) state[i] = chaining_value[i];
    state[8]  = BLAKE3_IV[0];
    state[9]  = BLAKE3_IV[1];
    state[10] = BLAKE3_IV[2];
    state[11] = BLAKE3_IV[3];
    state[12] = (uint32_t)counter;
    state[13] = (uint32_t)(counter >> 32);
    state[14] = block_len;
    state[15] = flags;

    uint32_t m[16];
    memcpy(m, block_words, sizeof(m));

    for (int r = 0; r < 7; r++) {
        round_fn(state, m);
        if (r < 6) permute(m);
    }

    for (int i = 0; i < 8; i++) {
        state[i]     ^= state[i + 8];
        state[i + 8] ^= chaining_value[i];
    }
    memcpy(out, state, sizeof(state));
}

static void words_from_block(uint32_t out[16], const uint8_t block[BLAKE3_BLOCK_LEN]) {
    for (int i = 0; i < 16; i++)
        out[i] = load32_le(block + i * 4);
}

typedef struct {
    uint32_t chaining_value[8];
    uint64_t chunk_counter;
    uint8_t  block[BLAKE3_BLOCK_LEN];
    uint32_t block_len;
    uint32_t blocks_compressed;
    uint32_t flags;
} chunk_state;

static void chunk_init(chunk_state *cs, const uint32_t key[8],
                       uint64_t counter, uint32_t flags) {
    memcpy(cs->chaining_value, key, 32);
    cs->chunk_counter = counter;
    memset(cs->block, 0, BLAKE3_BLOCK_LEN);
    cs->block_len = 0;
    cs->blocks_compressed = 0;
    cs->flags = flags;
}

static uint32_t chunk_start_flag(const chunk_state *cs) {
    return cs->blocks_compressed == 0 ? CHUNK_START : 0;
}

static void chunk_update(chunk_state *cs, const uint8_t *in, size_t inlen) {
    while (inlen > 0) {
        if (cs->block_len == BLAKE3_BLOCK_LEN) {
            uint32_t block_words[16];
            words_from_block(block_words, cs->block);
            uint32_t out[16];
            compress(cs->chaining_value, block_words, cs->chunk_counter,
                     BLAKE3_BLOCK_LEN, cs->flags | chunk_start_flag(cs), out);
            memcpy(cs->chaining_value, out, 32);
            cs->blocks_compressed++;
            memset(cs->block, 0, BLAKE3_BLOCK_LEN);
            cs->block_len = 0;
        }
        size_t want = BLAKE3_BLOCK_LEN - cs->block_len;
        size_t take = inlen < want ? inlen : want;
        memcpy(cs->block + cs->block_len, in, take);
        cs->block_len += (uint32_t)take;
        in += take;
        inlen -= take;
    }
}

typedef struct {
    uint32_t input_chaining_value[8];
    uint32_t block_words[16];
    uint64_t counter;
    uint32_t block_len;
    uint32_t flags;
} output_t;

static output_t chunk_output(const chunk_state *cs) {
    output_t o;
    memcpy(o.input_chaining_value, cs->chaining_value, 32);
    words_from_block(o.block_words, cs->block);
    o.counter   = cs->chunk_counter;
    o.block_len = cs->block_len;
    o.flags     = cs->flags | chunk_start_flag(cs) | CHUNK_END;
    return o;
}

static output_t parent_output(const uint32_t left_cv[8], const uint32_t right_cv[8],
                              const uint32_t key[8], uint32_t flags) {
    output_t o;
    memcpy(o.input_chaining_value, key, 32);
    memcpy(o.block_words,     left_cv,  32);
    memcpy(o.block_words + 8, right_cv, 32);
    o.counter   = 0;
    o.block_len = BLAKE3_BLOCK_LEN;
    o.flags     = flags | PARENT;
    return o;
}

static void output_chaining_value(const output_t *o, uint32_t cv[8]) {
    uint32_t out[16];
    compress(o->input_chaining_value, o->block_words,
             o->counter, o->block_len, o->flags, out);
    memcpy(cv, out, 32);
}

static void output_root_bytes(const output_t *o, uint8_t out_bytes[32]) {
    uint32_t words[16];
    compress(o->input_chaining_value, o->block_words, 0,
             o->block_len, o->flags | ROOT, words);
    for (int i = 0; i < 8; i++)
        store32_le(out_bytes + i * 4, words[i]);
}

typedef struct {
    chunk_state cs;
    uint32_t key[8];
    uint32_t cv_stack[54][8];   /* 2^54 chunks of 1024 bytes = 18 EiB */
    uint8_t  cv_stack_len;
    uint32_t flags;
} blake3_hasher;

static void hasher_init(blake3_hasher *h) {
    memcpy(h->key, BLAKE3_IV, 32);
    chunk_init(&h->cs, h->key, 0, 0);
    h->cv_stack_len = 0;
    h->flags = 0;
}

static void hasher_push_stack(blake3_hasher *h, const uint32_t cv[8]) {
    memcpy(h->cv_stack[h->cv_stack_len], cv, 32);
    h->cv_stack_len++;
}

static void hasher_pop_stack(blake3_hasher *h, uint32_t cv[8]) {
    h->cv_stack_len--;
    memcpy(cv, h->cv_stack[h->cv_stack_len], 32);
}

static void hasher_add_chunk_cv(blake3_hasher *h, uint32_t new_cv[8],
                                uint64_t total_chunks_after) {
    while ((total_chunks_after & 1) == 0) {
        uint32_t left_cv[8];
        hasher_pop_stack(h, left_cv);
        output_t parent = parent_output(left_cv, new_cv, h->key, h->flags);
        output_chaining_value(&parent, new_cv);
        total_chunks_after >>= 1;
    }
    hasher_push_stack(h, new_cv);
}

static void hasher_update(blake3_hasher *h, const uint8_t *in, size_t inlen) {
    while (inlen > 0) {
        size_t consumed_in_chunk =
            (size_t)h->cs.blocks_compressed * BLAKE3_BLOCK_LEN + h->cs.block_len;
        if (consumed_in_chunk == BLAKE3_CHUNK_LEN) {
            output_t o = chunk_output(&h->cs);
            uint32_t chunk_cv[8];
            output_chaining_value(&o, chunk_cv);
            uint64_t next = h->cs.chunk_counter + 1;
            hasher_add_chunk_cv(h, chunk_cv, next);
            chunk_init(&h->cs, h->key, next, h->flags);
            consumed_in_chunk = 0;
        }
        size_t want = BLAKE3_CHUNK_LEN - consumed_in_chunk;
        size_t take = inlen < want ? inlen : want;
        chunk_update(&h->cs, in, take);
        in += take;
        inlen -= take;
    }
}

static void hasher_finalize(blake3_hasher *h, uint8_t out[32]) {
    output_t o = chunk_output(&h->cs);
    while (h->cv_stack_len > 0) {
        uint32_t cv[8];
        output_chaining_value(&o, cv);
        uint32_t left_cv[8];
        hasher_pop_stack(h, left_cv);
        o = parent_output(left_cv, cv, h->key, h->flags);
    }
    output_root_bytes(&o, out);
}

static void blake3_raw(const uint8_t *in, size_t inlen, uint8_t out[32]) {
    blake3_hasher h;
    hasher_init(&h);
    hasher_update(&h, in, inlen);
    hasher_finalize(&h, out);
}

/* Lean FFI entry point.
   Takes a borrowed ByteArray (b_lean_obj_arg → no refcount transfer),
   returns a freshly-allocated 32-byte ByteArray (owned by the caller). */
LEAN_EXPORT lean_obj_res lean_blake3(b_lean_obj_arg input) {
    size_t inlen = lean_sarray_size(input);
    const uint8_t *in = lean_sarray_cptr(input);
    lean_object *out = lean_alloc_sarray(1, 32, 32);
    blake3_raw(in, inlen, lean_sarray_cptr(out));
    return out;
}
