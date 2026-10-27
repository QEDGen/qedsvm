def murmur3_32(data: bytes, seed: int = 0) -> int:
    c1, c2, h, n = 0xcc9e2d51, 0x1b873593, seed, len(data)
    rotl = lambda x, r: ((x << r) | (x >> (32 - r))) & 0xffffffff
    for i in range(0, n - n % 4, 4):
        k = int.from_bytes(data[i:i+4], "little")
        k = rotl((k * c1) & 0xffffffff, 15) * c2 & 0xffffffff
        h = (rotl(h ^ k, 13) * 5 + 0xe6546b64) & 0xffffffff
    tail, k = data[n - n % 4:], 0
    for i, b in enumerate(tail): k |= b << (8 * i)
    if tail:
        k = rotl((k * c1) & 0xffffffff, 15) * c2 & 0xffffffff; h ^= k
    h ^= n; h ^= h >> 16; h = h * 0x85ebca6b & 0xffffffff; h ^= h >> 13
    h = h * 0xc2b2ae35 & 0xffffffff; h ^= h >> 16
    return h
if __name__ == "__main__":
    import sys; print(hex(murmur3_32(sys.argv[1].encode())))
