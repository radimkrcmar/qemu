/*
 * RISC-V GHASH multiplication, shared by Zvkg and the Zkl AES-GCM Machine.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#ifndef RISCV_TCG_GHASH_INTERNAL_H
#define RISCV_TCG_GHASH_INTERNAL_H

static inline uint64_t brev8(uint64_t val)
{
    val = ((val & 0x5555555555555555ull) << 1) |
          ((val & 0xAAAAAAAAAAAAAAAAull) >> 1);
    val = ((val & 0x3333333333333333ull) << 2) |
          ((val & 0xCCCCCCCCCCCCCCCCull) >> 2);
    val = ((val & 0x0F0F0F0F0F0F0F0Full) << 4) |
          ((val & 0xF0F0F0F0F0F0F0F0ull) >> 4);

    return val;
}

/*
 * z = x * h in the GHASH field, on 128-bit strings in the bit order of
 * NIST SP 800-38D, each held as two little-endian 64-bit words (bytes 0-7,
 * then 8-15).  z may be x or h.
 */
static inline void ghash_mul(uint64_t *z, const uint64_t *x,
                             const uint64_t *h)
{
    uint64_t S[2] = {brev8(x[0]), brev8(x[1])};
    uint64_t H[2] = {brev8(h[0]), brev8(h[1])};
    uint64_t Z[2] = {0, 0};

    for (int j = 0; j < 128; j++) {
        if ((S[j / 64] >> (j % 64)) & 1) {
            Z[0] ^= H[0];
            Z[1] ^= H[1];
        }
        bool reduce = ((H[1] >> 63) & 1);
        H[1] = H[1] << 1 | H[0] >> 63;
        H[0] = H[0] << 1;
        if (reduce) {
            H[0] ^= 0x87;
        }
    }

    z[0] = brev8(Z[0]);
    z[1] = brev8(Z[1]);
}

#endif
