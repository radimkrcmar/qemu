/*
 * RISC-V Zkl (KLE, Cryptographic Lockers) architectural state.
 *
 * Minimal prototype: AES-ECB, AES-CTR and AES-GCM Machines only.  See
 * riscv-high-assurance-cryptography, Zkl-ISA-unpriv.adoc.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#ifndef RISCV_ZKL_H
#define RISCV_ZKL_H

#define KL_NUM_LOCKERS      32
/* Largest Content of the implemented Machines: AES256_GCM, five blocks. */
#define KL_CONTENT_MAX      80

/* Smklstatus: the two-bit *llockerstatus field of each locker. */
#define KL_LS_OFF           0
#define KL_LS_INITIAL       1
#define KL_LS_CLEAN         2
#define KL_LS_DIRTY         3
#define KL_LS_ALL_INITIAL   0x5555555555555555ULL

typedef struct RISCVKleLocker {
    uint64_t mdh[2];                    /* MDH[63:0], MDH[127:64] */
    uint8_t content[KL_CONTENT_MAX];    /* serialized Content */
} RISCVKleLocker;

typedef struct RISCVKleState {
    RISCVKleLocker lk[KL_NUM_LOCKERS];
    uint64_t klstart;
    uint64_t klnamedlocker;
    uint8_t siv[16];
    uint8_t impqual[16];
    uint8_t siv2[16];

    /* Smklstatus and Ssklstatus: mllockerstatus, sllockerstatus. */
    uint64_t mllockerstatus;
    uint64_t sllockerstatus;

    /* Context Sealing Key (mklcsk group, or generated at power-on). */
    uint64_t csk[4];
    bool csk_active;
    uint8_t csk_written;                /* bitmap of mklcsk CSRs written */
    uint64_t csk_pending[4];

    /* Software-programmable Locality Secrets. */
    uint64_t mlocality[2];
    uint64_t physbootscrt[2];
    uint64_t slocality[2];
} RISCVKleState;

/*
 * Process-wide secrets, shared by all harts: the power-on CSK of
 * x-zkl-csk-random, which a hart reset keeps, and DevScrt of the HW Binding
 * Group, generated on first use.  Migrated once, as "riscv_zkl_secrets".
 */
typedef struct RISCVKleSecrets {
    uint64_t csk[4];
    uint8_t devscrt[16];
} RISCVKleSecrets;

extern RISCVKleSecrets riscv_zkl_secrets;

#endif
