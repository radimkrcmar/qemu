/*
 * RISC-V Zkl (KLE, Cryptographic Lockers) unit model.
 *
 * A minimal implementation of the KLE Unprivileged and Privileged
 * Architecture (riscv-high-assurance-cryptography 9c5ce797a889, after Zkl
 * v0.6) covering:
 *   - Zkl common instructions except kl.restrict*, kl.clone/rename/swap and
 *     kl.derive; Zklv (vector operands), Zklmv and Zklmem;
 *   - the AES128/192/256_ECB, AES128/192/256_CTR and AES128/192/256_GCM
 *     Machines at SCProtection Level A (CTR unless the x-zkl-ctr property
 *     is off, GCM unless x-zkl-gcm is);
 *   - SCC export/import with the AES-256 GCM-SIV variant and Localities;
 *   - Smklstatus and Ssklstatus: mllockerstatus and sllockerstatus, with
 *     the KLE locker-Off exception (unless x-zkl-status is off).
 * Not implemented: Zklio, Zklexpire, Smstateen, the H-extension parts,
 * other Machines (GCM with Set IV among them).  Every encoding, CSR address and
 * exception cause is provisional, as in the specification.
 *
 * Section names and rules GRn in the comments refer to Zkl-ISA-unpriv.adoc,
 * rules MRn to Zkl-ISA-machines.adoc, unless stated otherwise.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include "qemu/osdep.h"
#include "qemu/bitops.h"
#include "qemu/bswap.h"
#include "qemu/guest-random.h"
#include "qemu/cutils.h"
#include "cpu.h"
#include "internals.h"
#include "crypto/aes.h"
#include "exec/helper-proto.h"
#include "accel/tcg/cpu-ldst.h"
#include "accel/tcg/probe.h"
#include "vector_internals.h"
#include "ghash_internal.h"
#include "zkl_internal.h"

/* State numbers (<<KLE-State-field>>, <<KLE-SC-sealing-status>>). */
enum {
    KL_ST_UNCONFIGURED = 0,
    KL_ST_READY = 1,
    KL_ST_OPERATE = 2,
    KL_ST_HASH_ABSORB = 2,      /* GCM; the number of CTR's Operate */
    KL_ST_HASH_VERIFY = 5,
    KL_ST_ENCRYPT = 7,
    KL_ST_DECRYPT = 8,
    KL_ST_ENC_LAST_BLOCK = 9,
    KL_ST_DEC_LAST_BLOCK = 10,
    KL_ST_ENC_TAG_FINALIZE = 11,
    KL_ST_DEC_TAG_FINALIZE = 12,
    KL_SET_AUX_VALUE = 13,      /* CTR: an operation; GCM: a State */
    KL_ST_SUCCESS = 46,
    KL_ST_FAILURE = 47,
    KL_ST_UNSUPPORTED = 48,
    KL_ST_INVALID = 49,
    KL_ST_PRIV_VIOLATION = 52,
    KL_ST_MGMT_AUTH = 51,
    KL_ST_EXPIRED = 53,
    KL_CFG_PROVISIONING = 56,
    KL_CFG_EXPORTING = 57,
    KL_CFG_IMPORTING = 58,
    KL_CFG_PPI_EXPORTING = 59,
    KL_CFG_PPI_IMPORTING = 60,
    KL_CFG_MANAGEMENT_END = 63,
    KL_CFG_CLEAR_ADS = 64,
    KL_CFG_CLEARALL = 65,
};

/* klnamedlocker when no locker is named. */
#define KL_NONE         KL_NUM_LOCKERS
/* A locker operand naming the named locker, KLNL (GR8). */
#define KLNL            (-1)

/*
 * Machines implemented: Type 0/1/2 (AES-128/192/256), Mode 0 (ECB), 1 (CTR),
 * 4 (GCM).
 */
#define KL_M_AES128_ECB 0x000
#define KL_M_AES192_ECB 0x010
#define KL_M_AES256_ECB 0x020
#define KL_M_AES128_CTR 0x001
#define KL_M_AES192_CTR 0x011
#define KL_M_AES256_CTR 0x021
#define KL_M_AES128_GCM 0x004
#define KL_M_AES192_GCM 0x014
#define KL_M_AES256_GCM 0x024

/* MDH fields (<<KLE-metadata-header>>), as (lo, width) over 128 bits. */
#define F_MACHINE       0, 12
#define F_POLICY        12, 2
#define F_MEXT          14, 2
#define F_SCPROT        16, 2
#define F_STATE         18, 6
#define F_STATEEXT      24, 4
#define F_KEYTYPE       28, 2
#define F_AUXDATALEN    32, 14
#define F_ADSDROPPED    47, 1
#define F_MACHINEUSE    48, 14
#define F_VERSION       62, 2
#define F_USAGEPOLICY   64, 5
#define F_LOCALITY      69, 9
#define F_AUXINFO       80, 16
#define F_EXPIRATION    96, 20

/* Reserved bits: 31:30, 46, 79:78, 127:116. */
#define MDH_RSV_LO      (MAKE_64BIT_MASK(30, 2) | BIT_ULL(46))
#define MDH_RSV_HI      (MAKE_64BIT_MASK(14, 2) | MAKE_64BIT_MASK(52, 12))

static uint64_t mdh_get(const uint64_t *m, int lo, int len)
{
    return extract64(m[lo / 64], lo % 64, len);
}

static void mdh_set(uint64_t *m, int lo, int len, uint64_t v)
{
    m[lo / 64] = deposit64(m[lo / 64], lo % 64, len, v);
}

#define GET(m, f)       mdh_get((m), f)
#define SET(m, f, v)    mdh_set((m), f, (v))

static bool st_valid(int st)        { return st >= 1 && st <= 47; }
static bool st_error(int st)        { return st >= 48 && st <= 55; }
static bool st_complete(int st)     { return st >= 1 && st <= 55; }
static bool st_config(int st)       { return st >= 56; }

static bool st_base_pi(int st)
{
    return st == KL_CFG_PROVISIONING || st == KL_CFG_PPI_EXPORTING ||
           st == KL_CFG_PPI_IMPORTING;
}

static bool st_base_scc(int st)
{
    return st == KL_CFG_EXPORTING || st == KL_CFG_IMPORTING;
}

/* ------------------------------------------------------------------ */
/* Machine properties                                                 */

/*
 * Unsupported Metadata (<<KLE-Metadata-validity>>): a Machine,
 * MachinePolicy, MachineExtension and SCProtection Level (A to C) that are
 * not implemented.  The reserved SCProtection value 3, KeyType 2 and 3 and
 * a zero MachinePolicy are invalid instead.
 */
static bool machine_supported(CPURISCVState *env, const uint64_t *m)
{
    int scprot = GET(m, F_SCPROT);

    switch (GET(m, F_MACHINE)) {
    case KL_M_AES128_ECB:
    case KL_M_AES192_ECB:
    case KL_M_AES256_ECB:
        break;
    case KL_M_AES128_CTR:
    case KL_M_AES192_CTR:
    case KL_M_AES256_CTR:
        if (!riscv_cpu_cfg(env)->zkl_ctr) {
            return false;
        }
        break;
    case KL_M_AES128_GCM:
    case KL_M_AES192_GCM:
    case KL_M_AES256_GCM:
        if (!riscv_cpu_cfg(env)->zkl_gcm) {
            return false;
        }
        break;
    default:
        return false;
    }
    return GET(m, F_MEXT) == 0 && scprot != 1 && scprot != 2;
}

/* CTR (Zkl-ISA-machines.adoc <<KLE-keystream-modes>>). */
static bool machine_is_ctr(const uint64_t *m)
{
    return (GET(m, F_MACHINE) & 0xf) == 1;
}

/* GCM (Zkl-ISA-machines.adoc <<KLE-GCM-mode>>); neither: ECB. */
static bool machine_is_gcm(const uint64_t *m)
{
    return (GET(m, F_MACHINE) & 0xf) == 4;
}

/* Key length in bytes; only meaningful when machine_supported(). */
static int machine_key_bytes(const uint64_t *m)
{
    return 16 + 8 * (GET(m, F_MACHINE) >> 4);
}

/* <<KLE-length-rule>>: Content of a PI, and Content1 of an SCC. */
static int pi_content_size(const uint64_t *m)
{
    return GET(m, F_KEYTYPE) == 1 ? 16 : ROUND_UP(machine_key_bytes(m), 16);
}

/*
 * Serialized Content: ECB the key or SKID; CTR the key or SKID, IV (96
 * bits) and ctr (32 bits); GCM the key or SKID, J0 and tag (128 bits
 * each), start_ctr (32) and last_blk_len (16); packed and zero-padded to
 * 128 bits.
 */
static int content1_size(const uint64_t *m)
{
    if (machine_is_gcm(m)) {
        return ROUND_UP((GET(m, F_KEYTYPE) == 1 ? 8 : machine_key_bytes(m))
                        + 38, 16);
    }
    if (machine_is_ctr(m)) {
        return ROUND_UP((GET(m, F_KEYTYPE) == 1 ? 8 : machine_key_bytes(m))
                        + 16, 16);
    }
    return pi_content_size(m);
}

static int content2_size(const uint64_t *m)
{
    int aux = GET(m, F_AUXDATALEN);

    return aux >= 2 && !GET(m, F_ADSDROPPED) ? 16 * (aux - 2) : 0;
}

/*
 * ECB supports Ready, Encrypt and Decrypt, CTR Ready and Operate, GCM the
 * States of its transitions, all with StateExtension 0; every Machine
 * supports the Configuration States 56-60 with any StateExtension.
 */
static bool machine_state_supported(const uint64_t *m)
{
    int st = GET(m, F_STATE);

    if (st >= KL_CFG_PROVISIONING && st <= KL_CFG_PPI_IMPORTING) {
        return true;
    }
    if (GET(m, F_STATEEXT) != 0) {
        return false;
    }
    if (machine_is_ctr(m)) {
        return st == KL_ST_READY || st == KL_ST_OPERATE;
    }
    if (machine_is_gcm(m)) {
        return st == KL_ST_READY || st == KL_ST_HASH_ABSORB ||
               st == KL_ST_HASH_VERIFY ||
               (st >= KL_ST_ENCRYPT && st <= KL_SET_AUX_VALUE) ||
               st == KL_ST_SUCCESS || st == KL_ST_FAILURE;
    }
    return st == KL_ST_READY || st == KL_ST_ENCRYPT || st == KL_ST_DECRYPT;
}

/* ------------------------------------------------------------------ */
/* Locality Secrets (<<KLE-Localities>>)                             */

/*
 * HW Binding Group: only ChipFamScrt and DevScrt, which the specification
 * requires, are populated.  An unconfigured entry is replaced by the next
 * configured one of its chain, SiPScrt -> ChipFamScrt -> ChipScrt and
 * OEMScrt -> ProdScrt -> DevScrt, so only ChipScrt has no substitute.
 */
static const uint8_t zkl_chipfamscrt[16] = "QEMU-ZKL-CHIPFAM";

/* DevScrt is generated on first use and migrates in riscv_zkl_secrets. */
static const uint8_t *zkl_devscrt_get(void)
{
    uint8_t *devscrt = riscv_zkl_secrets.devscrt;

    while (buffer_is_zero(devscrt, 16)) {
        qemu_guest_getrandom_nofail(devscrt, 16);
    }
    return devscrt;
}

/* LST_eff[j]; false (and zeros) if unconfigured without a substitute. */
static bool ls_value(CPURISCVState *env, int j, uint8_t out[16])
{
    RISCVKleState *kl = &env->kle;
    const uint64_t *v;

    switch (j) {
    case 0:
    case 1:
        memcpy(out, zkl_chipfamscrt, 16);
        return true;
    case 3:
    case 4:
    case 5:
        memcpy(out, zkl_devscrt_get(), 16);
        return true;
    case 6:
        v = kl->physbootscrt;
        break;
    case 8:
        v = kl->mlocality;
        break;
    case 10:
        v = kl->slocality;
        break;
    default:        /* ChipScrt, VirtBootScrt, HLocality */
        memset(out, 0, 16);
        return false;
    }
    stq_le_p(out, v[0]);
    stq_le_p(out + 8, v[1]);
    return !buffer_is_zero(out, 16);
}

/* Bitmap of the LST entries named by a Locality field, or -1 if invalid. */
static int locality_entries(uint64_t loc)
{
    int e = 0;

    if (loc & 3) {
        e |= BIT((loc & 3) - 1);
    }
    if ((loc >> 2) & 3) {
        e |= BIT(3 + ((loc >> 2) & 3) - 1);
    }
    switch ((loc >> 4) & 3) {
    case 1:
        e |= BIT(6);
        break;
    case 2:
        e |= BIT(7);
        break;
    case 3:
        return -1;
    }
    if (loc & BIT(6)) {
        e |= BIT(8);
    }
    if (loc & BIT(7)) {
        e |= BIT(9);
    }
    if (loc & BIT(8)) {
        e |= BIT(10);
    }
    return e;
}

static bool locality_configured(CPURISCVState *env, uint64_t loc)
{
    int e = locality_entries(loc);
    uint8_t tmp[16];

    if (e < 0) {
        return false;
    }
    for (int j = 0; j <= 10; j++) {
        if ((e & BIT(j)) && !ls_value(env, j, tmp)) {
            return false;
        }
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Validity of Metadata (<<KLE-Metadata-validity>>)                  */

enum mdh_use { USE_PROVISION, USE_IMPORT };

/*
 * Conditions for invalid Metadata.  With check_hi false only bits [63:0]
 * are examined (kl.size Form B).  MachineUse and AuxInfo are not checked
 * (<<KLE-MachineUse>>); custom Machines and system-specific Versions,
 * which GR16 concerns, are not supported.
 */
static bool mdh_invalid(CPURISCVState *env, const uint64_t *m,
                        enum mdh_use use, bool check_hi)
{
    int st = GET(m, F_STATE);
    int aux = GET(m, F_AUXDATALEN);
    bool pi_base = st == KL_ST_UNCONFIGURED || st_base_pi(st);

    if (GET(m, F_VERSION) != 0 || GET(m, F_KEYTYPE) >= 2 ||
        GET(m, F_SCPROT) == 3 || (m[0] & MDH_RSV_LO)) {
        return true;
    }
    if (use == USE_PROVISION ? st != KL_ST_UNCONFIGURED
                             : st == KL_ST_UNCONFIGURED || st >= 61) {
        return true;
    }
    if (st == 54 || st == 55 || st == KL_ST_EXPIRED) {
        return true;
    }
    if (st != KL_ST_UNCONFIGURED && !st_error(st) &&
        !machine_state_supported(m)) {
        return true;
    }
    if (aux == 1 || (pi_base && (aux || GET(m, F_ADSDROPPED)))) {
        return true;
    }
    if (GET(m, F_POLICY) == 0) {
        return true;
    }
    if (check_hi) {
        if ((m[1] & MDH_RSV_HI) || GET(m, F_EXPIRATION) != 0 ||
            !locality_configured(env, GET(m, F_LOCALITY))) {
            return true;
        }
    }
    return false;
}

/* ------------------------------------------------------------------ */
/* SCC authenticated encryption (<<KLE-SCC-AEAD>>)                   */

typedef struct Blk {
    uint8_t b[16];
} Blk;

/* The key schedule of an AES-256 key held as four 64-bit words. */
static void aes256_expand(const uint64_t *key, AES_KEY *ks)
{
    uint8_t k[32];

    for (int i = 0; i < 4; i++) {
        stq_le_p(k + 8 * i, key[i]);
    }
    AES_set_encrypt_key(k, 256, ks);
    memset(k, 0, sizeof(k));
}

/* SCC_KeyDeriv with the all-zero nonce; enc_key comes expanded. */
static void scc_keyderiv(const uint64_t *csk, AES_KEY *enc_key,
                         uint8_t auth_key[16])
{
    uint8_t in[16] = { 0 }, a[6][16];
    uint64_t k[4];
    AES_KEY ks;

    aes256_expand(csk, &ks);
    for (int i = 0; i < 6; i++) {
        stl_le_p(in, i);
        AES_encrypt(in, a[i], &ks);
    }
    memcpy(auth_key, a[0], 8);
    memcpy(auth_key + 8, a[1], 8);
    for (int i = 0; i < 4; i++) {
        k[i] = ldq_le_p(a[2 + i]);
    }
    aes256_expand(k, enc_key);
    memset(k, 0, sizeof(k));
    memset(a, 0, sizeof(a));
    memset(&ks, 0, sizeof(ks));
}

/*
 * Montmul(a, b) = a * b * x^-128 in GF(2)[x] / (x^128+x^127+x^126+x^121+1),
 * with V[k] the coefficient of x^k (RFC 8452 representation).
 */
static void montmul(const uint8_t *a, const uint8_t *b, uint8_t *r)
{
    uint64_t p[4] = { 0 }, x[2], y[4];

    x[0] = ldq_le_p(a);
    x[1] = ldq_le_p(a + 8);
    y[0] = ldq_le_p(b);
    y[1] = ldq_le_p(b + 8);
    y[2] = y[3] = 0;
    for (int i = 0; i < 128; i++) {
        if ((x[i / 64] >> (i % 64)) & 1) {
            for (int k = 0; k < 4; k++) {
                p[k] ^= y[k];
            }
        }
        y[3] = (y[3] << 1) | (y[2] >> 63);
        y[2] = (y[2] << 1) | (y[1] >> 63);
        y[1] = (y[1] << 1) | (y[0] >> 63);
        y[0] <<= 1;
    }
    /*
     * Divide by x^128: clear the low bit with G, shift right, 128 times.
     * The product has degree below 255, so the result has degree below
     * 128: no further reduction is needed.
     */
    for (int i = 0; i < 128; i++) {
        if (p[0] & 1) {
            p[0] ^= 1;
            p[1] ^= BIT_ULL(121 - 64);
            p[1] ^= BIT_ULL(126 - 64) | BIT_ULL(127 - 64);
            p[2] ^= 1;
        }
        p[0] = (p[0] >> 1) | (p[1] << 63);
        p[1] = (p[1] >> 1) | (p[2] << 63);
        p[2] = (p[2] >> 1) | (p[3] << 63);
        p[3] >>= 1;
    }
    stq_le_p(r, p[0]);
    stq_le_p(r + 8, p[1]);
}

/* SIV of SCC_Encrypt/SCC_Decrypt over AD || P (nonce zero). */
static void scc_tag(const AES_KEY *enc_key, const uint8_t *auth_key,
                    const Blk *ad, int n_ad, const uint8_t *p, int n_p,
                    int sep, uint8_t *siv)
{
    uint8_t acc[16] = { 0 }, t[16];

    for (int i = 0; i < n_ad + n_p; i++) {
        const uint8_t *blk = i < n_ad ? ad[i].b : p + 16 * (i - n_ad);

        memcpy(t, blk, 16);
        if (i == 0 && n_ad && sep == 0) {
            t[5] &= ~0x80;              /* AD_auth[0][47] <- 0 */
        }
        for (int k = 0; k < 16; k++) {
            acc[k] ^= t[k];
        }
        montmul(acc, auth_key, acc);
    }
    acc[15] = (acc[15] & 0x3f) | (sep << 6);   /* 0 @ sep @ S[125:0] */
    AES_encrypt(acc, siv, enc_key);
}

static void scc_ctr(const AES_KEY *enc_key, const uint8_t *siv, int sep,
                    uint8_t *data, int n)
{
    uint8_t cb[16], ks[16];

    for (int i = 0; i < n; i++) {
        memcpy(cb, siv, 16);
        cb[15] = (cb[15] & 0x3f) | 0x80 | (sep << 6);
        stl_le_p(cb, ldl_le_p(siv) + i);
        AES_encrypt(cb, ks, enc_key);
        for (int k = 0; k < 16; k++) {
            data[16 * i + k] ^= ks[k];
        }
    }
}

/* AD = saved_MDH (ADSDropped cleared later) followed by LST_eff[j]. */
static int scc_build_ad(CPURISCVState *env, const uint64_t *mdh, Blk *ad)
{
    int e = locality_entries(GET(mdh, F_LOCALITY));
    int n = 1;

    stq_le_p(ad[0].b, mdh[0]);
    stq_le_p(ad[0].b + 8, mdh[1]);
    for (int j = 0; j <= 10; j++) {
        if (e > 0 && (e & BIT(j))) {
            ls_value(env, j, ad[n++].b);  /* unconfigured: zeros(128) */
        }
    }
    return n;
}

static void scc_seal(CPURISCVState *env, RISCVKleLocker *lk)
{
    AES_KEY enc_key;
    uint8_t auth_key[16];
    Blk ad[12];
    int n_ad = scc_build_ad(env, lk->mdh, ad);
    int n_p = content1_size(lk->mdh) / 16;

    scc_keyderiv(env->kle.csk, &enc_key, auth_key);
    scc_tag(&enc_key, auth_key, ad, n_ad, lk->content, n_p, 0, env->kle.siv);
    scc_ctr(&enc_key, env->kle.siv, 0, lk->content, n_p);
    memset(&enc_key, 0, sizeof(enc_key));
    memset(auth_key, 0, sizeof(auth_key));
}

/* Decrypt and authenticate Content1 in place; zeroes it on failure. */
static bool scc_unseal(CPURISCVState *env, RISCVKleLocker *lk)
{
    AES_KEY enc_key;
    uint8_t auth_key[16], siv[16];
    Blk ad[12];
    int n_ad = scc_build_ad(env, lk->mdh, ad);
    int n_p = content1_size(lk->mdh) / 16;
    bool ok;

    scc_keyderiv(env->kle.csk, &enc_key, auth_key);
    scc_ctr(&enc_key, env->kle.siv, 0, lk->content, n_p);
    scc_tag(&enc_key, auth_key, ad, n_ad, lk->content, n_p, 0, siv);
    ok = !memcmp(siv, env->kle.siv, 16);
    if (!ok) {
        memset(lk->content, 0, sizeof(lk->content));
    }
    memset(&enc_key, 0, sizeof(enc_key));
    memset(auth_key, 0, sizeof(auth_key));
    return ok;
}

/* ------------------------------------------------------------------ */
/* KLE state changes                                                 */

/*
 * mstatus.KLS tracks the lockers and the writable KLE CSRs: a change of
 * klstart or klnamedlocker sets it to Dirty as a locker change does.
 */
static void kl_set_klstart(CPURISCVState *env, uint64_t v)
{
    if (env->kle.klstart != v) {
        env->kle.klstart = v;
        zkl_mark_dirty(env);
    }
}

static void kl_set_named(CPURISCVState *env, uint64_t v)
{
    if (env->kle.klnamedlocker != v) {
        env->kle.klnamedlocker = v;
        zkl_mark_dirty(env);
    }
}

/*
 * A change of locker n (Zkl-ISA-priv.adoc <<KLE-CSR-llockerstatus>>): KLS
 * and every *llockerstatus field in effect become Dirty, that is
 * mllockerstatus below M-mode and sllockerstatus in U-mode too (no H
 * extension).  An instruction never writes the field of its own mode.
 */
static void locker_dirty(CPURISCVState *env, int n)
{
    RISCVKleState *kl = &env->kle;
    uint64_t d = (uint64_t)KL_LS_DIRTY << (2 * n);

    zkl_mark_dirty(env);
    if (env->priv != PRV_M && riscv_cpu_cfg(env)->ext_smklstatus) {
        kl->mllockerstatus |= d;
    }
    if (env->priv == PRV_U && riscv_cpu_cfg(env)->ext_ssklstatus) {
        kl->sllockerstatus |= d;
    }
}

static void locker_zeroize(CPURISCVState *env, int n)
{
    memset(&env->kle.lk[n], 0, sizeof(env->kle.lk[n]));
    locker_dirty(env, n);
}

/*
 * Enter an Error State (GR29): only the MDH is retained.  klnamedlocker
 * keeps its value (GR12).
 */
static void locker_error(CPURISCVState *env, int n, int st)
{
    RISCVKleLocker *lk = &env->kle.lk[n];

    if (st == 54 || st == 55 || st == KL_ST_EXPIRED) {
        st = KL_ST_INVALID;
    }
    memset(lk->content, 0, sizeof(lk->content));
    SET(lk->mdh, F_STATE, st);
    SET(lk->mdh, F_AUXDATALEN, 0);
    SET(lk->mdh, F_ADSDROPPED, 0);
    locker_dirty(env, n);
}

/* A configuration check failed: the MDH holds nothing but State. */
static void locker_fail_open(CPURISCVState *env, int n, int st)
{
    locker_zeroize(env, n);
    SET(env->kle.lk[n].mdh, F_STATE, st);
}

/* CTR: IV (12 bytes), then ctr (little-endian), follow the key. */
static uint8_t *ctr_iv(RISCVKleLocker *lk)
{
    return lk->content + machine_key_bytes(lk->mdh);
}

/* Enter Ready; a CTR Machine sets IV and ctr to 0. */
static void locker_ready(RISCVKleLocker *lk)
{
    SET(lk->mdh, F_STATE, KL_ST_READY);
    if (machine_is_ctr(lk->mdh)) {
        memset(ctr_iv(lk), 0, 16);
    }
}

/* The State of locker n; klnamedlocker = 32 reads as Unconfigured. */
static int locker_state(CPURISCVState *env, int n)
{
    return n < KL_NUM_LOCKERS ? GET(env->kle.lk[n].mdh, F_STATE)
                              : KL_ST_UNCONFIGURED;
}

/* ------------------------------------------------------------------ */
/* Common gates                                                       */

static G_NORETURN void kl_raise(CPURISCVState *env, RISCVException e,
                                uintptr_t ra)
{
    riscv_raise_exception(env, e, ra);
}

static G_NORETURN void kl_illegal(CPURISCVState *env, uintptr_t ra)
{
    kl_raise(env, RISCV_EXCP_ILLEGAL_INST, ra);
}

/*
 * The illegal-instruction ground of the first group that depends on CPU
 * state (KLS Off), then the KLE missing-CSK exception.  The encoding
 * grounds are checked by each instruction before calling this.  The
 * effective data endianness is no ground: SCCs are stored and loaded in
 * little-endian format whatever it is (Zkl-notation.adoc "Endianness").
 */
static void kl_gate(CPURISCVState *env, uintptr_t ra)
{
    if (zkl_kls_off(env)) {
        kl_illegal(env, ra);
    }
    if (!zkl_csk_ready(env)) {
        kl_raise(env, RISCV_EXCP_KL_MISSING_CSK, ra);
    }
}

/*
 * Is locker n Off for this access?  Below M-mode mllockerstatus is in
 * effect, in U-mode sllockerstatus too; 32 (KLNL with no named locker)
 * names no locker.
 */
static bool locker_off(CPURISCVState *env, int n)
{
    RISCVKleState *kl = &env->kle;

    if (n >= KL_NUM_LOCKERS || env->priv == PRV_M) {
        return false;
    }
    if (riscv_cpu_cfg(env)->ext_smklstatus &&
        extract64(kl->mllockerstatus, 2 * n, 2) == KL_LS_OFF) {
        return true;
    }
    return env->priv == PRV_U && riscv_cpu_cfg(env)->ext_ssklstatus &&
           extract64(kl->sllockerstatus, 2 * n, 2) == KL_LS_OFF;
}

/*
 * An access to locker n (KLNL resolved), other than by a destructive
 * configuration instruction: the KLE locker-Off exception after the first
 * group, fatal-error and missing-CSK, before every other condition, so the
 * hardware locker is not consulted (Zkl-ISA-priv.adoc
 * <<KLE-CSR-llockerstatus>>).
 */
static void locker_access(CPURISCVState *env, int n, uintptr_t ra)
{
    if (locker_off(env, n)) {
        kl_raise(env, RISCV_EXCP_KL_LOCKER_OFF, ra);
    }
}

/*
 * A locker operand: Kd, or KLNL (r = 1 with X0, GR3) where @klnl_ok (GR8).
 * Any other r = 1 is reserved.  First group.
 */
static int locker_operand(CPURISCVState *env, int field, bool r,
                          bool klnl_ok, uintptr_t ra)
{
    if (!r) {
        return field;
    }
    if (field || !klnl_ok) {
        kl_illegal(env, ra);
    }
    return KLNL;
}

/* KLNL names the named locker, 32 if none (GR10: as Unconfigured). */
static int locker_resolve(CPURISCVState *env, int n)
{
    return n == KLNL ? env->kle.klnamedlocker : n;
}

/* UsagePolicy (<<KLE-UsagePolicy>>): bits 0-3 deny U, VS, HS, M. */
static bool usage_denied(CPURISCVState *env, const uint64_t *m)
{
    uint64_t up = GET(m, F_USAGEPOLICY);
    int bit;

    switch (env->priv) {
    case PRV_U:
        bit = 0;
        break;
    case PRV_S:
        bit = env->virt_enabled ? 1 : 2;
        break;
    default:
        bit = 3;
        break;
    }
    return up & BIT(bit);
}

/*
 * The conditions on the locker of a usage instruction, in the order of
 * GR39 (no ExpirationDate without Zklexpire).  Returns false when the
 * instruction performs no operation: an Unconfigured locker or one in an
 * Error State (GR20).  @subst_bad, a KLIOBUF substitution, forbidden
 * without Zklio, depends on the State and is only evaluated after it,
 * before the UsagePolicy.
 */
static bool usage_gate(CPURISCVState *env, int n, bool subst_bad,
                       uintptr_t ra)
{
    int st = locker_state(env, n);

    if (st == KL_ST_UNCONFIGURED || st_error(st)) {
        return false;
    }
    if (st_config(st)) {                                    /* GR44 */
        kl_raise(env, RISCV_EXCP_KL_PRIVILEGE_VIOLATION, ra);
    }
    if (subst_bad) {
        kl_illegal(env, ra);
    }
    if (usage_denied(env, env->kle.lk[n].mdh)) {          /* GR13 */
        kl_raise(env, RISCV_EXCP_KL_PRIVILEGE_VIOLATION, ra);
    }
    return true;
}

/* ------------------------------------------------------------------ */
/* Vector operands (Zklv)                                             */

static int vlmul_regs(CPURISCVState *env)
{
    int8_t lmul = sextract32(FIELD_EX64(env->vtype, VTYPE, VLMUL), 0, 3);

    return lmul > 0 ? 1 << lmul : 1;
}

static int vsew_bytes(CPURISCVState *env)
{
    return 1 << FIELD_EX64(env->vtype, VTYPE, VSEW);
}

static uint64_t vlen_bytes(CPURISCVState *env)
{
    return (uint64_t)env->vl * vsew_bytes(env);
}

static uint64_t vstart_bytes(CPURISCVState *env)
{
    return (uint64_t)env->vstart * vsew_bytes(env);
}

/* First-group checks of a vector register (group) operand (GR5, KLV). */
static void vreg_check(CPURISCVState *env, int r, uintptr_t ra)
{
    if (!riscv_cpu_vector_enabled(env) || env->vill ||
        (r % vlmul_regs(env))) {
        kl_illegal(env, ra);
    }
}

/* GR5: an operand of an instruction that produces no vstart value. */
static void vreg_check_no_vstart(CPURISCVState *env, int r, uintptr_t ra)
{
    vreg_check(env, r, ra);
    if (env->vstart) {
        kl_illegal(env, ra);
    }
}

static uint8_t *vreg_base(CPURISCVState *env, int r)
{
    return (uint8_t *)env->vreg + r * riscv_cpu_cfg(env)->vlenb;
}

static uint8_t vreg_ldb(CPURISCVState *env, int r, uint64_t i)
{
    return vreg_base(env, r)[H1(i)];
}

static void vreg_stb(CPURISCVState *env, int r, uint64_t i, uint8_t v)
{
    vreg_base(env, r)[H1(i)] = v;
}

static void vreg_zero(CPURISCVState *env, int r, uint64_t from, uint64_t to)
{
    for (uint64_t i = from; i < to; i++) {
        vreg_stb(env, r, i, 0);
    }
}

static void vreg_retire(CPURISCVState *env, bool wrote)
{
    env->vstart = 0;
    if (wrote) {
        env->mstatus |= MSTATUS_VS;
    }
}

/* The 128-bit MDH in the lowest 128 bits of a vector register (group). */
static void vreg_read_mdh(CPURISCVState *env, int r, uint64_t *m)
{
    for (int w = 0; w < 2; w++) {
        m[w] = 0;
        for (int i = 0; i < 8; i++) {
            m[w] |= (uint64_t)vreg_ldb(env, r, 8 * w + i) << (8 * i);
        }
    }
}

/* GR4: a vector operand carrying an MDH needs VL * SEW >= 128. */
static void vreg_mdh_check(CPURISCVState *env, uintptr_t ra)
{
    if (vlen_bytes(env) < 16) {
        kl_illegal(env, ra);
    }
}

/* ------------------------------------------------------------------ */
/* GPR operands (GR1, GR2; RV64 only)                                 */

static uint64_t gpr_get(CPURISCVState *env, int r)
{
    return r ? env->gpr[r] : 0;
}

static void gpr_set(CPURISCVState *env, int r, uint64_t v)
{
    if (r) {
        env->gpr[r] = v;
    }
}

static void gpr_pair_check(CPURISCVState *env, int r, uintptr_t ra)
{
    if (r & 1) {
        kl_illegal(env, ra);
    }
}

static void gpr_pair_get(CPURISCVState *env, int r, uint64_t *v)
{
    v[0] = r ? env->gpr[r] : 0;
    v[1] = r ? env->gpr[r + 1] : 0;
}

static void gpr_pair_set(CPURISCVState *env, int r, const uint64_t *v)
{
    if (r) {
        env->gpr[r] = v[0];
        env->gpr[r + 1] = v[1];
    }
}

/* ------------------------------------------------------------------ */
/* Serialized image of a locker under management (<<KLE-instruction-mv>>) */

typedef struct Image {
    int content_offset;
    int content_size;
    int image_end;
} Image;

static void image_layout(const uint64_t *m, Image *im)
{
    int st = GET(m, F_STATE);
    int max_admissible;

    if (st_base_pi(st)) {
        im->content_offset = 0;
        im->content_size = pi_content_size(m);
        max_admissible = im->content_size;
    } else {
        im->content_offset = GET(m, F_AUXDATALEN) ? 48 : 16;
        im->content_size = content1_size(m) + content2_size(m);
        max_admissible = content1_size(m);  /* no Content2 is retained */
    }
    im->image_end = im->content_offset + MIN(im->content_size,
                                             max_admissible);
}

static uint8_t *image_byte(CPURISCVState *env, int n, const Image *im,
                           uint64_t off)
{
    RISCVKleState *kl = &env->kle;

    if (off < im->content_offset) {
        uint8_t *regs[3] = { kl->siv, kl->impqual, kl->siv2 };
        return &regs[off / 16][off % 16];
    }
    return &kl->lk[n].content[off - im->content_offset];
}

static void image_write_block(CPURISCVState *env, int n, const Image *im,
                              uint64_t off, const uint8_t *src)
{
    for (int i = 0; i < 16; i++) {
        *image_byte(env, n, im, off + i) = src[i];
    }
}

/* Bytes from image_end on read as zero. */
static void image_read_block(CPURISCVState *env, int n, const Image *im,
                             uint64_t off, uint8_t *dst)
{
    if (off >= im->image_end) {
        memset(dst, 0, 16);
        return;
    }
    for (int i = 0; i < 16; i++) {
        dst[i] = *image_byte(env, n, im, off + i);
    }
}

/*
 * The locker checks of kl.mvin, kl.load (GR42), kl.mvout and kl.store
 * (GR43) on the named locker n, which is neither Unconfigured nor in an
 * Error State: a State that admits the transfer, and klstart a multiple of
 * 16.  Second group.
 */
static void image_check(CPURISCVState *env, int n, bool in, uintptr_t ra)
{
    int st = locker_state(env, n);
    bool ok = in ? st == KL_CFG_PROVISIONING || st == KL_CFG_IMPORTING ||
                   st == KL_CFG_PPI_IMPORTING
                 : st == KL_CFG_EXPORTING || st == KL_CFG_PPI_EXPORTING;

    if (!ok || env->kle.klstart % 16) {
        kl_illegal(env, ra);
    }
}

/* ------------------------------------------------------------------ */
/* kl.mgmt (<<KLE-locker-management>>)                               */

/*
 * The MDH operand ml, read only where the operation needs it (GR4): Form A
 * would take it from the KLIOBUF, a substitution that needs Zklio.  Second
 * group, after the klnamedlocker check.
 */
static void mgmt_read_ml(CPURISCVState *env, int form, int rs1,
                         uint64_t *ml, uintptr_t ra)
{
    if (form == 0) {
        kl_illegal(env, ra);
    }
    if (form == 2) {
        vreg_mdh_check(env, ra);
        vreg_read_mdh(env, rs1, ml);
    } else {
        gpr_pair_get(env, rs1, ml);
    }
}

/* Open a provisioning (56) or an import (58) of locker n with MDH @ml. */
static void mgmt_open_in(CPURISCVState *env, int n, int cmd,
                         const uint64_t *ml, uintptr_t ra)
{
    RISCVKleState *kl = &env->kle;
    RISCVKleLocker *lk = &kl->lk[n];
    int st = GET(ml, F_STATE);

    /* Zeroize; klnamedlocker names the locker, even after an exception. */
    locker_zeroize(env, n);
    kl_set_named(env, n);

    if (cmd == KL_CFG_IMPORTING && st_error(st)) {
        /* Short import path (<<KLE-error-state-transfer>>). */
        memcpy(lk->mdh, ml, sizeof(lk->mdh));
        locker_error(env, n, st);
        return;
    }
    if (cmd == KL_CFG_IMPORTING) {
        memset(kl->siv, 0, sizeof(kl->siv));
        memset(kl->impqual, 0, sizeof(kl->impqual));
        memset(kl->siv2, 0, sizeof(kl->siv2));
    }
    if (!machine_supported(env, ml)) {
        kl_raise(env, RISCV_EXCP_KL_UNSUPPORTED_METADATA, ra);
    }
    if (mdh_invalid(env, ml, cmd == KL_CFG_PROVISIONING ? USE_PROVISION
                                                       : USE_IMPORT, true)) {
        locker_fail_open(env, n, KL_ST_INVALID);
        return;
    }

    /* KLF capacity is never exhausted in this implementation. */
    memcpy(lk->mdh, ml, sizeof(lk->mdh));
    if (cmd == KL_CFG_PROVISIONING) {
        SET(lk->mdh, F_STATEEXT, 0);
        SET(lk->mdh, F_MACHINEUSE, 0);
        SET(lk->mdh, F_STATE, KL_CFG_PROVISIONING);
        return;
    }

    /*
     * <<KLE-SCC-import>> step 5: no ADS is retained by this implementation,
     * so any Content2 is dropped.
     */
    SET(lk->mdh, F_ADSDROPPED, GET(ml, F_AUXDATALEN) >= 2);
    SET(lk->mdh, F_STATE, st_base_pi(st) ? KL_CFG_PPI_IMPORTING
                                         : KL_CFG_IMPORTING);
}

/* Open an export (57) of locker n. */
static void mgmt_open_export(CPURISCVState *env, int n)
{
    RISCVKleLocker *lk = &env->kle.lk[n];
    int st = locker_state(env, n);

    if (st == KL_ST_UNCONFIGURED) {
        kl_set_named(env, KL_NONE);   /* nothing opened (GR37) */
        return;
    }
    kl_set_named(env, n);
    if (st_error(st)) {
        return;         /* nothing opened (<<KLE-error-state-transfer>>) */
    }
    locker_dirty(env, n);
    if (st_valid(st)) {
        scc_seal(env, lk);
        SET(lk->mdh, F_STATE, KL_CFG_EXPORTING);
    } else {
        SET(lk->mdh, F_STATE, st_base_pi(st) ? KL_CFG_PPI_EXPORTING
                                             : KL_CFG_EXPORTING);
    }
}

/* Turn a completed, authenticated or provisioned image into a usable CC. */
static void mgmt_finalize_key(CPURISCVState *env, int n, bool provisioning)
{
    RISCVKleLocker *lk = &env->kle.lk[n];

    if (GET(lk->mdh, F_KEYTYPE) == 1) {
        /*
         * No System Key Store: only the all-ones SKID, at provisioning,
         * resolves (to a random key); an SCC never carries it.
         */
        if (!provisioning || ldq_le_p(lk->content) != UINT64_MAX) {
            locker_error(env, n, KL_ST_INVALID);
            return;
        }
        memset(lk->content, 0, sizeof(lk->content));
        qemu_guest_getrandom_nofail(lk->content, machine_key_bytes(lk->mdh));
        SET(lk->mdh, F_KEYTYPE, 0);
    }
}

/* Complete the management operation open on locker n (63). */
static void mgmt_end(CPURISCVState *env, int n, int form, int rs1,
                     uintptr_t ra)
{
    RISCVKleLocker *lk = &env->kle.lk[n];
    int st = locker_state(env, n);
    uint64_t ml[2];
    int to;

    if (st == KL_ST_UNCONFIGURED) {
        kl_set_named(env, KL_NONE);   /* no operation (GR37) */
        return;
    }
    if (st_error(st)) {
        kl_set_named(env, n);         /* no operation (GR37) */
        return;
    }
    if (st_valid(st)) {
        kl_illegal(env, ra);            /* no management operation open */
    }

    if (st == KL_CFG_PROVISIONING) {
        /*
         * Needs no ml: Forms C and D ignore their operand.  AuxDataLen
         * and ADSDropped are zero, since mdh_invalid() rejected a PI with
         * either at the opening.
         */
        kl_set_named(env, n);
        locker_dirty(env, n);
        SET(lk->mdh, F_STATEEXT, 0);
        SET(lk->mdh, F_MACHINEUSE, 0);
        mgmt_finalize_key(env, n, true);
        if (locker_state(env, n) == KL_CFG_PROVISIONING) {
            locker_ready(lk);
        }
        return;
    }

    /* Completing an import or export restores the State saved in ml. */
    mgmt_read_ml(env, form, rs1, ml, ra);
    to = GET(ml, F_STATE);
    if (st_base_scc(st) ? !(st_complete(to) || st_base_scc(to))
                        : !st_base_pi(to)) {
        kl_illegal(env, ra);
    }
    kl_set_named(env, n);
    locker_dirty(env, n);
    SET(lk->mdh, F_STATE, to);
    if (!st_complete(to)) {
        return;                         /* nested completion */
    }

    /* AD[0] is the held MDH with State restored (ADSDropped cleared). */
    if (!scc_unseal(env, lk)) {
        locker_error(env, n, KL_ST_MGMT_AUTH);
        return;
    }
    if (GET(lk->mdh, F_AUXDATALEN) >= 2) {
        /* The ADS was dropped at opening; no replacement is generated. */
        SET(lk->mdh, F_AUXDATALEN, 0);
    }
    SET(lk->mdh, F_ADSDROPPED, 0);
    if (st_error(to)) {
        locker_error(env, n, to);
        return;
    }
    mgmt_finalize_key(env, n, false);
}

static void kl_mgmt(CPURISCVState *env, int n, int cmd, int form, int rs1,
                    uintptr_t ra)
{
    RISCVKleState *kl = &env->kle;
    uint64_t ml[2];

    /* First group: Form B and 59-62 are reserved; the operand. */
    if (form == 1 || (cmd >= 59 && cmd <= 62)) {
        kl_illegal(env, ra);
    }
    if (form == 3) {
        gpr_pair_check(env, rs1, ra);
    } else if (form == 2) {
        vreg_check_no_vstart(env, rs1, ra);
    }
    kl_gate(env, ra);
    /* Opening a provisioning or an import zeroizes the locker first. */
    if (cmd != KL_CFG_PROVISIONING && cmd != KL_CFG_IMPORTING) {
        locker_access(env, locker_resolve(env, n), ra);
    }

    /* GR11: the klnamedlocker check. */
    if (n == KLNL) {
        n = kl->klnamedlocker;
    } else if (kl->klnamedlocker != n && kl->klnamedlocker != KL_NONE) {
        kl_illegal(env, ra);
    }
    kl_set_klstart(env, 0);
    if (n == KL_NONE) {
        /*
         * KLNL without a named locker: no operation, an opening included
         * (GR9, GR10); the operand is not read (GR37).
         */
        return;
    }

    switch (cmd) {
    case KL_CFG_PROVISIONING:
    case KL_CFG_IMPORTING:
        mgmt_read_ml(env, form, rs1, ml, ra);
        mgmt_open_in(env, n, cmd, ml, ra);
        break;
    case KL_CFG_EXPORTING:
        mgmt_open_export(env, n);       /* ignores the operand */
        break;
    case KL_CFG_MANAGEMENT_END:
        mgmt_end(env, n, form, rs1, ra);
        break;
    default:
        g_assert_not_reached();
    }
}

/* ------------------------------------------------------------------ */
/* AES-GCM (Zkl-ISA-machines.adoc <<KLE-GCM-mode>>)                   */

/*
 * The Serialized Content after the key: J0 and tag, the byte strings of
 * SP 800-38D; start_ctr (32 bits) and last_blk_len (16 bits, in bits),
 * little-endian.  J0 holds the counter block last used, tag the GHASH
 * accumulator and then the tag.  In Set_Aux_Value tag accumulates the IV,
 * and J0's place holds the IV's len, block_base and cumul_len (in bits, at
 * bits 0, 32 and 48).  auth_key = E(0) is a derived field (MR4): each
 * instruction computes it with the key schedule it builds anyway.
 */
#define GCM_TAG         16
#define GCM_START_CTR   32
#define GCM_LAST_BLK    36
#define GCM_IV_LEN      0
#define GCM_IV_BASE     4
#define GCM_IV_CUMUL    6

typedef struct Gcm {
    AES_KEY ks;
    uint8_t h[16];              /* auth_key */
    uint8_t *j0, *tag;
} Gcm;

static uint8_t *gcm_j0(RISCVKleLocker *lk)
{
    return lk->content + machine_key_bytes(lk->mdh);
}

static void gcm_open(Gcm *g, RISCVKleLocker *lk)
{
    static const uint8_t zero[16];

    AES_set_encrypt_key(lk->content, 8 * machine_key_bytes(lk->mdh), &g->ks);
    AES_encrypt(zero, g->h, &g->ks);
    g->j0 = gcm_j0(lk);
    g->tag = g->j0 + GCM_TAG;
}

static void gcm_close(Gcm *g)
{
    memset(&g->ks, 0, sizeof(g->ks));
    memset(g->h, 0, sizeof(g->h));
}

/* x <- Galoismul(x, auth_key) */
static void gcm_mul(Gcm *g, uint8_t *x)
{
    uint64_t a[2] = { ldq_le_p(x), ldq_le_p(x + 8) };
    uint64_t h[2] = { ldq_le_p(g->h), ldq_le_p(g->h + 8) };

    ghash_mul(a, a, h);
    stq_le_p(x, a[0]);
    stq_le_p(x + 8, a[1]);
}

/* absorb(d): tag <- Galoismul(tag ^ d, auth_key) */
static void gcm_absorb(Gcm *g, const uint8_t *d)
{
    for (int i = 0; i < 16; i++) {
        g->tag[i] ^= d[i];
    }
    gcm_mul(g, g->tag);
}

/*
 * The next counter block into J0 (inc32 of its big-endian bytes 12-15) and
 * its keystream; false, with J0 kept, when ctr would reach start_ctr - 1.
 */
static bool gcm_keystream(Gcm *g, uint8_t *ks)
{
    uint32_t ctr = ldl_be_p(g->j0 + 12) + 1;

    if (ctr == ldl_le_p(g->j0 + GCM_START_CTR) - 1) {
        return false;
    }
    stl_be_p(g->j0 + 12, ctr);
    AES_encrypt(g->j0, ks, &g->ks);
    return true;
}

/*
 * Set_Aux_Value: bytes [start, len) of Vs2 continue the IV (process_VLI
 * with b = 128): XORed into tag at block_base, each full block multiplied
 * by auth_key unless the IV has 96 bits; bytes past the IV are ignored.
 * The last byte computes J0 and start_ctr and enters Hash_Absorb.
 */
static void gcm_iv(CPURISCVState *env, Gcm *g, RISCVKleLocker *lk, int vs2,
                   uint64_t start, uint64_t len)
{
    uint32_t ivlen = lduw_le_p(g->j0 + GCM_IV_LEN);
    uint32_t base = lduw_le_p(g->j0 + GCM_IV_BASE);
    uint64_t cumul = ldq_le_p(g->j0 + GCM_IV_CUMUL) & MAKE_64BIT_MASK(0, 48);
    uint8_t lb[8];

    for (uint64_t off = start; off < len && cumul < ivlen; off++) {
        g->tag[base / 8] ^= vreg_ldb(env, vs2, off);
        base += 8;
        cumul += 8;
        if (base == 128) {
            gcm_mul(g, g->tag);         /* never for 96 bits */
            base = 0;
        }
    }
    if (cumul < ivlen) {
        stw_le_p(g->j0 + GCM_IV_BASE, base);
        for (int i = 0; i < 6; i++) {
            g->j0[GCM_IV_CUMUL + i] = cumul >> (8 * i);
        }
        return;
    }
    if (ivlen == 96) {
        memcpy(g->j0, g->tag, 12);
        stl_be_p(g->j0 + 12, 1);
    } else {
        if (base) {
            gcm_mul(g, g->tag);
        }
        stq_be_p(lb, ivlen);            /* the block 0^64 || [len]64 */
        for (int i = 0; i < 8; i++) {
            g->tag[8 + i] ^= lb[i];
        }
        gcm_mul(g, g->tag);
        memcpy(g->j0, g->tag, 16);
    }
    stl_le_p(g->j0 + GCM_START_CTR, ldl_be_p(g->j0 + 12));
    memset(g->tag, 0, 16);
    SET(lk->mdh, F_STATE, KL_ST_HASH_ABSORB);
}

/*
 * Encrypt/Decrypt from *off: per block the next counter, then the
 * ciphertext absorbed (the input in Decrypt, the output in Encrypt).
 * false at the counter limit, with *off at the block not processed.
 */
static bool gcm_text(CPURISCVState *env, Gcm *g, bool enc, int vd, int vs2,
                     uint64_t *off, uint64_t len)
{
    uint8_t blk[16], ks[16];
    bool ok = true;

    for (; *off < len; *off += 16) {
        for (int i = 0; i < 16; i++) {
            blk[i] = vreg_ldb(env, vs2, *off + i);
        }
        if (!gcm_keystream(g, ks)) {
            ok = false;
            break;
        }
        if (!enc) {
            gcm_absorb(g, blk);
        }
        for (int i = 0; i < 16; i++) {
            blk[i] ^= ks[i];
        }
        if (enc) {
            gcm_absorb(g, blk);
        }
        for (int i = 0; i < 16; i++) {
            vreg_stb(env, vd, *off + i, blk[i]);
        }
    }
    memset(blk, 0, sizeof(blk));
    memset(ks, 0, sizeof(ks));
    return ok;
}

/*
 * Enc/Dec_Last_Block, its one kl.exec: last_blk_len bits of input; the
 * output above them is cleared (MR8), the ciphertext absorbed zero-padded.
 */
static bool gcm_last(CPURISCVState *env, Gcm *g, bool enc, int vd, int vs2,
                     uint64_t len)
{
    unsigned lb = lduw_le_p(g->j0 + GCM_LAST_BLK) / 8;
    uint8_t x[16] = { 0 }, o[16] = { 0 }, ks[16];

    if (lb == 0 || !gcm_keystream(g, ks)) {
        return false;                   /* MR10: one final block */
    }
    for (unsigned i = 0; i < lb; i++) {
        x[i] = vreg_ldb(env, vs2, i);
        o[i] = x[i] ^ ks[i];
    }
    gcm_absorb(g, enc ? o : x);
    stw_le_p(g->j0 + GCM_LAST_BLK, 0);
    for (uint64_t i = 0; i < len; i++) {
        vreg_stb(env, vd, i, i < lb ? o[i] : 0);
    }
    memset(ks, 0, sizeof(ks));
    memset(o, 0, sizeof(o));
    return true;
}

/* tag ^= E(J0[95:0] with start_ctr), when the length block is absorbed */
static void gcm_tag_mask(Gcm *g)
{
    uint8_t cb[16];

    memcpy(cb, g->j0, 12);
    stl_be_p(cb + 12, ldl_le_p(g->j0 + GCM_START_CTR));
    AES_encrypt(cb, cb, &g->ks);
    for (int i = 0; i < 16; i++) {
        g->tag[i] ^= cb[i];
    }
}

/*
 * The kl.setst Form of each listed GCM transition (MR1): 0 A, 1 B, 2 C;
 * -1 if not listed.  A Form A kl.setst into Ready is always allowed
 * (GR21).  Same-State transitions: Set_Aux_Value restarts the IV, Hash_
 * Absorb, Encrypt and Decrypt do nothing, a last block replaces its length
 * until processed; a Tag_Finalize cannot repeat (GR22).
 */
static int gcm_setst_form(int st, int imm)
{
    switch (imm) {
    case KL_SET_AUX_VALUE:
        return st == KL_ST_READY || st == KL_SET_AUX_VALUE ? 1 : -1;
    case KL_ST_HASH_ABSORB:
        return st == KL_SET_AUX_VALUE || st == KL_ST_HASH_ABSORB ? 0 : -1;
    case KL_ST_ENCRYPT:
    case KL_ST_DECRYPT:
        return st == KL_ST_HASH_ABSORB || st == imm ? 0 : -1;
    case KL_ST_ENC_LAST_BLOCK:
        return st == KL_ST_ENCRYPT || st == imm ? 1 : -1;
    case KL_ST_DEC_LAST_BLOCK:
        return st == KL_ST_DECRYPT || st == imm ? 1 : -1;
    case KL_ST_ENC_TAG_FINALIZE:
        return st == KL_ST_ENCRYPT || st == KL_ST_ENC_LAST_BLOCK ? 2 : -1;
    case KL_ST_DEC_TAG_FINALIZE:
        return st == KL_ST_DECRYPT || st == KL_ST_DEC_LAST_BLOCK ? 2 : -1;
    case KL_ST_HASH_VERIFY:
        return st == KL_ST_DEC_TAG_FINALIZE ? 2 : -1;
    }
    return -1;
}

/* A usage kl.setst on a GCM locker in a Valid State, past the gate. */
static void gcm_setst(CPURISCVState *env, int n, int imm, int form, int rs1)
{
    RISCVKleLocker *lk = &env->kle.lk[n];
    int st = GET(lk->mdh, F_STATE);
    int policy = GET(lk->mdh, F_POLICY);
    uint8_t *j0 = gcm_j0(lk), v[16], d = 0;
    uint64_t x;
    Gcm g;

    if (imm == KL_ST_READY && form == 0) {             /* GR21, GR26 */
        if (st == KL_SET_AUX_VALUE) {
            memset(j0, 0, 16);          /* an incomplete IV goes (MR9) */
        }
        memset(j0 + GCM_TAG, 0, 16);
        SET(lk->mdh, F_STATE, KL_ST_READY);
        return;
    }
    if (st == KL_ST_SUCCESS || st == KL_ST_FAILURE ||
        gcm_setst_form(st, imm) != form) {
        goto invalid;                                   /* GR27, MR1 */
    }
    if (st == imm && (st == KL_ST_ENC_LAST_BLOCK ||
                      st == KL_ST_DEC_LAST_BLOCK) &&
        !lduw_le_p(j0 + GCM_LAST_BLK)) {
        goto invalid;                                   /* GR22, MR10 */
    }
    if ((imm == KL_ST_ENCRYPT && !(policy & 1)) ||
        (imm == KL_ST_DECRYPT && !(policy & 2))) {
        goto invalid;                                   /* MR11 */
    }
    switch (imm) {
    case KL_SET_AUX_VALUE:              /* Xs: the IV's length in bits */
        x = gpr_get(env, rs1);
        if (x < 8 || x > 8192 || x % 8) {
            goto invalid;
        }
        memset(j0, 0, 32);
        stw_le_p(j0 + GCM_IV_LEN, x);
        break;
    case KL_ST_ENC_LAST_BLOCK:
    case KL_ST_DEC_LAST_BLOCK:          /* Xs: last_blk_len in bits */
        x = gpr_get(env, rs1);
        if (x == 0 || x >= 128 || x % 8) {
            goto invalid;
        }
        stw_le_p(j0 + GCM_LAST_BLK, x);
        break;
    case KL_ST_ENC_TAG_FINALIZE:
    case KL_ST_DEC_TAG_FINALIZE:        /* Vs: the length block */
    case KL_ST_HASH_VERIFY:             /* Vs: the tag received */
        if (vlen_bytes(env) < 16) {
            goto invalid;                               /* MR2, MR7 */
        }
        for (int i = 0; i < 16; i++) {
            v[i] = vreg_ldb(env, rs1, i);
        }
        if (imm == KL_ST_HASH_VERIFY) {
            /* Only the comparison: no key schedule is needed. */
            for (int i = 0; i < 16; i++) {              /* MR15 */
                d |= v[i] ^ j0[GCM_TAG + i];
            }
            imm = d ? KL_ST_FAILURE : KL_ST_SUCCESS;
            break;
        }
        gcm_open(&g, lk);
        gcm_absorb(&g, v);
        gcm_tag_mask(&g);
        gcm_close(&g);
        break;
    case KL_ST_HASH_ABSORB:
        if (st == KL_SET_AUX_VALUE) {
            goto invalid;               /* MR11: the IV is incomplete */
        }
        break;
    }
    SET(lk->mdh, F_STATE, imm);
    return;
invalid:
    locker_error(env, n, KL_ST_INVALID);
}

/* The kl.exec Form of each GCM State: 0 A, 1 B, 2 C; -1 none. */
static int gcm_exec_form(int st)
{
    switch (st) {
    case KL_SET_AUX_VALUE:
    case KL_ST_HASH_ABSORB:
        return 1;
    case KL_ST_ENCRYPT:
    case KL_ST_DECRYPT:
    case KL_ST_ENC_LAST_BLOCK:
    case KL_ST_DEC_LAST_BLOCK:
        return 0;
    case KL_ST_ENC_TAG_FINALIZE:
        return 2;
    }
    return -1;
}

/*
 * kl.exec on a GCM locker in a Valid State, past the gate, over the window
 * [start, len) of KLLEN = len bytes.  Returns where the unwritten part of
 * the output window starts (GR34).
 */
static uint64_t gcm_exec(CPURISCVState *env, int n, int form, int vd,
                         int vs2, uint64_t start, uint64_t len)
{
    RISCVKleLocker *lk = &env->kle.lk[n];
    int st = GET(lk->mdh, F_STATE);
    uint8_t *j0 = gcm_j0(lk);
    uint64_t off = start;
    bool ok = true;
    Gcm g;

    if (gcm_exec_form(st) != form) {
        goto invalid;                                   /* GR23, MR1 */
    }
    /* MR2 before the window (<<KLE-truncation-vs-length>>). */
    if (st == KL_SET_AUX_VALUE) {
        uint64_t cumul = ldq_le_p(j0 + GCM_IV_CUMUL) & MAKE_64BIT_MASK(0, 48);
        uint32_t ivlen = lduw_le_p(j0 + GCM_IV_LEN);

        /* Every transfer of the IV but the last one is whole blocks. */
        if ((len % 16 && cumul + 8 * len < ivlen) || cumul >= ivlen) {
            goto invalid;
        }
    } else if (st == KL_ST_ENC_LAST_BLOCK || st == KL_ST_DEC_LAST_BLOCK) {
        if (8 * len < lduw_le_p(j0 + GCM_LAST_BLK)) {
            goto invalid;
        }
    } else if (st != KL_ST_ENC_TAG_FINALIZE && len % 16) {
        goto invalid;
    }
    if (start >= len) {
        return len;                     /* empty window */
    }
    /* Interruption points: whole blocks, none in a one-output State. */
    if (start % 16 || (start && (st == KL_ST_ENC_LAST_BLOCK ||
                                 st == KL_ST_DEC_LAST_BLOCK ||
                                 st == KL_ST_ENC_TAG_FINALIZE))) {
        goto invalid;
    }

    /* Every GCM kl.exec changes the locker. */
    locker_dirty(env, n);
    gcm_open(&g, lk);
    switch (st) {
    case KL_SET_AUX_VALUE:
        gcm_iv(env, &g, lk, vs2, start, len);
        break;
    case KL_ST_HASH_ABSORB:
        for (uint8_t blk[16]; off < len; off += 16) {
            for (int i = 0; i < 16; i++) {
                blk[i] = vreg_ldb(env, vs2, off + i);
            }
            gcm_absorb(&g, blk);
        }
        break;
    case KL_ST_ENCRYPT:
    case KL_ST_DECRYPT:
        ok = gcm_text(env, &g, st == KL_ST_ENCRYPT, vd, vs2, &off, len);
        break;
    case KL_ST_ENC_LAST_BLOCK:
    case KL_ST_DEC_LAST_BLOCK:
        ok = gcm_last(env, &g, st == KL_ST_ENC_LAST_BLOCK, vd, vs2, len);
        off = ok ? len : 0;
        break;
    case KL_ST_ENC_TAG_FINALIZE:        /* KLLEN may truncate the tag */
        for (off = 0; off < MIN(len, 16); off++) {
            vreg_stb(env, vd, off, g.tag[off]);
        }
        SET(lk->mdh, F_STATE, KL_ST_SUCCESS);
        break;
    }
    gcm_close(&g);
    if (!ok) {
        locker_error(env, n, KL_ST_INVALID);            /* GR67 */
    }
    return off;

invalid:
    locker_error(env, n, KL_ST_INVALID);
    return start;
}

/* ------------------------------------------------------------------ */
/* kl.setst (<<KLE-instruction-setst>>)                              */

static void kl_clearall(CPURISCVState *env)
{
    RISCVKleState *kl = &env->kle;

    memset(kl->lk, 0, sizeof(kl->lk));
    memset(kl->siv, 0, sizeof(kl->siv));
    memset(kl->impqual, 0, sizeof(kl->impqual));
    memset(kl->siv2, 0, sizeof(kl->siv2));
    kl->klstart = 0;
    kl->klnamedlocker = KL_NONE;
    for (int n = 0; n < KL_NUM_LOCKERS; n++) {
        locker_dirty(env, n);
    }
}

/* kl.setnl Xs1, kl.setnli #uimm7 (<<KLE-instruction-get-set-nl>>). */
static void kl_setnl(CPURISCVState *env, int kd, bool r, int form, int rs1,
                     int imm, uintptr_t ra)
{
    uint64_t v;

    if (kd || r) {
        kl_illegal(env, ra);
    }
    if (form == 0 && rs1 == 0) {
        v = imm;
    } else if (form == 1 && imm == 0) {
        v = gpr_get(env, rs1);
    } else {
        kl_illegal(env, ra);
    }
    kl_gate(env, ra);       /* gated as an access to klnamedlocker */
    if (v <= KL_NONE) {
        kl_set_named(env, v);
    }
}

void helper_kl_setst(CPURISCVState *env, uint32_t insn)
{
    uintptr_t ra = GETPC();
    int kd = extract32(insn, 7, 5);
    int rs1 = extract32(insn, 15, 5);
    bool r = extract32(insn, 20, 1);
    int form = extract32(insn, 21, 2);
    int imm = extract32(insn, 25, 7);
    RISCVKleLocker *lk;
    int n, st;

    /* Encoding grounds (first group). */
    if (extract32(insn, 23, 1)) {
        kl_illegal(env, ra);
    }
    if (extract32(insn, 24, 1)) {
        kl_setnl(env, kd, r, form, rs1, imm, ra);
        return;
    }
    if (form == 0 && rs1) {
        kl_illegal(env, ra);
    }
    if (imm == KL_CFG_CLEARALL) {
        /* Form A, K0, r = 0 only; KLNL is reserved with it. */
        if (form || kd || r) {
            kl_illegal(env, ra);
        }
        kl_gate(env, ra);
        kl_clearall(env);
        return;
    }
    /* Every kl.setst but kl.clearall may name KLNL (GR8). */
    n = locker_operand(env, kd, r, true, ra);
    if ((imm >> 3) == 0x7) {
        kl_mgmt(env, n, imm, form, rs1, ra);
        return;
    }
    /* GR25 and the Error States 53 (no Zklexpire), 54 and 55. */
    if (imm == KL_ST_SUCCESS || imm == KL_ST_FAILURE ||
        imm == KL_ST_EXPIRED || imm == 54 || imm == 55) {
        kl_illegal(env, ra);
    }
    /* Auxiliary operands: Form D a GPR pair, Form C a vector register. */
    if (form == 3) {
        gpr_pair_check(env, rs1, ra);
    } else if (form == 2) {
        vreg_check_no_vstart(env, rs1, ra);
    }
    kl_gate(env, ra);

    n = locker_resolve(env, n);
    /* kl.clear is a destructive configuration instruction. */
    if (imm != KL_ST_UNCONFIGURED) {
        locker_access(env, n, ra);
    }
    st = locker_state(env, n);
    if (st == KL_ST_UNCONFIGURED) {
        /*
         * kl.clear leaves it Unconfigured, an Error State is not set (GR35)
         * and usage performs no operation; KLNL without a named locker
         * lands here too (GR10).  kl.clear still makes the locker Dirty,
         * since it may be Off with its image elsewhere.
         */
        if (imm == KL_ST_UNCONFIGURED && n < KL_NUM_LOCKERS) {
            locker_dirty(env, n);
            if (n == env->kle.klnamedlocker) {
                kl_set_named(env, KL_NONE);
            }
        }
        return;
    }
    lk = &env->kle.lk[n];
    if (imm == KL_ST_UNCONFIGURED) {                        /* kl.clear */
        locker_zeroize(env, n);
        if (n == env->kle.klnamedlocker) {
            kl_set_named(env, KL_NONE);
        }
        return;
    }
    if (st_error(imm)) {
        /* Not a usage instruction; allowed in a Configuration State. */
        locker_error(env, n, imm);
        return;
    }

    /*
     * A usage instruction.  A CTR Machine expects a Form C kl.setst into
     * Operate, a GCM Machine into the Tag_Finalize States and Hash_Verify:
     * a Form A there would be a KLIOBUF substitution, without Zklio.
     */
    if (!usage_gate(env, n, form == 0 &&
                            ((machine_is_ctr(lk->mdh) &&
                              imm == KL_ST_OPERATE) ||
                             (machine_is_gcm(lk->mdh) &&
                              gcm_setst_form(st, imm) == 2)), ra)) {
        return;
    }
    locker_dirty(env, n);
    if (imm == KL_CFG_CLEAR_ADS) {                          /* GR24 */
        SET(lk->mdh, F_AUXDATALEN, 0);
        SET(lk->mdh, F_ADSDROPPED, 0);
        return;
    }
    if (machine_is_gcm(lk->mdh)) {
        gcm_setst(env, n, imm, form, rs1);
        return;
    }

    /*
     * CTR (Zkl-ISA-machines.adoc <<KLE-keystream-modes>>), in Ready or
     * Operate (no other Valid State is supported):
     *   - Ready, Form A as for ECB: IV and ctr are set to 0;
     *   - Operate, Form C, also from Operate (GR22): IV takes the 96 least
     *     significant bits of the operand (MR7), ctr is kept.  Either
     *     MachinePolicy bit allows it (MR11), so valid Metadata always does;
     *     a KLLEN below 96 violates the granularity (MR2);
     *   - set_aux_value, Form B, an operation in Ready and Operate: ctr takes
     *     the 32 least significant bits of Xs, the State is kept.
     */
    if (machine_is_ctr(lk->mdh)) {
        if (imm == KL_ST_READY && form == 0) {
            locker_ready(lk);
            return;
        }
        if (imm == KL_ST_OPERATE && form == 2 && vlen_bytes(env) >= 12) {
            for (int i = 0; i < 12; i++) {
                ctr_iv(lk)[i] = vreg_ldb(env, rs1, i);
            }
            SET(lk->mdh, F_STATE, KL_ST_OPERATE);
            return;
        }
        if (imm == KL_SET_AUX_VALUE && form == 1) {
            stl_le_p(ctr_iv(lk) + 12, gpr_get(env, rs1));
            return;
        }
        locker_error(env, n, KL_ST_INVALID);                /* MR1 */
        return;
    }

    /*
     * ECB (Zkl-ISA-machines.adoc <<KLE-ECB-mode>>): from any Valid State to
     * Encrypt/Decrypt, by a Form A kl.setst, if the MachinePolicy allows it
     * (MR11); to Ready by GR21.  Any other Form violates MR1.
     */
    if (form == 0 &&
        (imm == KL_ST_READY ||
         (imm == KL_ST_ENCRYPT && (GET(lk->mdh, F_POLICY) & 1)) ||
         (imm == KL_ST_DECRYPT && (GET(lk->mdh, F_POLICY) & 2)))) {
        SET(lk->mdh, F_STATE, imm);
        return;
    }
    locker_error(env, n, KL_ST_INVALID);
}

/* ------------------------------------------------------------------ */
/* kl.exec (<<KLE-instruction-exec>>), ECB and CTR                   */

/* CTR, per block: OUTPUT <- keystream_block(bswap(ctr) @ IV); tick_ctr(). */
static void ctr_keystream(CPURISCVState *env, RISCVKleLocker *lk, int vd,
                          uint64_t start, uint64_t len)
{
    uint8_t *iv = ctr_iv(lk);
    uint32_t ctr = ldl_le_p(iv + 12);
    AES_KEY ks;
    uint8_t blk[16];

    AES_set_encrypt_key(lk->content, 8 * machine_key_bytes(lk->mdh), &ks);
    for (uint64_t off = start; off < len; off += 16) {
        memcpy(blk, iv, 12);
        stl_be_p(blk + 12, ctr++);      /* wraps silently */
        AES_encrypt(blk, blk, &ks);
        for (int i = 0; i < 16; i++) {
            vreg_stb(env, vd, off + i, blk[i]);
        }
    }
    stl_le_p(iv + 12, ctr);
    memset(&ks, 0, sizeof(ks));
    memset(blk, 0, sizeof(blk));
}

static void kl_exec(CPURISCVState *env, int n, int form, int vd, int vs2,
                    uintptr_t ra)
{
    RISCVKleLocker *lk;
    RISCVKleState *kl = &env->kle;
    bool has_out = form == 0 || form == 2;
    bool has_in = form == 0 || form == 1;
    uint64_t len, start;
    int st, nregs;
    AES_KEY ks;
    uint8_t blk[16];
    bool enc;

    if (form != 3) {
        nregs = vlmul_regs(env);
        if (has_out) {
            vreg_check(env, vd, ra);
        }
        if (has_in) {
            vreg_check(env, vs2, ra);
        }
        /* Form A: Vd = Vs2 or disjoint groups. */
        if (form == 0 && vd != vs2 && vd < vs2 + nregs && vs2 < vd + nregs) {
            kl_illegal(env, ra);
        }
    }
    kl_gate(env, ra);
    n = locker_resolve(env, n);
    locker_access(env, n, ra);
    if (form != 3 && kl->klstart != vstart_bytes(env)) {
        kl_illegal(env, ra);
    }

    /* KLNL with klnamedlocker = 32 reads as Unconfigured (GR10). */
    st = locker_state(env, n);
    lk = &kl->lk[n];
    len = form == 3 ? 0 : vlen_bytes(env);
    start = kl->klstart;

    /*
     * GCM: where Form A is expected Forms B and C mix vector and KLIOBUF
     * operands; where B or C is, Form D is a KLIOBUF substitution.
     */
    if (st_valid(st) && machine_is_gcm(lk->mdh)) {
        int want = gcm_exec_form(st);

        usage_gate(env, n, (want == 0 && form != 0) ||
                           (want > 0 && form == 3), ra);
        start = gcm_exec(env, n, form, vd, vs2, start, len);
        goto zero_out;
    }

    /*
     * In Encrypt/Decrypt Form A is expected: Forms B and C mix vector and
     * KLIOBUF operands, and Form D would be a KLIOBUF substitution (no
     * Zklio), both illegal (<<KLE-usage-input-output>>).  In Operate Form C
     * is expected: Form D would again be a substitution, and Forms A and B
     * are not allowed by the State (MR1).
     */
    if (!usage_gate(env, n, ((st == KL_ST_ENCRYPT || st == KL_ST_DECRYPT) &&
                             form != 0) ||
                            (st == KL_ST_OPERATE && form == 3), ra)) {
        goto zero_out;                  /* no operation (GR20) */
    }
    if (st == KL_ST_OPERATE ? form != 2
                            : st != KL_ST_ENCRYPT && st != KL_ST_DECRYPT) {
        locker_error(env, n, KL_ST_INVALID);              /* GR23, MR1 */
        goto zero_out;
    }
    if (len % 16) {                                        /* MR2 */
        locker_error(env, n, KL_ST_INVALID);
        goto zero_out;
    }
    if (start >= len) {
        goto done;                      /* empty window */
    }
    if (start % 16) {               /* not an interruption point */
        locker_error(env, n, KL_ST_INVALID);
        goto zero_out;
    }

    if (st == KL_ST_OPERATE) {
        /* ctr advanced: the locker must be saved on a context switch. */
        ctr_keystream(env, lk, vd, start, len);
        locker_dirty(env, n);
        goto done;
    }

    enc = st == KL_ST_ENCRYPT;
    if (enc) {
        AES_set_encrypt_key(lk->content, 8 * machine_key_bytes(lk->mdh), &ks);
    } else {
        AES_set_decrypt_key(lk->content, 8 * machine_key_bytes(lk->mdh), &ks);
    }
    for (uint64_t off = start; off < len; off += 16) {
        for (int i = 0; i < 16; i++) {
            blk[i] = vreg_ldb(env, vs2, off + i);
        }
        if (enc) {
            AES_encrypt(blk, blk, &ks);
        } else {
            AES_decrypt(blk, blk, &ks);
        }
        for (int i = 0; i < 16; i++) {
            vreg_stb(env, vd, off + i, blk[i]);
        }
    }
    memset(&ks, 0, sizeof(ks));
    memset(blk, 0, sizeof(blk));
    goto done;

zero_out:
    /* GR34: zero the unwritten part of the output window. */
    if (has_out && start < len) {
        vreg_zero(env, vd, start, len);
    }
done:
    kl_set_klstart(env, 0);
    if (form != 3) {
        vreg_retire(env, has_out);
    }
}

/* ------------------------------------------------------------------ */
/* kl.mvin, kl.mvout (<<KLE-instruction-mv>>)                        */

enum {
    MV_IN_X = 1, MV_IN_V = 2, MV_IN_IOBUF = 3,
    MV_OUT_X = 5, MV_OUT_V = 6, MV_OUT_IOBUF = 7,
};

/* On the named locker; @reg is Xs2 or Vs2 (in), Xs1 or Vs1 (out). */
static void kl_mv(CPURISCVState *env, int variant, int reg, uintptr_t ra)
{
    RISCVKleState *kl = &env->kle;
    bool in = variant <= MV_IN_IOBUF;
    bool vec = variant == MV_IN_V || variant == MV_OUT_V;
    uint64_t v[2] = { 0, 0 };
    uint8_t blk[16];
    int n, st;
    Image im;

    /* First group. */
    if (variant == MV_IN_IOBUF || variant == MV_OUT_IOBUF) {
        kl_illegal(env, ra);            /* no Zklio */
    }
    if (vec) {
        vreg_check(env, reg, ra);
        if ((vlen_bytes(env) % 16) || (vstart_bytes(env) % 16)) {
            kl_illegal(env, ra);
        }
    } else {
        gpr_pair_check(env, reg, ra);
    }
    kl_gate(env, ra);

    n = kl->klnamedlocker;
    locker_access(env, n, ra);
    st = locker_state(env, n);
    if (st == KL_ST_UNCONFIGURED || st_error(st)) {
        /* No operation, klstart unchanged; kl.mvout writes zeros (GR37). */
        if (vec) {
            if (!in) {
                vreg_zero(env, reg, vstart_bytes(env), vlen_bytes(env));
            }
            vreg_retire(env, !in);
        } else if (!in) {
            gpr_pair_set(env, reg, v);
        }
        return;
    }
    image_check(env, n, in, ra);
    image_layout(kl->lk[n].mdh, &im);

    if (!vec) {
        if (in) {
            if (kl->klstart < im.image_end) {
                gpr_pair_get(env, reg, v);
                stq_le_p(blk, v[0]);
                stq_le_p(blk + 8, v[1]);
                image_write_block(env, n, &im, kl->klstart, blk);
                locker_dirty(env, n);
                kl_set_klstart(env, kl->klstart + 16);
            }
        } else {
            image_read_block(env, n, &im, kl->klstart, blk);
            v[0] = ldq_le_p(blk);
            v[1] = ldq_le_p(blk + 8);
            gpr_pair_set(env, reg, v);
            if (kl->klstart < im.image_end) {
                kl_set_klstart(env, kl->klstart + 16);
            }
        }
        return;
    }

    /* Element k (from vstart) <-> image offset klstart + (k - vstart). */
    for (uint64_t voff = vstart_bytes(env); voff < vlen_bytes(env);
         voff += 16) {
        uint64_t ioff = kl->klstart;

        if (in) {
            if (ioff >= im.image_end) {
                break;
            }
            for (int i = 0; i < 16; i++) {
                blk[i] = vreg_ldb(env, reg, voff + i);
            }
            image_write_block(env, n, &im, ioff, blk);
            locker_dirty(env, n);
        } else {
            image_read_block(env, n, &im, ioff, blk);
            for (int i = 0; i < 16; i++) {
                vreg_stb(env, reg, voff + i, blk[i]);
            }
        }
        if (ioff < im.image_end) {
            kl_set_klstart(env, ioff + 16);
        }
    }
    vreg_retire(env, !in);
}

/* ------------------------------------------------------------------ */
/* kl.size, kl.avail (<<KLE-instruction-size>>)                      */

/* Only Machine, MachinePolicy, MachineExtension, KeyType, SCProtection. */
static bool avail(CPURISCVState *env, const uint64_t *m)
{
    return machine_supported(env, m) && GET(m, F_SCPROT) == 0 &&
           GET(m, F_POLICY) != 0 && GET(m, F_KEYTYPE) <= 1;
}

static uint64_t size_of(CPURISCVState *env, const uint64_t *m, bool supplied,
                        bool check_hi)
{
    int st = GET(m, F_STATE);
    int aux = GET(m, F_AUXDATALEN);

    if (!supplied && st == KL_ST_UNCONFIGURED) {
        return 0;
    }
    /* Validity as at provisioning for an Unconfigured State, else import. */
    if (supplied && !st_error(st) &&
        (!machine_supported(env, m) ||
         mdh_invalid(env, m, st == KL_ST_UNCONFIGURED ? USE_PROVISION
                                                      : USE_IMPORT,
                     check_hi))) {
        return 0;
    }
    if (st_error(st)) {
        return 16;
    }
    if (st_valid(st) || st_base_scc(st)) {
        return aux ? 64 + content1_size(m) + content2_size(m)
                   : 32 + content1_size(m);
    }
    return 16 + pi_content_size(m);
}

static void kl_size_avail(CPURISCVState *env, uint32_t insn, uintptr_t ra)
{
    int rd = extract32(insn, 7, 5);
    int rs1 = extract32(insn, 15, 5);
    bool q = extract32(insn, 25, 1);
    bool r = extract32(insn, 26, 1);
    int f = extract32(insn, 28, 2);
    uint64_t m[2] = { 0, 0 };
    uint64_t res;
    int n = rs1;

    if (extract32(insn, 20, 5) || f == 3) {
        kl_illegal(env, ra);            /* reserved */
    }
    if (f == 0) {
        n = locker_operand(env, rs1, r, true, ra);
    } else if (r) {
        kl_illegal(env, ra);
    }
    if (f == 2) {
        vreg_check_no_vstart(env, rs1, ra);
        vreg_mdh_check(env, ra);
        vreg_read_mdh(env, rs1, m);
    } else if (f == 1) {
        m[0] = gpr_get(env, rs1);
    }
    kl_gate(env, ra);
    if (f == 0) {
        n = locker_resolve(env, n);
        locker_access(env, n, ra);
        if (n < KL_NUM_LOCKERS) {
            memcpy(m, env->kle.lk[n].mdh, sizeof(m));
        }
    }
    if (q) {
        res = (f != 0 || GET(m, F_STATE) != KL_ST_UNCONFIGURED) &&
              avail(env, m);
    } else {
        res = size_of(env, m, f != 0, f == 2);
    }
    gpr_set(env, rd, res);
}

/* ------------------------------------------------------------------ */
/* kl.getmd*, kl.getnl (<<KLE-instruction-getmd>>)                   */

static void kl_getmd(CPURISCVState *env, uint32_t insn, uintptr_t ra)
{
    int rd = extract32(insn, 7, 5);
    int rs1 = extract32(insn, 15, 5);
    bool r = extract32(insn, 26, 1);
    bool h = extract32(insn, 28, 1);
    bool v = extract32(insn, 29, 1);
    uint64_t m[2] = { 0, 0 };
    int n;

    if (extract32(insn, 20, 5) || extract32(insn, 25, 1) ||
        extract32(insn, 27, 1)) {
        kl_illegal(env, ra);
    }
    if (h && v) {
        /* kl.getnl Xd */
        if (r || rs1) {
            kl_illegal(env, ra);
        }
        kl_gate(env, ra);   /* gated as an access to klnamedlocker */
        gpr_set(env, rd, env->kle.klnamedlocker);
        return;
    }
    n = locker_operand(env, rs1, r, true, ra);
    if (v) {
        vreg_check_no_vstart(env, rd, ra);
        vreg_mdh_check(env, ra);
    } else if (h) {
        gpr_pair_check(env, rd, ra);
    }
    kl_gate(env, ra);
    n = locker_resolve(env, n);
    locker_access(env, n, ra);
    if (n < KL_NUM_LOCKERS) {
        memcpy(m, env->kle.lk[n].mdh, sizeof(m));
    }
    if (v) {
        for (int i = 0; i < 16; i++) {
            vreg_stb(env, rd, i, m[i / 8] >> (8 * (i % 8)));
        }
        vreg_zero(env, rd, 16, vlen_bytes(env));
        vreg_retire(env, true);
    } else if (h) {
        gpr_pair_set(env, rd, m);
    } else {
        gpr_set(env, rd, m[0]);
    }
}

/* ------------------------------------------------------------------ */
/* MISC-MEM funct3 = 4 group                                          */

void helper_kl_exec_grp(CPURISCVState *env, uint32_t insn)
{
    uintptr_t ra = GETPC();
    int rd = extract32(insn, 7, 5);
    int rs1 = extract32(insn, 15, 5);
    int rs2 = extract32(insn, 20, 5);
    int funct2 = extract32(insn, 30, 2);
    int form = extract32(insn, 28, 2);
    bool r = extract32(insn, 26, 1);
    int n = 0;

    switch (funct2) {
    case 0:
        if (extract32(insn, 27, 1)) {
            kl_size_avail(env, insn, ra);
            return;
        }
        /*
         * Masking is reserved.  kl.exec may name KLNL (GR8); kl.mvin and
         * kl.mvout take no locker operand, and their r is reserved.
         */
        if (extract32(insn, 25, 1)) {
            kl_illegal(env, ra);
        }
        if (form == 3 && rd) {
            if (r) {
                kl_illegal(env, ra);
            }
        } else {
            n = locker_operand(env, rs1, r, true, ra);
        }
        switch (form) {
        case 0:
            kl_exec(env, n, 0, rd, rs2, ra);
            return;
        case 1:
            if (rd) {
                kl_illegal(env, ra);
            }
            kl_exec(env, n, 1, 0, rs2, ra);
            return;
        case 2:
            if (rs2) {
                kl_illegal(env, ra);
            }
            kl_exec(env, n, 2, rd, 0, ra);
            return;
        default:
            if (rd == 0) {
                if (rs2) {
                    kl_illegal(env, ra);
                }
                kl_exec(env, n, 3, 0, 0, ra);
            } else if (rd <= MV_IN_IOBUF) {
                if (rs1) {
                    kl_illegal(env, ra);
                }
                kl_mv(env, rd, rs2, ra);            /* I-III */
            } else if (rd >= MV_OUT_X) {
                if (rs2) {
                    kl_illegal(env, ra);
                }
                kl_mv(env, rd, rs1, ra);            /* IV-VI */
            } else {
                kl_illegal(env, ra);
            }
            return;
        }
    case 3:
        kl_getmd(env, insn, ra);
        return;
    default:
        /* kl.restrict*, kl.clone/rename/swap, kl.derive: not implemented. */
        kl_illegal(env, ra);
    }
}

/* ------------------------------------------------------------------ */
/* kl.load, kl.store (<<KLE-instruction-load>>, <<KLE-instruction-store>>) */

/*
 * The checks of kl.load and kl.store, on the named locker: returns it,
 * or -1 when the instruction performs no operation.  With
 * klnamedlocker = 32 they are kl.input and kl.output, which need Zklio
 * unless Xl = 0 (GR37).
 */
static int kl_mem_check(CPURISCVState *env, int xl, bool load,
                        target_ulong ea, uintptr_t ra)
{
    int n, st;

    kl_gate(env, ra);
    n = env->kle.klnamedlocker;
    if (n == KL_NONE) {
        if (gpr_get(env, xl)) {
            kl_illegal(env, ra);
        }
        kl_set_klstart(env, 0);
        return -1;
    }
    locker_access(env, n, ra);
    if (gpr_get(env, xl)) {
        kl_illegal(env, ra);
    }
    st = locker_state(env, n);
    if (st != KL_ST_UNCONFIGURED && !st_error(st)) {
        image_check(env, n, load, ra);
    }
    if (ea % 16) {
        env->badaddr = ea;
        kl_raise(env, load ? RISCV_EXCP_LOAD_ADDR_MIS
                           : RISCV_EXCP_STORE_AMO_ADDR_MIS, ra);
    }
    if (st == KL_ST_UNCONFIGURED || st_error(st)) {
        kl_set_klstart(env, 0);         /* an empty window */
        return -1;
    }
    return n;
}

void helper_kl_load(CPURISCVState *env, uint32_t insn)
{
    uintptr_t ra = GETPC();
    target_ulong ea = gpr_get(env, extract32(insn, 15, 5)) +
                      sextract32(insn, 20, 12);
    int mmu_idx = riscv_env_mmu_index(env, false);
    RISCVKleState *kl = &env->kle;
    uint8_t blk[16];
    Image im;
    int n;

    n = kl_mem_check(env, extract32(insn, 7, 5), true, ea, ra);
    if (n < 0) {
        return;
    }
    image_layout(kl->lk[n].mdh, &im);
    if (kl->klstart < im.image_end) {
        locker_dirty(env, n);       /* the locker, and klstart on a fault */
    }
    while (kl->klstart < im.image_end) {
        target_ulong a = adjust_addr(env, ea + kl->klstart);

        stq_le_p(blk, cpu_ldq_le_mmuidx_ra(env, a, mmu_idx, ra));
        stq_le_p(blk + 8, cpu_ldq_le_mmuidx_ra(env, a + 8, mmu_idx, ra));
        image_write_block(env, n, &im, kl->klstart, blk);
        kl->klstart += 16;          /* prefix-complete point */
    }
    kl_set_klstart(env, 0);
}

void helper_kl_store(CPURISCVState *env, uint32_t insn)
{
    uintptr_t ra = GETPC();
    target_ulong ea = gpr_get(env, extract32(insn, 15, 5)) +
                      ((sextract32(insn, 25, 7) << 5) | extract32(insn, 7, 5));
    int mmu_idx = riscv_env_mmu_index(env, false);
    RISCVKleState *kl = &env->kle;
    uint8_t blk[16];
    Image im;
    int n;

    n = kl_mem_check(env, extract32(insn, 20, 5), false, ea, ra);
    if (n < 0) {
        return;
    }
    image_layout(kl->lk[n].mdh, &im);
    if (kl->klstart < im.content_offset + im.content_size) {
        zkl_mark_dirty(env);        /* klstart changes, on a fault too */
    }
    while (kl->klstart < im.content_offset + im.content_size) {
        target_ulong a = adjust_addr(env, ea + kl->klstart);

        image_read_block(env, n, &im, kl->klstart, blk);
        probe_write(env, a, 16, mmu_idx, ra);
        cpu_stq_le_mmuidx_ra(env, a, ldq_le_p(blk), mmu_idx, ra);
        cpu_stq_le_mmuidx_ra(env, a + 8, ldq_le_p(blk + 8), mmu_idx, ra);
        kl->klstart += 16;
    }
    kl_set_klstart(env, 0);
}
