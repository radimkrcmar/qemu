/*
 * Bare-metal test of the Zkl (KLE) prototype: AES-ECB, AES-CTR and AES-GCM
 * Machines, locker management, SCC sealing (checked against the
 * specification's own models through zkl-vectors.h), Localities and the
 * privileged gates.  Built with ZKL_NO_CTR or ZKL_NO_GCM, it checks a unit
 * without the CTR Machines (x-zkl-ctr=false) or without the GCM Machines
 * (x-zkl-gcm=false) instead; built with ZKL_CSK_FIXED, a unit whose CSK is
 * the vectors' (x-zkl-csk=000102...1f), active out of reset, with the
 * mklcsk group illegal, so every SCC comparison holds without programming it.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#include <stdint.h>
#include <stddef.h>
#include "zkl-vectors.h"

/* ---------------------------------------------------------------- encodings */

/*
 * kl.setst / kl.mgmt: MISC-MEM, funct3 = 3; r = 1 with locker 0 is KLNL.
 * Bit 24 makes kl.setnl (Form B) and kl.setnli (Form A).
 */
#define SETST(imm, f, r, rs1, rd) \
    (((imm) << 25) | ((f) << 21) | ((r) << 20) | ((rs1) << 15) | \
     (3 << 12) | ((rd) << 7) | 0x0f)
#define SETNLI(v)           (SETST(v, 0, 0, 0, 0) | (1 << 24))
#define SETNL(rs1)          (SETST(0, 1, 0, rs1, 0) | (1 << 24))
/* kl.exec group: MISC-MEM, funct3 = 4. */
#define R4(f7, rs2, rs1, rd) \
    (((f7) << 25) | ((rs2) << 20) | ((rs1) << 15) | (4 << 12) | \
     ((rd) << 7) | 0x0f)
#define F7_EXEC(form)       ((form) << 3)
#define F7_SIZE(f, q)       (((f) << 3) | (1 << 2) | (q))
#define F7_GETMDL           0x60
#define F7_GETMD            0x68
#define F7_GETMDV           0x70
#define F7_GETNL            0x78
#define F7_KLNL             0x02    /* r: KLNL with locker field 0 */
/* kl.mvin / kl.mvout: kl.exec Form D with rd selecting the variant. */
#define MV_IN_X(rs2)        R4(F7_EXEC(3), rs2, 0, 1)
#define MV_IN_V(vs2)        R4(F7_EXEC(3), vs2, 0, 2)
#define MV_OUT_X(rd)        R4(F7_EXEC(3), 0, rd, 5)
#define MV_OUT_V(vd)        R4(F7_EXEC(3), 0, vd, 6)
/* kl.load: LOAD funct3 = 7; kl.store: STORE funct3 = 5; offset 0. */
#define KL_LOAD(rs1, xl)    (((rs1) << 15) | (7 << 12) | ((xl) << 7) | 0x03)
#define KL_STORE(rs1, xl)   (((xl) << 20) | ((rs1) << 15) | (5 << 12) | 0x23)

#define X_A0 10
#define X_A2 12
#define X_A3 13
#define V8 8
#define V16 16

enum {
    ST_READY = 1, ST_OPERATE = 2, ST_HA = 2, ST_HV = 5, ST_ENCRYPT = 7,
    ST_DECRYPT = 8, ST_ELB = 9, ST_DLB = 10, ST_ETF = 11, ST_DTF = 12,
    SET_AUX = 13, ST_SUCCESS = 46, ST_FAILURE = 47,
    ST_UNSUPPORTED = 48, ST_INVALID = 49,
    ST_MGMT_AUTH = 51, ST_PRIV = 52, ST_EXPIRED = 53,
    CFG_PROV = 56, CFG_EXP = 57, CFG_IMP = 58, CFG_PPI_EXP = 59,
    CFG_PPI_IMP = 60, CFG_END = 63, CFG_CLEAR_ADS = 64, CFG_CLEARALL = 65,
};

#define CAUSE_ILLEGAL       2
#define CAUSE_LOAD_MIS      4
#define CAUSE_STORE_MIS     6
#define CAUSE_MISSING_CSK   25
#define CAUSE_LOCKER_OFF    26
#define CAUSE_UNSUPPORTED   27
#define CAUSE_PRIV_VIOL     28

/* ---------------------------------------------------------------- runtime */

volatile uint64_t trap_count, trap_cause, trap_prev_cause, trap_tval;
uint64_t saved_sp;

asm(
"   .text\n"
"   .globl _start\n"
"_start:\n"
"   lla sp, stack_top\n"
"   lla t0, trap_entry\n"
"   csrw mtvec, t0\n"
"   li t0, -1\n"
"   csrw pmpaddr0, t0\n"
"   li t0, 0x1f\n"
"   csrw pmpcfg0, t0\n"
"   li t0, 0x200\n"                 /* mstatus.VS = Initial */
"   csrs mstatus, t0\n"
"   call main\n"
"   j sys_exit\n"

/* Record the trap; return to U-mode callers' resume point on ecall. */
"   .align 4\n"
"trap_entry:\n"
"   csrw mscratch, t0\n"
"   ld t0, trap_cause\n"
"   sd t0, trap_prev_cause, t1\n"
"   csrr t0, mcause\n"
"   sd t0, trap_cause, t1\n"
"   csrr t0, mtval\n"
"   sd t0, trap_tval, t1\n"
"   ld t0, trap_count\n"
"   addi t0, t0, 1\n"
"   sd t0, trap_count, t1\n"
"   csrr t0, mcause\n"
"   addi t0, t0, -8\n"              /* ecall from U */
"   beqz t0, 1f\n"
"   csrr t0, mepc\n"
"   addi t0, t0, 4\n"
"   csrw mepc, t0\n"
"   csrr t0, mscratch\n"
"   mret\n"
"1: lla t0, u_resume\n"
"   csrw mepc, t0\n"
"   li t0, 0x1800\n"
"   csrs mstatus, t0\n"             /* MPP = M */
"   csrr t0, mscratch\n"
"   mret\n"

/* void run_in_u(void (*fn)(void)): call fn in U-mode. */
"   .globl run_in_u\n"
"run_in_u:\n"
"   addi sp, sp, -112\n"
"   sd ra, 0(sp)\n"
"   sd s0, 8(sp)\n  sd s1, 16(sp)\n sd s2, 24(sp)\n sd s3, 32(sp)\n"
"   sd s4, 40(sp)\n sd s5, 48(sp)\n sd s6, 56(sp)\n sd s7, 64(sp)\n"
"   sd s8, 72(sp)\n sd s9, 80(sp)\n sd s10, 88(sp)\n sd s11, 96(sp)\n"
"   sd sp, saved_sp, t0\n"
"   csrw mepc, a0\n"
"   li t0, 0x1800\n"
"   csrc mstatus, t0\n"             /* MPP = U */
"   lla ra, u_ecall\n"
"   mret\n"
"u_ecall:\n"
"   ecall\n"
"u_resume:\n"
"   ld sp, saved_sp\n"
"   ld ra, 0(sp)\n"
"   ld s0, 8(sp)\n  ld s1, 16(sp)\n ld s2, 24(sp)\n ld s3, 32(sp)\n"
"   ld s4, 40(sp)\n ld s5, 48(sp)\n ld s6, 56(sp)\n ld s7, 64(sp)\n"
"   ld s8, 72(sp)\n ld s9, 80(sp)\n ld s10, 88(sp)\n ld s11, 96(sp)\n"
"   addi sp, sp, 112\n"
"   ret\n"

/* Semihosting: a0 = op, a1 = argument block. */
"   .align 4\n"
"   .option push\n"
"   .option norvc\n"
"semihost:\n"
"   slli zero, zero, 0x1f\n"
"   ebreak\n"
"   srai zero, zero, 0x7\n"
"   ret\n"
"   .option pop\n"
"sys_exit:\n"
"   lla a1, semiargs\n"
"   li t0, 0x20026\n"
"   sd t0, 0(a1)\n"
"   sd a0, 8(a1)\n"
"   li a0, 0x20\n"
"   call semihost\n"
"   j .\n"
"   .data\n"
"   .align 4\n"
"semiargs: .space 16\n"
"   .bss\n"
"   .align 4\n"
"   .space 16384\n"
"stack_top:\n"
"   .text\n"
);

void run_in_u(void (*fn)(void));
uint64_t semihost(uint64_t op, const void *arg);

static void puts_(const char *s)
{
    semihost(0x04, s);      /* SYS_WRITE0 */
}

static void puthex(uint64_t v)
{
    char b[19] = "0x";

    for (int i = 0; i < 16; i++) {
        b[2 + i] = "0123456789abcdef"[(v >> (60 - 4 * i)) & 15];
    }
    b[18] = 0;
    puts_(b);
}

static int failures, checks;

static void check(const char *what, uint64_t got, uint64_t want)
{
    checks++;
    if (got != want) {
        failures++;
        puts_("FAIL ");
        puts_(what);
        puts_(": got ");
        puthex(got);
        puts_(" want ");
        puthex(want);
        puts_("\n");
    }
}

static int memeq(const void *a, const void *b, size_t n)
{
    const uint8_t *x = a, *y = b;

    for (size_t i = 0; i < n; i++) {
        if (x[i] != y[i]) {
            return 0;
        }
    }
    return 1;
}

static void cpy(void *d, const void *s, size_t n)
{
    uint8_t *x = d;
    const uint8_t *y = s;

    while (n--) {
        *x++ = *y++;
    }
}

static uint64_t ld64(const uint8_t *p)
{
    uint64_t v = 0;

    for (int i = 7; i >= 0; i--) {
        v = (v << 8) | p[i];
    }
    return v;
}

void *memset(void *d, int c, size_t n)
{
    uint8_t *x = d;

    while (n--) {
        *x++ = c;
    }
    return d;
}

void *memcpy(void *d, const void *s, size_t n)
{
    cpy(d, s, n);
    return d;
}

/* Run an instruction that is expected to trap; returns the cause or 0. */
#define TRAPS(stmt) ({                                  \
    uint64_t _n = trap_count;                           \
    stmt;                                               \
    trap_count != _n ? trap_cause : 0;                  \
})

/* ---------------------------------------------------------------- KLE ops */

#define CSR_KLSTART         0x800
#define CSR_KLNAMEDLOCKER   0x801

#define csr_read(csr) ({ uint64_t _v; \
    asm volatile("csrr %0, " #csr : "=r"(_v)); _v; })
#define csr_write(csr, v) asm volatile("csrw " #csr ", %0" :: "r"(v))

static void set_kls(int v)
{
    uint64_t m = 3ul << 25;

    asm volatile("csrc mstatus, %0" :: "r"(m));
    asm volatile("csrs mstatus, %0" :: "r"((uint64_t)v << 25));
}

#ifndef ZKL_CSK_FIXED
static void write_csk(const uint8_t *k, int n)
{
    if (n > 0) asm volatile("csrw 0xbc0, %0" :: "r"(ld64(k)));
    if (n > 1) asm volatile("csrw 0xbc1, %0" :: "r"(ld64(k + 8)));
    if (n > 2) asm volatile("csrw 0xbc2, %0" :: "r"(ld64(k + 16)));
    if (n > 3) asm volatile("csrw 0xbc3, %0" :: "r"(ld64(k + 24)));
}
#endif

/* kl.mgmt Kk, #imm, a1:a0 (Form D) */
#define KL_MGMT(k, imm, lo, hi) do {                                    \
    register uint64_t _a0 asm("a0") = (lo);                             \
    register uint64_t _a1 asm("a1") = (hi);                             \
    asm volatile(".4byte %2" :: "r"(_a0), "r"(_a1),                     \
                 "i"(SETST(imm, 3, 0, X_A0, k)) : "memory");            \
} while (0)

/* kl.mgmt KLNL, #imm, a1:a0 (Form D) */
#define KL_MGMT_NL(imm, lo, hi) do {                                    \
    register uint64_t _a0 asm("a0") = (lo);                             \
    register uint64_t _a1 asm("a1") = (hi);                             \
    asm volatile(".4byte %2" :: "r"(_a0), "r"(_a1),                     \
                 "i"(SETST(imm, 3, 1, X_A0, 0)) : "memory");            \
} while (0)

/* kl.mgmt Kk, #imm (Form A) */
#define KL_MGMT_A(k, imm) \
    asm volatile(".4byte %0" :: "i"(SETST(imm, 0, 0, 0, k)) : "memory")
#define KL_MGMT_A_NL(imm) \
    asm volatile(".4byte %0" :: "i"(SETST(imm, 0, 1, 0, 0)) : "memory")

#define KL_SETST(k, imm) \
    asm volatile(".4byte %0" :: "i"(SETST(imm, 0, 0, 0, k)) : "memory")
#define KL_SETST_NL(imm) \
    asm volatile(".4byte %0" :: "i"(SETST(imm, 0, 1, 0, 0)) : "memory")

#define KL_CLEARALL() \
    asm volatile(".4byte %0" :: "i"(SETST(CFG_CLEARALL, 0, 0, 0, 0)) : "memory")

/* kl.setnli #v; kl.getnl a0 */
#define KL_SETNLI(v) \
    asm volatile(".4byte %0" :: "i"(SETNLI(v)) : "memory")
#define KL_SETNL(v) do {                                                \
    register uint64_t _a2 asm("a2") = (v);                              \
    asm volatile(".4byte %1" :: "r"(_a2), "i"(SETNL(X_A2)) : "memory"); \
} while (0)
#define KL_GETNL() ({                                                   \
    register uint64_t _a0 asm("a0");                                    \
    asm volatile(".4byte %1" : "=r"(_a0) : "i"(R4(F7_GETNL, 0, 0, X_A0))); \
    _a0; })

#define KL_GETMDL(k) ({                                                 \
    register uint64_t _a0 asm("a0");                                    \
    asm volatile(".4byte %1" : "=r"(_a0) : "i"(R4(F7_GETMDL, 0, k, X_A0))); \
    _a0; })
#define KL_GETMDL_NL() ({                                               \
    register uint64_t _a0 asm("a0");                                    \
    asm volatile(".4byte %1" : "=r"(_a0)                                \
                 : "i"(R4(F7_GETMDL | F7_KLNL, 0, 0, X_A0)));           \
    _a0; })

#define KL_GETMD(k, m) do {                                             \
    register uint64_t _a0 asm("a0");                                    \
    register uint64_t _a1 asm("a1");                                    \
    asm volatile(".4byte %2" : "=r"(_a0), "=r"(_a1)                     \
                 : "i"(R4(F7_GETMD, 0, k, X_A0)));                      \
    (m)[0] = _a0; (m)[1] = _a1;                                         \
} while (0)

#define KL_GETST(k)     ((KL_GETMDL(k) >> 18) & 0x3f)
#define KL_GETST_NL()   ((KL_GETMDL_NL() >> 18) & 0x3f)

/* kl.size / kl.avail Form A (locker) and Form B (MDH[63:0] in a2) */
#define KL_SIZE_A(k, q) ({                                              \
    register uint64_t _a0 asm("a0");                                    \
    asm volatile(".4byte %1" : "=r"(_a0) : "i"(R4(F7_SIZE(0, q), 0, k, X_A0))); \
    _a0; })
#define KL_SIZE_BQ(lo, q) ({                                            \
    register uint64_t _a0 asm("a0");                                    \
    register uint64_t _a2 asm("a2") = (lo);                             \
    asm volatile(".4byte %1" : "=r"(_a0)                                \
                 : "i"(R4(F7_SIZE(1, q), 0, X_A2, X_A0)), "r"(_a2));    \
    _a0; })
#define KL_SIZE_B(lo)   KL_SIZE_BQ(lo, 0)
#define KL_AVAIL_B(lo)  KL_SIZE_BQ(lo, 1)
#define KL_SIZE_NL() ({                                                 \
    register uint64_t _a0 asm("a0");                                    \
    asm volatile(".4byte %1" : "=r"(_a0)                                \
                 : "i"(R4(F7_SIZE(0, 0) | F7_KLNL, 0, 0, X_A0)));       \
    _a0; })

/* kl.setst Kk, #imm, a2 (Form B) */
#define KL_SETST_B(k, imm, x) do {                                      \
    register uint64_t _a2 asm("a2") = (x);                              \
    asm volatile(".4byte %1" :: "r"(_a2),                               \
                 "i"(SETST(imm, 1, 0, X_A2, k)) : "memory");            \
} while (0)
/* kl.setst KLNL, #imm, a2 (Form B) */
#define KL_SETST_B_NL(imm, x) do {                                      \
    register uint64_t _a2 asm("a2") = (x);                              \
    asm volatile(".4byte %1" :: "r"(_a2),                               \
                 "i"(SETST(imm, 1, 1, X_A2, 0)) : "memory");            \
} while (0)

/* kl.setst Kk, #imm, v8 (Form C) with the n bytes at p, e8 */
#define KL_SETST_C(k, imm, p, n) do {                                   \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m1, ta, ma\n"                     \
                 "vle8.v v8, (%2)\n"                                    \
                 ".4byte %3\n"                                          \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(p),             \
                   "i"(SETST(imm, 2, 0, V8, k)) : "memory", "v8");      \
} while (0)
/* The same, issued with vstart = 1 (reset afterwards) */
#define KL_SETST_C_VSTART(k, imm, p, n) do {                            \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m1, ta, ma\n"                     \
                 "vle8.v v8, (%2)\n"                                    \
                 "csrwi vstart, 1\n"                                    \
                 ".4byte %3\n"                                          \
                 "csrwi vstart, 0\n"                                    \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(p),             \
                   "i"(SETST(imm, 2, 0, V8, k)) : "memory", "v8");      \
} while (0)
/* kl.setst KLNL, #imm, v8 (Form C) with the n bytes at p, e8 */
#define KL_SETST_C_NL(imm, p, n) do {                                   \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m1, ta, ma\n"                     \
                 "vle8.v v8, (%2)\n"                                    \
                 ".4byte %3\n"                                          \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(p),             \
                   "i"(SETST(imm, 2, 1, V8, 0)) : "memory", "v8");      \
} while (0)

/* kl.mvin a3:a2 (variant I) */
#define KL_MV_IN(p) do {                                                \
    register uint64_t _a2 asm("a2") = ld64(p);                          \
    register uint64_t _a3 asm("a3") = ld64((p) + 8);                    \
    asm volatile(".4byte %2" :: "r"(_a2), "r"(_a3),                     \
                 "i"(MV_IN_X(X_A2)) : "memory");                        \
} while (0)
/* kl.mvout a1:a0 (variant IV) into m[2] */
#define KL_MV_OUT(m) do {                                               \
    register uint64_t _a0 asm("a0") = 0xa5;                             \
    register uint64_t _a1 asm("a1") = 0xa5;                             \
    asm volatile(".4byte %2" : "+r"(_a0), "+r"(_a1)                     \
                 : "i"(MV_OUT_X(X_A0)) : "memory");                     \
    (m)[0] = _a0; (m)[1] = _a1;                                         \
} while (0)

/* kl.load 0(a2), x0 / kl.store 0(a2), x0: on the named locker */
#define KL_LOAD_(p) do {                                                \
    register const void *_a2 asm("a2") = (p);                           \
    asm volatile(".4byte %1" :: "r"(_a2), "i"(KL_LOAD(X_A2, 0)) : "memory"); \
} while (0)
#define KL_STORE_(p) do {                                               \
    register void *_a2 asm("a2") = (p);                                 \
    asm volatile(".4byte %1" :: "r"(_a2), "i"(KL_STORE(X_A2, 0)) : "memory"); \
} while (0)
/* kl.load 0(a2), a3 with a3 = xl (kl.input with klnamedlocker = 32) */
#define KL_LOAD_XL(p, xl) do {                                          \
    register const void *_a2 asm("a2") = (p);                           \
    register uint64_t _a3 asm("a3") = (xl);                             \
    asm volatile(".4byte %2" :: "r"(_a2), "r"(_a3),                     \
                 "i"(KL_LOAD(X_A2, X_A3)) : "memory");                  \
} while (0)

/*
 * kl.exec v8, Kk, v8 (Form A, in place) on n bytes, e8 with the given LMUL
 * (lmul_log2), from buf to out.
 */
#define KL_ECB(k, lmul, in, out, n) do {                                \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m" #lmul ", ta, ma\n"             \
                 "vle8.v v8, (%2)\n"                                    \
                 ".4byte %4\n"                                          \
                 "vse8.v v8, (%3)\n"                                    \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(in), "r"(out),  \
                   "i"(R4(F7_EXEC(0), V8, k, V8)) : "memory", "v8", "v9", \
                   "v10", "v11");                                       \
} while (0)

/*
 * kl.exec v8, Kk (Form C, output only) on n bytes, e8 with the given LMUL
 * (lmul_log2), into out.
 */
#define KL_CTR(k, lmul, out, n) do {                                    \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m" #lmul ", ta, ma\n"             \
                 ".4byte %3\n"                                          \
                 "vse8.v v8, (%2)\n"                                    \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(out),           \
                   "i"(R4(F7_EXEC(2), 0, k, V8)) : "memory", "v8", "v9", \
                   "v10", "v11");                                       \
} while (0)

/* The same on KLNL (GR8) */
#define KL_ECB_NL(lmul, in, out, n) do {                                \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m" #lmul ", ta, ma\n"             \
                 "vle8.v v8, (%2)\n"                                    \
                 ".4byte %4\n"                                          \
                 "vse8.v v8, (%3)\n"                                    \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(in), "r"(out),  \
                   "i"(R4(F7_EXEC(0) | F7_KLNL, V8, 0, V8))             \
                 : "memory", "v8", "v9", "v10", "v11");                 \
} while (0)
#define KL_CTR_NL(lmul, out, n) do {                                    \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m" #lmul ", ta, ma\n"             \
                 ".4byte %3\n"                                          \
                 "vse8.v v8, (%2)\n"                                    \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(out),           \
                   "i"(R4(F7_EXEC(2) | F7_KLNL, 0, 0, V8))              \
                 : "memory", "v8", "v9", "v10", "v11");                 \
} while (0)

/* An encoding that should trap, issued as is */
#define INSN(i) asm volatile(".4byte %0" :: "i"(i) : "memory")

/* kl.mvout v16 (variant V) of n bytes into out */
#define KL_MV_VOUT(out, n) do {                                         \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m4, ta, ma\n"                     \
                 ".4byte %3\n"                                          \
                 "vse8.v v16, (%2)\n"                                   \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(out),           \
                   "i"(MV_OUT_V(V16))                                   \
                 : "memory", "v16", "v17", "v18", "v19");               \
} while (0)

/* ---------------------------------------------------------------- MDH */

static uint64_t mdh_lo(int machine, int policy, int state, int keytype)
{
    return machine | (uint64_t)policy << 12 | (uint64_t)state << 18 |
           (uint64_t)keytype << 28;
}

#define MDH_HI(usage, loc)  ((uint64_t)(usage) | (uint64_t)(loc) << 5)

static const uint8_t pt1[16] __attribute__((aligned(16))) = {
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff };
static const uint8_t ct128[16] = {
    0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30,
    0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a };
static const uint8_t ct192[16] = {
    0xdd, 0xa9, 0x7c, 0xa4, 0x86, 0x4c, 0xdf, 0xe0,
    0x6e, 0xaf, 0x70, 0xa0, 0xec, 0x0d, 0x71, 0x91 };
static const uint8_t ct256[16] = {
    0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf,
    0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49, 0x60, 0x89 };

/* SP 800-38A F.1.5 (ECB-AES256.Encrypt), four blocks. */
static const uint8_t f15_key[32] __attribute__((aligned(16))) = {
    0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0,
    0x85, 0x7d, 0x77, 0x81, 0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7,
    0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4 };
static const uint8_t f15_pt[64] __attribute__((aligned(16))) = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96, 0xe9, 0x3d, 0x7e, 0x11,
    0x73, 0x93, 0x17, 0x2a, 0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
    0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51, 0x30, 0xc8, 0x1c, 0x46,
    0xa3, 0x5c, 0xe4, 0x11, 0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
    0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17, 0xad, 0x2b, 0x41, 0x7b,
    0xe6, 0x6c, 0x37, 0x10 };
static const uint8_t f15_ct[64] = {
    0xf3, 0xee, 0xd1, 0xbd, 0xb5, 0xd2, 0xa0, 0x3c, 0x06, 0x4b, 0x5a, 0x7e,
    0x3d, 0xb1, 0x81, 0xf8, 0x59, 0x1c, 0xcb, 0x10, 0xd4, 0x10, 0xed, 0x26,
    0xdc, 0x5b, 0xa7, 0x4a, 0x31, 0x36, 0x28, 0x70, 0xb6, 0xed, 0x21, 0xb9,
    0x9c, 0xa6, 0xf4, 0xf9, 0xf1, 0x53, 0xe7, 0xb1, 0xbe, 0xaf, 0xed, 0x1d,
    0x23, 0x30, 0x4b, 0x7a, 0x39, 0xf9, 0xf3, 0xff, 0x06, 0x7d, 0x8d, 0x8f,
    0x9e, 0x24, 0xec, 0xc7 };

static uint8_t buf[64] __attribute__((aligned(16)));
static const uint8_t zero16[16] __attribute__((aligned(16)));
static uint8_t img[112] __attribute__((aligned(16)));

/*
 * The management operations name their locker in kl.mgmt, which leaves
 * klnamedlocker naming it for kl.load and kl.store, and write 32 to it
 * when done (SR10).
 */

/* Provision Kk from a PI in memory with kl.load (Zklmem). */
#define PROVISION_LOAD(k, lo, hi, key, keylen) do {                     \
    static uint8_t _pi[48] __attribute__((aligned(16)));                \
    memset(_pi, 0, sizeof(_pi));                                        \
    cpy(_pi, key, keylen);                                              \
    KL_MGMT(k, CFG_PROV, lo, hi);                                       \
    KL_LOAD_(_pi);                                                      \
    KL_MGMT_A(k, CFG_END);                                              \
    KL_SETNLI(32);                                                      \
} while (0)

/* Import an SCC/PCCC image (MDH first) with kl.load. */
#define IMPORT(k, image) do {                                           \
    uint64_t _lo = ld64(image), _hi = ld64((image) + 8);                \
    KL_MGMT(k, CFG_IMP, _lo, _hi);                                      \
    KL_LOAD_((image) + 16);                                             \
    KL_MGMT(k, CFG_END, _lo, _hi);                                      \
    KL_SETNLI(32);                                                      \
} while (0)

/* Export Kk to image (MDH first) with kl.getmd/kl.store. */
#define EXPORT(k, image) do {                                           \
    uint64_t _m[2];                                                     \
    KL_GETMD(k, _m);                                                    \
    cpy(image, _m, 16);                                                 \
    KL_MGMT_A(k, CFG_EXP);                                              \
    KL_STORE_((image) + 16);                                            \
    KL_MGMT(k, CFG_END, _m[0], _m[1]);                                  \
    KL_SETNLI(32);                                                      \
} while (0)

/* ---------------------------------------------------------------- tests */

#ifndef ZKL_CSK_FIXED
static void u_nop(void)
{
}
#endif

static void u_use_k5(void)
{
    KL_ECB(5, 1, pt1, buf, 16);
}

static void u_use_k6(void)
{
    KL_ECB(6, 1, pt1, buf, 16);
}

static void u_clear_k5(void)
{
    KL_SETST(5, 0);
}

#ifndef ZKL_NO_CTR
static void u_operate_a_k5(void)
{
    KL_SETST(5, ST_OPERATE);
}
#endif

static void test_gates(void)
{
    uint64_t c;

    puts_("gates\n");
    /* KLS Off out of reset: illegal instruction. */
    c = TRAPS(KL_GETMDL(0));
    check("KLS off -> illegal", c, CAUSE_ILLEGAL);
    c = TRAPS(csr_read(0x800));
    check("KLS off: klstart illegal", c, CAUSE_ILLEGAL);
    check("KLS off: klmvendorid readable", TRAPS(csr_read(0xcc0)), 0);

    set_kls(1);
#ifdef ZKL_CSK_FIXED
    /* x-zkl-csk: the CSK is active out of reset, and no software sees it. */
    check("fixed CSK: active out of reset", TRAPS(KL_GETMDL(0)), 0);
    check("fixed CSK: mklcsk0 read -> illegal", TRAPS(csr_read(0xbc0)),
          CAUSE_ILLEGAL);
    check("fixed CSK: mklcsk3 write -> illegal", TRAPS(csr_write(0xbc3, 0)),
          CAUSE_ILLEGAL);
    check("fixed CSK: still active", TRAPS(KL_GETMDL(0)), 0);
#else
    c = TRAPS(KL_GETMDL(0));
    check("no CSK -> missing-CSK", c, CAUSE_MISSING_CSK);
    check("no CSK: kl.getnl -> missing-CSK", TRAPS(KL_GETNL()),
          CAUSE_MISSING_CSK);
    check("no CSK: usage kl.setst on KLNL -> missing-CSK",
          TRAPS(KL_SETST_NL(ST_ENCRYPT)), CAUSE_MISSING_CSK);
    check("no CSK: r with K9 -> illegal (first group)",
          TRAPS(INSN(SETST(ST_ENCRYPT, 0, 1, 0, 9))), CAUSE_ILLEGAL);

    /* A partially written mklcsk group survives a trap from U into M. */
    write_csk(zv_csk, 3);
    run_in_u(u_nop);
    c = TRAPS(KL_GETMDL(0));
    check("partial mklcsk, trap to M -> missing-CSK", c, CAUSE_MISSING_CSK);
    asm volatile("csrw 0xbc3, %0" :: "r"(ld64(zv_csk + 24)));
    c = TRAPS(KL_GETMDL(0));
    check("CSK active once the group is written", c, 0);
    check("mklcsk2 readback", csr_read(0xbc2), ld64(zv_csk + 16));

    /* One write disables the unit until the group is written again. */
    write_csk(zv_csk, 1);
    check("one mklcsk write -> missing-CSK", TRAPS(KL_GETMDL(0)),
          CAUSE_MISSING_CSK);
    write_csk(zv_csk, 4);
    check("group rewritten: CSK active", TRAPS(KL_GETMDL(0)), 0);
#endif
    check("klnamedlocker reset", csr_read(0x801), 32);
    check("kl.getnl", KL_GETNL(), 32);
}

static void test_ecb(void)
{
    puts_("ecb\n");
    /* AES-128, provisioned with kl.mvin from GPRs, encrypt only. */
    KL_MGMT(1, CFG_PROV, mdh_lo(0x000, 1, 0, 0), 0);
    check("open provisioning", KL_GETST(1), CFG_PROV);
    check("klnamedlocker = 1", csr_read(0x801), 1);
    KL_MV_IN(zv_k128);
    check("klstart after kl.mvin", csr_read(0x800), 16);
    KL_MV_IN(zv_k128);
    check("kl.mvin past image_end: klstart kept", csr_read(0x800), 16);
    KL_MGMT_A(1, CFG_END);
    check("provisioned", KL_GETST(1), ST_READY);
    check("klnamedlocker kept after completion (GR12)", csr_read(0x801), 1);
    check("KLNL names it", KL_GETST_NL(), ST_READY);
    check("kl.size KLNL", KL_SIZE_NL(), 48);
    check("kl.mvin on a Ready locker -> illegal", TRAPS(KL_MV_IN(zv_k128)),
          CAUSE_ILLEGAL);
    check("kl.mgmt on another locker meanwhile -> illegal (GR11)",
          TRAPS(KL_MGMT(2, CFG_PROV, mdh_lo(0x000, 3, 0, 0), 0)),
          CAUSE_ILLEGAL);
    KL_SETNLI(32);
    check("kl.setnli 32", csr_read(0x801), 32);
    check("KLNL without a named locker reads as Unconfigured",
          KL_GETMDL_NL() | KL_SIZE_NL(), 0);
    check("kl.size Form A", KL_SIZE_A(1, 0), 48);
    check("kl.avail Form A", KL_SIZE_A(1, 1), 1);
    check("kl.size Form B (PI)", KL_SIZE_B(mdh_lo(0x020, 1, 0, 0)), 48);
    check("kl.size Form B (KeyType 1 PI)",
          KL_SIZE_B(mdh_lo(0x020, 1, 0, 1)), 32);
    check("kl.size Form B (invalid)", KL_SIZE_B(mdh_lo(0x000, 0, 1, 0)), 0);

    /* GR23: kl.exec in Ready invalidates and zeroes the output. */
    KL_MGMT(2, CFG_PROV, mdh_lo(0x000, 3, 0, 0), 0);
    KL_MV_IN(zv_k128);
    KL_MGMT_A(2, CFG_END);
    KL_SETNLI(32);
    cpy(buf, pt1, 16);
    KL_ECB(2, 1, pt1, buf, 16);
    check("exec in Ready -> Invalid", KL_GETST(2), ST_INVALID);
    check("output zeroed", ld64(buf) | ld64(buf + 8), 0);
    check("Error State: kl.size 16", KL_SIZE_A(2, 0), 16);

    KL_SETST(1, ST_ENCRYPT);
    KL_ECB(1, 1, pt1, buf, 16);
    check("AES-128 C.1", memeq(buf, ct128, 16), 1);
    KL_SETST(1, ST_DECRYPT);    /* MachinePolicy forbids decryption */
    check("decrypt not allowed -> Invalid", KL_GETST(1), ST_INVALID);

    /* AES-192 and AES-256 via kl.load, enc+dec. */
    {
        static const uint8_t k192[24] = {
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23 };

        PROVISION_LOAD(3, mdh_lo(0x010, 3, 0, 0), 0, k192, 24);
        KL_SETST(3, ST_ENCRYPT);
        KL_ECB(3, 1, pt1, buf, 16);
        check("AES-192 C.2", memeq(buf, ct192, 16), 1);
        KL_SETST(3, ST_DECRYPT);
        KL_ECB(3, 1, buf, buf, 16);
        check("AES-192 decrypt", memeq(buf, pt1, 16), 1);
    }
    PROVISION_LOAD(4, mdh_lo(0x020, 3, 0, 0), 0, zv_k256, 32);
    KL_SETST(4, ST_ENCRYPT);
    KL_ECB(4, 1, pt1, buf, 16);
    check("AES-256 C.3", memeq(buf, ct256, 16), 1);

    /* SP 800-38A F.1.5: four blocks in one kl.exec with LMUL = 4. */
    PROVISION_LOAD(4, mdh_lo(0x020, 3, 0, 0), 0, f15_key, 32);
    KL_SETST(4, ST_ENCRYPT);
    KL_ECB(4, 4, f15_pt, buf, 64);
    check("SP800-38A F.1.5 (4 blocks)", memeq(buf, f15_ct, 64), 1);
    KL_SETST(4, ST_DECRYPT);
    KL_ECB(4, 4, buf, buf, 64);
    check("SP800-38A F.1.6", memeq(buf, f15_pt, 64), 1);

    /* Unconfigured use, management end with nothing open (GR35, GR37). */
    cpy(buf, pt1, 16);
    check("exec on Unconfigured: no exception",
          TRAPS(KL_ECB(9, 1, pt1, buf, 16)), 0);
    check("exec on Unconfigured: output zeroed", ld64(buf) | ld64(buf + 8), 0);
    check("setst on Unconfigured: no operation",
          TRAPS(KL_SETST(9, ST_ENCRYPT)) | KL_GETST(9), 0);
    check("Error State immediate on Unconfigured: no operation",
          TRAPS(KL_SETST(9, ST_PRIV)) | KL_GETST(9), 0);
    check("mgmt end on a Valid locker -> illegal",
          TRAPS(KL_MGMT_A(4, CFG_END)), CAUSE_ILLEGAL);
    KL_SETNLI(9);
    check("mgmt end on Unconfigured: no exception",
          TRAPS(KL_MGMT_A(9, CFG_END)), 0);
    check("... and klnamedlocker = 32", csr_read(0x801), 32);
    check("export opening on Unconfigured: no exception",
          TRAPS(KL_MGMT_A(9, CFG_EXP)) | KL_GETST(9), 0);

    /* Reserved immediates (first group), and kl.clearall's. */
    check("setst #46 -> illegal", TRAPS(KL_SETST(4, 46)), CAUSE_ILLEGAL);
    check("setst #55 -> illegal", TRAPS(KL_SETST(4, 55)), CAUSE_ILLEGAL);
    check("setst #53 without Zklexpire -> illegal",
          TRAPS(KL_SETST(4, ST_EXPIRED)), CAUSE_ILLEGAL);
    check("setst #65 on K4 -> illegal",
          TRAPS(KL_SETST(4, CFG_CLEARALL)), CAUSE_ILLEGAL);
    check("setst #65 on KLNL -> illegal",
          TRAPS(KL_SETST_NL(CFG_CLEARALL)), CAUSE_ILLEGAL);
    check("K4 unchanged", KL_GETST(4), ST_DECRYPT);
}

static void test_scc(void)
{
    uint64_t m[2];

    puts_("scc\n");
    asm volatile("csrw 0xbc4, %0" :: "r"(ld64(zv_mloc)));
    asm volatile("csrw 0xbc5, %0" :: "r"(ld64(zv_mloc + 8)));
    asm volatile("csrw 0x5e0, %0" :: "r"(ld64(zv_sloc)));
    asm volatile("csrw 0x5e1, %0" :: "r"(ld64(zv_sloc + 8)));

    /* Export compared byte for byte with the spec model. */
    PROVISION_LOAD(7, mdh_lo(0x020, 3, 0, 0), MDH_HI(0, 0x140),
                   zv_k256, 32);
    KL_SETST(7, ST_ENCRYPT);
    check("kl.size of the SCC", KL_SIZE_A(7, 0), 64);
    memset(img, 0xa5, sizeof(img));
    EXPORT(7, img);
    check("export completed", KL_GETST(7), ST_ENCRYPT);
    check("SCC (MLocality, SLocality) matches spec model",
          memeq(img, zv_scc_a, 64), 1);

    /* Import into another locker and use it. */
    IMPORT(8, zv_scc_a);
    check("import restores Encrypt", KL_GETST(8), ST_ENCRYPT);
    KL_ECB(8, 1, pt1, buf, 16);
    check("imported key encrypts", memeq(buf, ct256, 16), 1);

    /* Export with kl.mvout to a vector register gives the same bytes. */
    KL_GETMD(8, m);
    KL_MGMT_A(8, CFG_EXP);
    KL_MV_VOUT(buf, 48);
    check("kl.mvout keeps klstart", csr_read(0x800), 48);
    KL_MGMT(8, CFG_END, m[0], m[1]);
    check("kl.mvout export = kl.store export", memeq(buf, zv_scc_a + 16, 48),
          1);
    check("kl.mvout outside export -> illegal",
          TRAPS(KL_MV_VOUT(buf, 16)), CAUSE_ILLEGAL);
    KL_SETNLI(32);
    memset(buf, 0xa5, 16);
    check("kl.mvout without a named locker: no exception",
          TRAPS(KL_MV_VOUT(buf, 16)), 0);
    check("... writes zeros", ld64(buf) | ld64(buf + 8), 0);

    /* ChipFamScrt binding. */
    IMPORT(9, zv_scc_b);
    check("import (ChipFamScrt)", KL_GETST(9), ST_READY);
    EXPORT(9, img);
    check("SCC (ChipFamScrt) matches spec model", memeq(img, zv_scc_b, 48), 1);

    /* Tampering and wrong Localities fail authentication. */
    cpy(img, zv_scc_a, 64);
    img[16] ^= 1;
    IMPORT(10, img);
    check("tampered SIV -> Authentication Failed", KL_GETST(10), ST_MGMT_AUTH);
    KL_MGMT(10, CFG_IMP, ld64(img), ld64(img + 8));
    KL_LOAD_(img + 16);
    KL_MGMT(10, CFG_END, ld64(img), ld64(img + 8));
    check("klnamedlocker kept after auth failure", csr_read(0x801), 10);
    KL_SETNLI(32);
    asm volatile("csrw 0x5e0, %0" :: "r"(ld64(zv_sloc) ^ 1));
    IMPORT(10, zv_scc_a);
    check("other SLocality -> Authentication Failed", KL_GETST(10),
          ST_MGMT_AUTH);
    asm volatile("csrw 0x5e0, %0" :: "r"(0ul));
    asm volatile("csrw 0x5e1, %0" :: "r"(0ul));
    IMPORT(10, zv_scc_a);
    check("unconfigured SLocality -> Invalid", KL_GETST(10), ST_INVALID);
    asm volatile("csrw 0x5e0, %0" :: "r"(ld64(zv_sloc)));
    asm volatile("csrw 0x5e1, %0" :: "r"(ld64(zv_sloc + 8)));

    /* Error-State transfer: MDH only. */
    KL_SETST(10, ST_PRIV);
    KL_GETMD(10, m);
    check("Error State kl.size", KL_SIZE_A(10, 0), 16);
    KL_MGMT(11, CFG_IMP, m[0], m[1]);
    check("short import", KL_GETST(11), ST_PRIV);
    check("klnamedlocker names it", csr_read(0x801), 11);
    check("completion after a short import: no operation",
          TRAPS(KL_MGMT(11, CFG_END, m[0], m[1])), 0);
    check("... the Error State kept", KL_GETST(11), ST_PRIV);
    KL_SETNLI(32);

    /* Unsupported Machine (SM4_ECB) and invalid Metadata at provisioning. */
    check("unsupported Machine -> unsupported-Metadata",
          TRAPS(KL_MGMT(12, CFG_PROV, mdh_lo(0x030, 1, 0, 0), 0)),
          CAUSE_UNSUPPORTED);
    check("left Unconfigured", KL_GETST(12), 0);
    check("klnamedlocker names it after the exception", csr_read(0x801), 12);
    check("SCProtection Level B -> unsupported-Metadata",
          TRAPS(KL_MGMT(12, CFG_PROV, mdh_lo(0x000, 1, 0, 0) | 1ul << 16, 0)),
          CAUSE_UNSUPPORTED);
    KL_MGMT(12, CFG_PROV, mdh_lo(0x000, 1, 0, 0) | 3ul << 16, 0);
    check("SCProtection 3 -> Invalid", KL_GETST(12), ST_INVALID);
    KL_MGMT(12, CFG_PROV, mdh_lo(0x000, 1, 0, 0) | 1ul << 62, 0);
    check("Version 1 -> Invalid", KL_GETST(12), ST_INVALID);
    check("Invalid MDH holds only State", KL_GETMDL(12),
          (uint64_t)ST_INVALID << 18);
    KL_MGMT(12, CFG_PROV, mdh_lo(0x000, 1, 0, 0), MDH_HI(0, 3 << 4));
    check("Locality[5:4] = 3 -> Invalid", KL_GETST(12), ST_INVALID);
    KL_MGMT(12, CFG_PROV, mdh_lo(0x000, 1, 0, 0), MDH_HI(0, 1));
    check("SiPScrt -> substituted ChipFamScrt", KL_GETST(12), CFG_PROV);
    KL_MGMT(12, CFG_PROV, mdh_lo(0x000, 1, 0, 0), MDH_HI(0, 3));
    check("ChipScrt, no substitute -> Invalid", KL_GETST(12), ST_INVALID);
    check("import opening of Form A (KLIOBUF) -> illegal",
          TRAPS(KL_MGMT_A(12, CFG_IMP)), CAUSE_ILLEGAL);
    check("... locker unchanged", KL_GETST(12), ST_INVALID);
    KL_SETNLI(32);
}

/* KLNL, kl.getnl/kl.setnl(i), and transfers without a usable locker. */
static void test_klnl(void)
{
    static uint8_t pi[32] __attribute__((aligned(16)));
    uint64_t m[2];

    puts_("klnl\n");
    /* A management routine that names its locker only through KLNL. */
    KL_SETNL(17);
    check("kl.setnl", KL_GETNL(), 17);
    cpy(pi, zv_k128, 16);
    KL_MGMT_NL(CFG_PROV, mdh_lo(0x000, 1, 0, 0), 0);
    check("KLNL opening", KL_GETST(17), CFG_PROV);
    KL_LOAD_(pi);
    KL_MGMT_A_NL(CFG_END);
    check("KLNL completion", KL_GETST_NL(), ST_READY);
    /* GR8: so do kl.exec and every kl.setst but kl.clearall. */
    KL_SETST_NL(ST_ENCRYPT);
    check("Encrypt on KLNL", KL_GETST(17), ST_ENCRYPT);
    KL_ECB_NL(1, pt1, buf, 16);
    check("kl.exec on KLNL", memeq(buf, ct128, 16), 1);
    KL_SETST_NL(CFG_CLEAR_ADS);
    check("kl.clearads on KLNL", KL_GETST(17), ST_ENCRYPT);
    KL_SETST_NL(ST_READY);
    check("Ready on KLNL", KL_GETST(17), ST_READY);
    /* GR3: r with any locker field but X0 is reserved; so is r elsewhere. */
    check("kl.setst with r and K17 -> illegal",
          TRAPS(INSN(SETST(ST_ENCRYPT, 0, 1, 0, 17))), CAUSE_ILLEGAL);
    check("kl.mgmt with r and K17 -> illegal",
          TRAPS(INSN(SETST(CFG_EXP, 0, 1, 0, 17))), CAUSE_ILLEGAL);
    check("kl.exec with r and K17 -> illegal",
          TRAPS(INSN(R4(F7_EXEC(0) | F7_KLNL, V8, 17, V8))), CAUSE_ILLEGAL);
    check("kl.getmd with r and K17 -> illegal",
          TRAPS(INSN(R4(F7_GETMDL | F7_KLNL, 0, 17, X_A0))), CAUSE_ILLEGAL);
    check("kl.size with r and K17 -> illegal",
          TRAPS(INSN(R4(F7_SIZE(0, 0) | F7_KLNL, 0, 17, X_A0))),
          CAUSE_ILLEGAL);
    check("kl.mvin with r -> illegal",
          TRAPS(INSN(MV_IN_X(X_A2) | F7_KLNL << 25)), CAUSE_ILLEGAL);
    check("kl.getnl with r -> illegal",
          TRAPS(INSN(R4(F7_GETNL | F7_KLNL, 0, 0, X_A0))), CAUSE_ILLEGAL);
    check("... State kept", KL_GETST(17), ST_READY);
    KL_SETST(17, ST_ENCRYPT);
    KL_ECB(17, 1, pt1, buf, 16);
    check("KLNL-provisioned key", memeq(buf, ct128, 16), 1);
    KL_SETST_NL(0);
    check("kl.clear KLNL", KL_GETST(17), 0);
    check("... resets klnamedlocker", KL_GETNL(), 32);
    /* GR10: usage on KLNL without a named locker performs no operation. */
    check("Encrypt on KLNL without a named locker: no operation",
          TRAPS(KL_SETST_NL(ST_ENCRYPT)), 0);
    KL_ECB_NL(1, pt1, buf, 16);
    check("kl.exec on KLNL without a named locker writes zeros",
          memeq(buf, zero16, 16), 1);
    /* GR9: so does an opening, which reads no operand (GR37). */
    check("KLNL opening without a named locker: no operation",
          TRAPS(KL_MGMT_NL(CFG_PROV, mdh_lo(0x000, 1, 0, 0), 0)), 0);
    check("... leaves klnamedlocker", KL_GETNL(), 32);
    check("... leaves the locker Unconfigured", KL_GETST(17), 0);
    check("Form A KLNL opening without a named locker: no operation",
          TRAPS(KL_MGMT_A_NL(CFG_PROV)), 0);
    check("KLNL export opening without a named locker: no operation",
          TRAPS(KL_MGMT_A_NL(CFG_EXP)), 0);
    check("KLNL completion without a named locker: no operation",
          TRAPS(KL_MGMT_A_NL(CFG_END)), 0);
    KL_SETNLI(33);
    check("kl.setnli 33 leaves it", KL_GETNL(), 32);

    /* With klnamedlocker = 32, x0: no operation, no alignment check. */
    csr_write(0x800, 32);
    check("kl.load without a named locker: no exception",
          TRAPS(KL_LOAD_(pi + 1)), 0);
    check("... klstart = 0", csr_read(0x800), 0);
    check("kl.input without Zklio -> illegal", TRAPS(KL_LOAD_XL(pi, 16)),
          CAUSE_ILLEGAL);
    KL_MV_OUT(m);
    check("kl.mvout without a named locker writes zeros", m[0] | m[1], 0);

    /* With a named locker: Xl, alignment, and an Error-State locker. */
    KL_MGMT(18, CFG_PROV, mdh_lo(0x000, 1, 0, 0), 0);
    check("kl.load with Xl != 0 -> illegal", TRAPS(KL_LOAD_XL(pi, 16)),
          CAUSE_ILLEGAL);
    check("kl.load misaligned -> address-misaligned", TRAPS(KL_LOAD_(pi + 8)),
          CAUSE_LOAD_MIS);
    check("... mtval", trap_tval, (uint64_t)(pi + 8));
    KL_SETST_NL(ST_PRIV);
    check("Error State set on KLNL in a Configuration State (GR41)",
          KL_GETST(18), ST_PRIV);
    check("kl.load on an Error-State locker: no operation",
          TRAPS(KL_LOAD_(pi)), 0);
    check("... still checks the alignment", TRAPS(KL_STORE_(img + 8)),
          CAUSE_STORE_MIS);
    KL_MV_OUT(m);
    check("kl.mvout on an Error-State locker writes zeros", m[0] | m[1], 0);
    check("completion on an Error-State locker: no operation",
          TRAPS(KL_MGMT_A(18, CFG_END)), 0);
    check("... klnamedlocker names it", KL_GETNL(), 18);
    KL_SETNLI(32);
}

static void test_nested(void)
{
    uint64_t m[2];
    static uint8_t pccc[48] __attribute__((aligned(16)));

    puts_("nested\n");
    /* Partial provisioning of K13 interrupted after the first block. */
    KL_MGMT(13, CFG_PROV, mdh_lo(0x020, 3, 0, 0), 0);
    KL_MV_IN(zv_k256);
    /* Context switch: save klstart, export the partial locker (PCCC). */
    {
        uint64_t klstart = csr_read(0x800);

        check("klstart mid-provisioning", klstart, 16);
        KL_GETMD(13, m);
        cpy(pccc, m, 16);
        KL_MGMT_A(13, CFG_EXP);
        check("nested export state", KL_GETST(13), CFG_PPI_EXP);
        KL_STORE_(pccc + 16);
        check("PCCC is the clear PI content", memeq(pccc + 16, zv_k256, 16), 1);
        KL_MGMT(13, CFG_END, m[0], m[1]);
        check("nested export completion", KL_GETST(13), CFG_PROV);
        KL_SETST(13, 0);
        check("clear resets klnamedlocker", csr_read(0x801), 32);

        /* Restore: re-import the PCCC, then resume at klstart. */
        KL_MGMT(13, CFG_IMP, m[0], m[1]);
        check("nested import state", KL_GETST(13), CFG_PPI_IMP);
        KL_LOAD_(pccc + 16);
        KL_MGMT(13, CFG_END, m[0], m[1]);
        check("restored provisioning", KL_GETST(13), CFG_PROV);
        csr_write(0x800, klstart);
    }
    KL_MV_IN(zv_k256 + 16);
    KL_MGMT_A(13, CFG_END);
    KL_SETNLI(32);
    KL_SETST(13, ST_ENCRYPT);
    KL_ECB(13, 1, pt1, buf, 16);
    check("resumed provisioning yields the key", memeq(buf, ct256, 16), 1);

    /* Using a locker under management: privilege violation. */
    KL_GETMD(13, m);
    KL_MGMT_A(13, CFG_EXP);
    check("exec in Config State -> privilege-violation",
          TRAPS(KL_ECB(13, 1, pt1, buf, 16)), CAUSE_PRIV_VIOL);
    check("setst in Config State -> privilege-violation",
          TRAPS(KL_SETST(13, ST_READY)), CAUSE_PRIV_VIOL);
    check("other locker's kl.mgmt meanwhile -> illegal",
          TRAPS(KL_MGMT_A(14, CFG_EXP)), CAUSE_ILLEGAL);
    KL_STORE_(img);
    KL_MGMT(13, CFG_END, m[0], m[1]);
    check("export completed", KL_GETST(13), ST_ENCRYPT);
    KL_SETNLI(32);
}

static void test_priv(void)
{
    uint8_t first[16];

    puts_("priv\n");
    /* UsagePolicy bit 0 denies U-mode. */
    PROVISION_LOAD(5, mdh_lo(0x000, 1, 0, 0), MDH_HI(1, 0), zv_k128, 16);
    KL_SETST(5, ST_ENCRYPT);
    {
        uint64_t n = trap_count;

        run_in_u(u_use_k5);
        check("U-mode use with U denied: two traps", trap_count - n, 2);
        check("U-mode use with U denied -> privilege-violation",
              trap_prev_cause, CAUSE_PRIV_VIOL);
        /* kl.clear is a configuration instruction: no policy gates it. */
        n = trap_count;
        run_in_u(u_clear_k5);
        check("U-mode kl.clear with U denied: no trap", trap_count - n, 1);
        check("... cleared", KL_GETST(5), 0);
    }
    /* UsagePolicy bit 3 denies M-mode; U-mode may use it. */
    PROVISION_LOAD(6, mdh_lo(0x000, 1, 0, 0), MDH_HI(8, 0), zv_k128, 16);
    check("M-mode setst with M denied -> privilege-violation",
          TRAPS(KL_SETST(6, ST_ENCRYPT)), CAUSE_PRIV_VIOL);
    run_in_u(u_use_k6);     /* setst not done: exec in Ready -> Invalid */
    check("U-mode exec in Ready -> Invalid", KL_GETST(6), ST_INVALID);

    /* KeyType 1 with the all-ones SKID: a random key. */
    {
        static const uint8_t skid[8] = { 0xff, 0xff, 0xff, 0xff,
                                         0xff, 0xff, 0xff, 0xff };

        PROVISION_LOAD(15, mdh_lo(0x020, 3, 0, 1), 0, skid, 8);
        check("random key provisioned", KL_GETST(15), ST_READY);
        check("KeyType becomes 0", (KL_GETMDL(15) >> 28) & 3, 0);
        KL_SETST(15, ST_ENCRYPT);
        KL_ECB(15, 1, pt1, first, 16);
        check("random key differs from zero key",
              memeq(first, ct256, 16), 0);
        EXPORT(15, img);
        KL_SETST(15, 0);
        IMPORT(16, img);
        KL_ECB(16, 1, pt1, buf, 16);
        check("random key survives export/import", memeq(buf, first, 16), 1);
    }

    /* kl.clearall */
    KL_SETNLI(16);
    csr_write(0x800, 48);
    KL_CLEARALL();
    check("clearall", KL_GETST(16) | KL_GETST(1) | KL_GETST(8), 0);
    check("clearall klnamedlocker", csr_read(0x801), 32);
    check("clearall klstart", csr_read(0x800), 0);
    check("SD reflects KLS dirty", csr_read(mstatus) >> 63, 1);
}

#ifndef ZKL_NO_CTR
/* Keystream ks XOR plaintext pt is ct. */
static int ctr_ok(const uint8_t *ks, const uint8_t *pt, const uint8_t *ct,
                  size_t n)
{
    for (size_t i = 0; i < n; i++) {
        if ((ks[i] ^ pt[i]) != ct[i]) {
            return 0;
        }
    }
    return 1;
}

/* A fresh AES128_CTR locker (encrypt only) in Ready. */
#define CTR_FRESH(k) \
    PROVISION_LOAD(k, mdh_lo(0x001, 1, 0, 0), 0, zv_ctr_k128, 16)

static void test_ctr(void)
{
    static const uint8_t zero[16] __attribute__((aligned(16)));
    static uint8_t ks[64] __attribute__((aligned(16)));
    uint8_t e0[16];

    puts_("ctr\n");
    /* SP 800-38A F.5: Form C IV <- ICB, Form B ctr <- 0xfcfdfeff. */
    CTR_FRESH(1);
    check("CTR provisioned", KL_GETST(1), ST_READY);
    check("kl.size AES128_CTR", KL_SIZE_A(1, 0), 64);
    KL_SETST_C(1, ST_OPERATE, zv_ctr_icb, 16);
    check("Form C into Operate (encrypt-only policy)", KL_GETST(1), ST_OPERATE);
    KL_SETST_B(1, SET_AUX, 0xfcfdfeff);
    check("set_aux_value keeps Operate", KL_GETST(1), ST_OPERATE);
    KL_CTR(1, 4, ks, 64);
    check("F.5.1 (4 blocks)", ctr_ok(ks, zv_ctr_pt, zv_ctr_ct128, 64), 1);

    PROVISION_LOAD(2, mdh_lo(0x011, 3, 0, 0), 0, zv_ctr_k192, 24);
    check("kl.size AES192_CTR", KL_SIZE_A(2, 0), 80);
    KL_SETST_B(2, SET_AUX, 0xfcfdfeff);
    check("set_aux_value in Ready", KL_GETST(2), ST_READY);
    KL_SETST_C(2, ST_OPERATE, zv_ctr_icb, 16);
    KL_CTR(2, 1, ks, 16);
    KL_CTR(2, 2, ks + 16, 32);
    KL_CTR(2, 1, ks + 48, 16);
    check("F.5.3 (1 + 2 + 1 blocks)", ctr_ok(ks, zv_ctr_pt, zv_ctr_ct192, 64),
          1);

    PROVISION_LOAD(3, mdh_lo(0x021, 1, 0, 0), 0, zv_ctr_k256, 32);
    check("kl.size AES256_CTR", KL_SIZE_A(3, 0), 80);
    KL_SETST_C(3, ST_OPERATE, zv_ctr_icb, 12);      /* KLLEN 96 suffices */
    KL_SETST_B(3, SET_AUX, 0x1fcfdfeff);            /* 32 LSBs of Xs */
    KL_CTR(3, 4, ks, 64);
    check("F.5.5", ctr_ok(ks, zv_ctr_pt, zv_ctr_ct256, 64), 1);

    /* The counter wraps silently; a new IV in Operate keeps ctr. */
    KL_SETST_C(1, ST_OPERATE, zv_ctr_wrap_iv, 16);
    KL_SETST_B(1, SET_AUX, 0xfffffffe);
    KL_CTR(1, 1, ks, 16);
    KL_SETST_C(1, ST_OPERATE, zv_ctr_wrap_iv, 16);
    KL_CTR(1, 4, ks + 16, 48);
    check("ctr wraps, Operate -> Operate keeps ctr",
          memeq(ks, zv_ctr_wrap_ks, 64), 1);

    /* Ready sets ctr to 0: the block is E(K, IV = 0 | ctr = 0). */
    PROVISION_LOAD(4, mdh_lo(0x000, 1, 0, 0), 0, zv_ctr_k128, 16);
    KL_SETST(4, ST_ENCRYPT);
    KL_ECB(4, 1, zero, e0, 16);
    KL_SETST(1, ST_READY);
    check("Operate -> Ready", KL_GETST(1), ST_READY);
    KL_SETST_C(1, ST_OPERATE, zero, 16);
    KL_CTR(1, 1, ks, 16);
    check("Ready resets ctr", memeq(ks, e0, 16), 1);

    /* KLS: the keystream advanced ctr, so the locker is dirty. */
    set_kls(2);
    KL_CTR(1, 1, ks, 16);
    check("CTR kl.exec sets KLS Dirty", (csr_read(mstatus) >> 25) & 3, 3);

    /*
     * A Form A kl.setst into Operate would substitute the KLIOBUF for the
     * expected Form C: illegal without Zklio.  So is a Form C kl.setst
     * issued with vstart != 0 (GR5).
     */
    CTR_FRESH(5);
    check("Form A into Operate -> illegal", TRAPS(KL_SETST(5, ST_OPERATE)),
          CAUSE_ILLEGAL);
    check("... State kept", KL_GETST(5), ST_READY);
    check("Form C with vstart != 0 -> illegal",
          TRAPS(KL_SETST_C_VSTART(5, ST_OPERATE, zv_ctr_icb, 16)),
          CAUSE_ILLEGAL);
    check("... State kept", KL_GETST(5), ST_READY);
    /* A locker driven only through KLNL (GR8): SP 800-38A F.5.1. */
    KL_SETNLI(5);
    KL_SETST_C_NL(ST_OPERATE, zv_ctr_icb, 16);
    KL_SETST_B_NL(SET_AUX, 0xfcfdfeff);
    check("CTR IV and counter on KLNL", KL_GETST(5), ST_OPERATE);
    KL_CTR_NL(4, ks, 64);
    check("F.5.1 on KLNL", ctr_ok(ks, zv_ctr_pt, zv_ctr_ct128, 64), 1);
    KL_SETNLI(32);

    /* GR39: the substitution is illegal before the UsagePolicy is seen. */
    PROVISION_LOAD(5, mdh_lo(0x001, 1, 0, 0), MDH_HI(1, 0), zv_ctr_k128, 16);
    {
        uint64_t n = trap_count;

        run_in_u(u_operate_a_k5);
        check("U-mode Form A into Operate with U denied -> illegal",
              trap_count - n == 2 ? trap_prev_cause : 0, CAUSE_ILLEGAL);
        check("... State kept", KL_GETST(5), ST_READY);
    }

    /* MR1, GR23: everything else invalidates. */
    CTR_FRESH(5);
    KL_SETST_C(5, SET_AUX, zv_ctr_icb, 16);
    check("Form C set_aux_value -> Invalid", KL_GETST(5), ST_INVALID);
    CTR_FRESH(5);
    KL_SETST_C(5, ST_OPERATE, zv_ctr_icb, 8);
    check("Form C with KLLEN 64 -> Invalid", KL_GETST(5), ST_INVALID);
    CTR_FRESH(5);
    KL_SETST(5, ST_ENCRYPT);
    check("Encrypt on a CTR Machine -> Invalid", KL_GETST(5), ST_INVALID);
    CTR_FRESH(5);
    cpy(ks, zv_ctr_icb, 16);
    KL_CTR(5, 1, ks, 16);
    check("exec in Ready -> Invalid", KL_GETST(5), ST_INVALID);
    check("output zeroed", ld64(ks) | ld64(ks + 8), 0);
    CTR_FRESH(5);
    KL_SETST_C(5, ST_OPERATE, zv_ctr_icb, 16);
    KL_ECB(5, 1, pt1, buf, 16);
    check("Form A exec in Operate -> Invalid", KL_GETST(5), ST_INVALID);
    check("Form C exec in Encrypt (mixed operands) -> illegal",
          TRAPS(KL_CTR(4, 1, ks, 16)),
          CAUSE_ILLEGAL);
    KL_SETST_C(4, ST_OPERATE, zv_ctr_icb, 16);
    check("Operate on an ECB Machine -> Invalid", KL_GETST(4), ST_INVALID);

    /* kl.size / kl.avail of supplied CTR Metadata. */
    check("kl.size Form B (CTR PI)", KL_SIZE_B(mdh_lo(0x001, 1, 0, 0)), 32);
    check("kl.size Form B (CTR KeyType 1 PI)",
          KL_SIZE_B(mdh_lo(0x021, 1, 0, 1)), 32);
    check("kl.size Form B (AES256_CTR in Operate)",
          KL_SIZE_B(mdh_lo(0x021, 1, ST_OPERATE, 0)), 80);
    check("kl.size Form B (CTR in Encrypt)",
          KL_SIZE_B(mdh_lo(0x001, 1, ST_ENCRYPT, 0)), 0);
    check("kl.size Form B (ECB in Operate)",
          KL_SIZE_B(mdh_lo(0x000, 1, ST_OPERATE, 0)), 0);
    check("kl.avail Form B (CTR)", KL_AVAIL_B(mdh_lo(0x011, 1, 0, 0)), 1);

    /* Export in Operate, byte for byte with the spec model, and resume. */
    PROVISION_LOAD(6, mdh_lo(0x001, 1, 0, 0), MDH_HI(0, 2), zv_ctr_k128, 16);
    KL_SETST_C(6, ST_OPERATE, zv_ctr_icb, 16);
    KL_SETST_B(6, SET_AUX, 0xfcfdfeff);
    KL_CTR(6, 2, ks, 32);
    memset(img, 0xa5, sizeof(img));
    EXPORT(6, img);
    check("export in Operate completed", KL_GETST(6), ST_OPERATE);
    check("SCC (AES128_CTR, IV, ctr) matches spec model",
          memeq(img, zv_scc_ctr128, 64), 1);
    IMPORT(7, zv_scc_ctr128);
    check("import restores Operate", KL_GETST(7), ST_OPERATE);
    KL_CTR(7, 2, ks + 32, 32);
    check("imported locker continues the keystream",
          ctr_ok(ks, zv_ctr_pt, zv_ctr_ct128, 64), 1);

    /* Ready after use clears IV and ctr: the SCC holds only the new ctr. */
    PROVISION_LOAD(8, mdh_lo(0x011, 3, 0, 0), MDH_HI(0, 0x140),
                   zv_ctr_k192, 24);
    KL_SETST_C(8, ST_OPERATE, zv_ctr_icb, 16);
    KL_SETST_B(8, SET_AUX, 0xfcfdfeff);
    KL_CTR(8, 1, ks, 16);
    KL_SETST(8, ST_READY);
    KL_SETST_B(8, SET_AUX, 0x01020304);
    check("kl.size of the AES192_CTR SCC", KL_SIZE_A(8, 0), 80);
    EXPORT(8, img);
    check("SCC (AES192_CTR in Ready) matches spec model",
          memeq(img, zv_scc_ctr192, 80), 1);
    IMPORT(9, zv_scc_ctr192);
    check("import restores Ready", KL_GETST(9), ST_READY);
}
#else
/* x-zkl-ctr=false: the CTR Machines are unsupported Metadata. */
static void test_no_ctr(void)
{
    puts_("no ctr\n");
    check("kl.size Form B (CTR PI)", KL_SIZE_B(mdh_lo(0x001, 1, 0, 0)), 0);
    check("kl.avail Form B (CTR)", KL_AVAIL_B(mdh_lo(0x001, 1, 1, 0)), 0);
    check("kl.size Form B (ECB PI)", KL_SIZE_B(mdh_lo(0x000, 1, 0, 0)), 32);
    check("CTR provisioning -> unsupported-Metadata",
          TRAPS(KL_MGMT(1, CFG_PROV, mdh_lo(0x001, 1, 0, 0), 0)),
          CAUSE_UNSUPPORTED);
    check("left Unconfigured", KL_GETST(1), 0);
    check("CTR import -> unsupported-Metadata",
          TRAPS(KL_MGMT(1, CFG_IMP, ld64(zv_scc_ctr128),
                        ld64(zv_scc_ctr128 + 8))), CAUSE_UNSUPPORTED);
    check("left Unconfigured, klnamedlocker names it",
          KL_GETST(1) | (csr_read(0x801) ^ 1), 0);
    KL_SETNLI(32);
}
#endif

/* ---------------------------------------------------------------- gcm */

#ifndef ZKL_NO_GCM
/* kl.exec Kk, v8 (Form B, input only) on the n bytes at p, e8 m4 */
#define KL_EXEC_B(k, p, n) do {                                         \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m4, ta, ma\n"                     \
                 "vle8.v v8, (%2)\n"                                    \
                 ".4byte %3\n"                                          \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(p),             \
                   "i"(R4(F7_EXEC(1), V8, k, 0)) : "memory", "v8", "v9", \
                   "v10", "v11");                                       \
} while (0)
#define KL_EXEC_B_NL(p, n) do {                                         \
    uint64_t _vl;                                                       \
    asm volatile("vsetvli %0, %1, e8, m4, ta, ma\n"                     \
                 "vle8.v v8, (%2)\n"                                    \
                 ".4byte %3\n"                                          \
                 : "=&r"(_vl) : "r"((uint64_t)(n)), "r"(p),             \
                   "i"(R4(F7_EXEC(1) | F7_KLNL, V8, 0, 0))              \
                 : "memory", "v8", "v9", "v10", "v11");                 \
} while (0)

static const char *const gcm_tc[] = {
    "tc1", "tc2", "tc3", "tc4", "tc5", "tc6", "tc13", "tc14", "tc15",
    "tc16", "tc17", "tc18", "tc4 with AES-192",
};
static uint8_t gcm_ab[64] __attribute__((aligned(16)));
static uint8_t gcm_lb[16] __attribute__((aligned(16)));

/* The length block: the AAD and text lengths in bits, big-endian. */
static void gcm_lens(uint64_t alen, uint64_t plen)
{
    for (int i = 0; i < 8; i++) {
        gcm_lb[i] = (8 * alen) >> (56 - 8 * i);
        gcm_lb[8 + i] = (8 * plen) >> (56 - 8 * i);
    }
}

/*
 * The helpers below act on KLNL, as a library does.  From any Valid State:
 * Ready, the IV in transfers of ivc bytes, then the AAD, zero-padded.
 */
static void gcm_iv_aad(const struct zv_gcm *v, uint32_t ivc)
{
    KL_SETST_NL(ST_READY);
    KL_SETST_B_NL(SET_AUX, 8 * v->ivlen);
    for (uint32_t o = 0; o < v->ivlen; o += ivc) {
        KL_EXEC_B_NL(v->iv + o, v->ivlen - o < ivc ? v->ivlen - o : ivc);
    }
    if (v->alen) {
        memset(gcm_ab, 0, sizeof(gcm_ab));
        cpy(gcm_ab, v->a, v->alen);
        KL_EXEC_B_NL(gcm_ab, (v->alen + 15) & ~15u);
    }
}

/* Whole blocks in one kl.exec, then the last partial block. */
static void gcm_text(int dec, const uint8_t *in, uint8_t *out, uint32_t n)
{
    uint32_t full = n & ~15u;

    if (full) {
        KL_ECB_NL(4, in, out, full);
    }
    if (n > full) {
        if (dec) {
            KL_SETST_B_NL(ST_DLB, 8 * (n - full));
        } else {
            KL_SETST_B_NL(ST_ELB, 8 * (n - full));
        }
        KL_ECB_NL(1, in + full, out + full, n - full);
    }
}

/* Encrypt a vector's message on locker k; the State at the end. */
static uint64_t gcm_enc(int k, const struct zv_gcm *v, uint32_t ivc,
                        uint8_t *ct, uint8_t *tag)
{
    uint64_t st;

    KL_SETNL(k);
    gcm_iv_aad(v, ivc);
    KL_SETST_NL(ST_ENCRYPT);
    gcm_text(0, v->p, ct, v->plen);
    gcm_lens(v->alen, v->plen);
    KL_SETST_C_NL(ST_ETF, gcm_lb, 16);
    KL_CTR_NL(1, tag, 16);
    st = KL_GETST_NL();
    KL_SETNLI(32);
    return st;
}

/* Decrypt it, checking tag; the State at the end. */
static uint64_t gcm_dec(int k, const struct zv_gcm *v, const uint8_t *tag,
                        uint8_t *pt)
{
    uint64_t st;

    KL_SETNL(k);
    gcm_iv_aad(v, 16);
    KL_SETST_NL(ST_DECRYPT);
    gcm_text(1, v->c, pt, v->plen);
    gcm_lens(v->alen, v->plen);
    KL_SETST_C_NL(ST_DTF, gcm_lb, 16);
    KL_SETST_C_NL(ST_HV, tag, 16);
    st = KL_GETST_NL();
    KL_SETNLI(32);
    return st;
}

/* An AES128_GCM locker with tc4's key, in Ready; then tc4's IV and AAD. */
#define GCM_FRESH(k, policy) \
    PROVISION_LOAD(k, mdh_lo(0x004, policy, 0, 0), 0, zv_gcm3_k, 16)
#define GCM_HA(k) do {                                                  \
    KL_SETNL(k);                                                        \
    gcm_iv_aad(&zv_gcm[3], 16);                                         \
    KL_SETNLI(32);                                                      \
} while (0)

static void test_gcm(void)
{
    static uint8_t ct[64], pt[64], tag[16] __attribute__((aligned(16)));
    static uint8_t bad[16] __attribute__((aligned(16)));
    const struct zv_gcm *v;
    uint64_t r;

    puts_("gcm\n");
    /*
     * McGrew-Viega tc1-6 and 13-18, and tc4 with AES-192: encrypt (IV in
     * 16-byte transfers), decrypt, a bad tag -> Failure, and from there
     * through Ready the message again (IV in one transfer).
     */
    for (int i = 0; i < (int)(sizeof(zv_gcm) / sizeof(zv_gcm[0])); i++) {
        v = &zv_gcm[i];
        PROVISION_LOAD(1, mdh_lo(0x004 | (v->klen - 16) / 8 << 4, 3, 0, 0), 0,
                       v->k, v->klen);
        r = gcm_enc(1, v, 16, ct, tag) == ST_SUCCESS;
        r |= memeq(ct, v->c, v->plen) << 1;
        r |= memeq(tag, v->t, 16) << 2;
        r |= (gcm_dec(1, v, v->t, pt) == ST_SUCCESS) << 3;
        r |= memeq(pt, v->p, v->plen) << 4;
        cpy(bad, v->t, 16);
        bad[15] ^= 1;
        r |= (gcm_dec(1, v, bad, pt) == ST_FAILURE) << 5;
        r |= (gcm_enc(1, v, v->ivlen, ct, tag) == ST_SUCCESS &&
              memeq(tag, v->t, 16)) << 6;
        check(gcm_tc[i], r, 0x7f);
    }

    /* tc4 on immediate lockers, the text in single blocks. */
    v = &zv_gcm[3];
    PROVISION_LOAD(8, mdh_lo(0x004, 1, 0, 0), 0, v->k, 16);
    KL_SETST_B(8, SET_AUX, 96);
    KL_EXEC_B(8, v->iv, 12);
    check("IV complete -> Hash_Absorb", KL_GETST(8), ST_HA);
    memset(gcm_ab, 0, sizeof(gcm_ab));
    cpy(gcm_ab, v->a, 20);
    KL_EXEC_B(8, gcm_ab, 16);
    KL_EXEC_B(8, gcm_ab + 16, 16);
    KL_SETST(8, ST_ENCRYPT);
    for (int o = 0; o < 48; o += 16) {
        KL_ECB(8, 1, v->p + o, ct + o, 16);
    }
    KL_SETST_B(8, ST_ELB, 96);
    KL_ECB(8, 1, v->p + 48, ct + 48, 12);
    gcm_lens(20, 60);
    KL_SETST_C(8, ST_ETF, gcm_lb, 16);
    KL_CTR(8, 1, tag, 8);
    check("tc4 on K8; a tag read with KLLEN 64 is truncated",
          memeq(ct, v->c, 60) && memeq(tag, v->t, 8) &&
          KL_GETST(8) == ST_SUCCESS, 1);

    /* kl.size and kl.avail. */
    check("kl.size Form B (GCM PI)", KL_SIZE_B(mdh_lo(0x004, 1, 0, 0)), 32);
    check("kl.size Form B (AES128_GCM in Encrypt)",
          KL_SIZE_B(mdh_lo(0x004, 3, ST_ENCRYPT, 0)), 96);
    check("kl.size Form B (AES192_GCM in Success)",
          KL_SIZE_B(mdh_lo(0x014, 3, ST_SUCCESS, 0)), 96);
    check("kl.size Form B (AES256_GCM in Set_Aux_Value)",
          KL_SIZE_B(mdh_lo(0x024, 3, SET_AUX, 0)), 112);
    check("kl.size Form B (GCM in Operate+1 = 3)",
          KL_SIZE_B(mdh_lo(0x004, 3, 3, 0)), 0);
    check("kl.avail Form B (GCM)", KL_AVAIL_B(mdh_lo(0x024, 3, 0, 0)), 1);

    /* MR1, GR22, GR23, GR27, MR2, MR10, MR11: invalid transitions. */
    GCM_FRESH(2, 3);
    KL_SETST(2, ST_ENCRYPT);
    check("Ready -> Encrypt -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    KL_SETST_B(2, SET_AUX, 0);
    check("IV of 0 bits -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    KL_SETST_B(2, SET_AUX, 92);
    check("IV of 92 bits -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    KL_SETST_B(2, SET_AUX, 8200);
    check("IV of 8200 bits -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    KL_SETST_B(2, SET_AUX, 480);
    KL_SETST(2, ST_HA);
    check("Hash_Absorb before the IV is complete -> Invalid", KL_GETST(2),
          ST_INVALID);
    GCM_FRESH(2, 3);
    KL_SETST_B(2, SET_AUX, 480);
    KL_EXEC_B(2, zv_gcm[5].iv, 12);
    check("a partial IV transfer that is not the last -> Invalid",
          KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    KL_SETST_B(2, SET_AUX, 480);
    KL_SETST(2, ST_READY);
    KL_SETST_B(2, SET_AUX, 96);
    KL_EXEC_B(2, zv_gcm[3].iv, 12);
    check("an incomplete IV left through Ready, a new one", KL_GETST(2), ST_HA);
    KL_EXEC_B(2, zv_gcm[3].a, 20);
    check("AAD not in whole blocks -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    GCM_HA(2);
    KL_CTR(2, 1, ct, 16);
    check("Form C kl.exec in Hash_Absorb -> Invalid", KL_GETST(2), ST_INVALID);
    check("  output zeroed", ld64(ct) | ld64(ct + 8), 0);
    GCM_FRESH(2, 3);
    KL_ECB(2, 1, pt1, ct, 16);
    check("kl.exec in Ready -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    GCM_HA(2);
    KL_SETST(2, ST_ENCRYPT);
    check("Form B kl.exec in Encrypt (mixed operands) -> illegal",
          TRAPS(KL_EXEC_B(2, pt1, 16)), CAUSE_ILLEGAL);
    check("Form A kl.setst into Enc_Tag_Finalize -> illegal (no Zklio)",
          TRAPS(KL_SETST(2, ST_ETF)), CAUSE_ILLEGAL);
    check("  State kept", KL_GETST(2), ST_ENCRYPT);
    KL_SETST_B(2, ST_ELB, 128);
    check("last block of 128 bits -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    GCM_HA(2);
    KL_SETST(2, ST_ENCRYPT);
    KL_SETST_B(2, ST_ELB, 96);
    KL_SETST_B(2, ST_ELB, 64);
    KL_ECB(2, 1, pt1, ct, 8);
    check("last block length replaced before its kl.exec", KL_GETST(2),
          ST_ELB);
    KL_ECB(2, 1, pt1, ct, 8);
    check("a second last block -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    GCM_HA(2);
    KL_SETST(2, ST_ENCRYPT);
    KL_SETST_B(2, ST_ELB, 96);
    KL_ECB(2, 1, pt1, ct, 12);
    KL_SETST_B(2, ST_ELB, 96);
    check("Enc_Last_Block again after its kl.exec -> Invalid", KL_GETST(2),
          ST_INVALID);
    GCM_FRESH(2, 3);
    GCM_HA(2);
    KL_SETST(2, ST_ENCRYPT);
    gcm_lens(20, 0);
    KL_SETST_C(2, ST_ETF, gcm_lb, 16);
    KL_SETST_C(2, ST_ETF, gcm_lb, 16);
    check("Enc_Tag_Finalize twice -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    GCM_HA(2);
    KL_SETST(2, ST_DECRYPT);
    KL_SETST_C(2, ST_DTF, gcm_lb, 16);
    KL_SETST_C(2, ST_HV, zv_gcm[3].t, 12);
    check("Hash_Verify with KLLEN 96 -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 2);
    GCM_HA(2);
    KL_SETST(2, ST_ENCRYPT);
    check("Encrypt, decrypt-only policy -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 1);
    GCM_HA(2);
    KL_SETST(2, ST_DECRYPT);
    check("Decrypt, encrypt-only policy -> Invalid", KL_GETST(2), ST_INVALID);
    GCM_FRESH(2, 3);
    check("a message to Success", gcm_enc(2, &zv_gcm[3], 16, ct, tag),
          ST_SUCCESS);
    KL_SETST_B(2, SET_AUX, 96);
    check("Success -> Set_Aux_Value -> Invalid", KL_GETST(2), ST_INVALID);

    /* The counter limit (the model seeded ctr ffffffff, start_ctr 1). */
    IMPORT(3, zv_scc_gcm_lim);
    check("import in Encrypt at ctr ffffffff", KL_GETST(3), ST_ENCRYPT);
    memset(ct, 0xa5, sizeof(ct));
    KL_ECB(3, 4, zv_gcm_p60, ct, 48);
    check("counter limit: one block, then Invalid and zeros",
          memeq(ct, zv_gcm_lim_out, 48) && KL_GETST(3) == ST_INVALID, 1);

    /* KLS: every GCM kl.exec changes the locker. */
    GCM_FRESH(2, 3);
    KL_SETST_B(2, SET_AUX, 96);
    set_kls(2);
    KL_EXEC_B(2, zv_gcm[3].iv, 12);
    check("GCM kl.exec sets KLS Dirty", (csr_read(mstatus) >> 25) & 3, 3);

    /* Export in Ready, Set_Aux_Value and Encrypt, byte for byte, and resume. */
    v = &zv_gcm[9];                     /* tc16 */
    PROVISION_LOAD(4, mdh_lo(0x024, 3, 0, 0), MDH_HI(0, 2), v->k, 32);
    check("kl.size AES256_GCM", KL_SIZE_A(4, 0), 112);
    EXPORT(4, img);
    check("SCC (AES256_GCM in Ready) matches spec model",
          memeq(img, zv_scc_gcm_ready, 112), 1);
    KL_SETST_B(4, SET_AUX, 480);
    KL_EXEC_B(4, zv_gcm[11].iv, 16);
    EXPORT(4, img);
    check("SCC (in Set_Aux_Value, 16 of 60 IV bytes) matches spec model",
          memeq(img, zv_scc_gcm_sav, 112), 1);
    IMPORT(5, zv_scc_gcm_sav);
    check("import restores Set_Aux_Value", KL_GETST(5), SET_AUX);
    KL_EXEC_B(5, zv_gcm[11].iv + 16, 44);
    check("the rest of the IV -> Hash_Absorb", KL_GETST(5), ST_HA);
    memset(gcm_ab, 0, sizeof(gcm_ab));
    cpy(gcm_ab, zv_gcm[11].a, 20);
    KL_SETNL(5);
    KL_EXEC_B_NL(gcm_ab, 32);
    KL_SETST_NL(ST_ENCRYPT);
    gcm_text(0, zv_gcm[11].p, ct, 60);
    gcm_lens(20, 60);
    KL_SETST_C_NL(ST_ETF, gcm_lb, 16);
    KL_CTR_NL(1, tag, 16);
    KL_SETNLI(32);
    check("... and finishes tc18", memeq(ct, zv_gcm[11].c, 60) &&
          memeq(tag, zv_gcm[11].t, 16), 1);

    PROVISION_LOAD(6, mdh_lo(0x024, 3, 0, 0), MDH_HI(0, 2), v->k, 32);
    KL_SETNL(6);
    gcm_iv_aad(v, 16);
    KL_SETST_NL(ST_ENCRYPT);
    KL_ECB_NL(1, v->p, ct, 16);
    KL_SETNLI(32);
    EXPORT(6, img);
    check("SCC (in Encrypt, one block done) matches spec model",
          memeq(img, zv_scc_gcm_enc, 112), 1);
    IMPORT(7, zv_scc_gcm_enc);
    check("import restores Encrypt", KL_GETST(7), ST_ENCRYPT);
    KL_SETNL(7);
    gcm_text(0, v->p + 16, ct + 16, 44);
    KL_SETST_C_NL(ST_ETF, gcm_lb, 16);
    KL_CTR_NL(1, tag, 16);
    KL_SETNLI(32);
    check("... and finishes tc16", memeq(ct, v->c, 60) &&
          memeq(tag, v->t, 16), 1);
}
#else
/* x-zkl-gcm=false: the GCM Machines are unsupported Metadata. */
static void test_no_gcm(void)
{
    puts_("no gcm\n");
    check("kl.size Form B (GCM PI)", KL_SIZE_B(mdh_lo(0x004, 1, 0, 0)), 0);
    check("kl.avail Form B (GCM)", KL_AVAIL_B(mdh_lo(0x024, 3, 1, 0)), 0);
    check("GCM provisioning -> unsupported-Metadata",
          TRAPS(KL_MGMT(1, CFG_PROV, mdh_lo(0x004, 3, 0, 0), 0)),
          CAUSE_UNSUPPORTED);
    check("left Unconfigured", KL_GETST(1), 0);
    check("GCM import -> unsupported-Metadata",
          TRAPS(KL_MGMT(1, CFG_IMP, ld64(zv_scc_gcm_ready),
                        ld64(zv_scc_gcm_ready + 8))), CAUSE_UNSUPPORTED);
    KL_SETNLI(32);
}
#endif

/* ---------------------------------------------------------------- status */

/*
 * Smklstatus and Ssklstatus (Zkl-ISA-priv.adoc <<KLE-CSR-llockerstatus>>):
 * from U-mode, an access to a locker whose mllockerstatus or sllockerstatus
 * field is Off raises the KLE locker-Off exception, except by kl.clear,
 * kl.clearall or a kl.mgmt opening a provisioning or an import, which make
 * it Dirty; a change of a locker makes both fields Dirty.  M-mode is gated
 * by neither and writes neither.
 */
#define CSR_MLLOCKERSTATUS  0xbc8
#define CSR_SLLOCKERSTATUS  0x5e2
enum { LS_OFF, LS_INITIAL, LS_CLEAN, LS_DIRTY };
#define LS_ALL_INITIAL      0x5555555555555555ull

static uint64_t ls(uint64_t v, int k)
{
    return (v >> (2 * k)) & 3;
}

static uint64_t ls_set(uint64_t v, int k, int f)
{
    return (v & ~(3ull << (2 * k))) | (uint64_t)f << (2 * k);
}

#define MLS()       csr_read(0xbc8)
#define SLS()       csr_read(0x5e2)
#define MLS_W(v)    csr_write(0xbc8, v)
#define SLS_W(v)    csr_write(0x5e2, v)

static volatile uint64_t u_val;

static void u_ecb_k3(void)      { KL_ECB(3, 1, pt1, buf, 16); }
static void u_enc_k3(void)      { KL_SETST(3, ST_ENCRYPT); }
static void u_getmd_k3(void)    { u_val = KL_GETMDL(3); }
static void u_getmd_nl(void)    { u_val = KL_GETMDL_NL(); }
static void u_size_nl(void)     { u_val = KL_SIZE_NL(); }
static void u_ecb_nl(void)      { KL_ECB_NL(1, pt1, buf, 16); }
static void u_load_nl(void)     { KL_LOAD_(img); }
static void u_load_xl_nl(void)  { KL_LOAD_XL(img, 1); }
static void u_invalid_k3(void)  { KL_SETST(3, ST_INVALID); }
static void u_export_k3(void)   { KL_MGMT_A(3, CFG_EXP); }
static void u_clear_k3(void)    { KL_SETST(3, 0); }
static void u_clearall(void)    { KL_CLEARALL(); }
static void u_sls(void)         { u_val = SLS(); }

static void u_prov_k4(void)
{
    PROVISION_LOAD(4, mdh_lo(0x000, 1, 0, 0), 0, zv_k128, 16);
}

#ifndef ZKL_NO_CTR
static void u_ctr_k5(void)      { KL_CTR(5, 1, buf, 16); }
static void u_ctr_nl(void)      { KL_CTR_NL(1, buf, 16); }
#endif

/* Run fn in U-mode: the cause of the one trap it takes, 0 if none. */
static uint64_t u_trap(void (*fn)(void))
{
    uint64_t n = trap_count;

    run_in_u(fn);
    return trap_count - n == 1 ? 0 : trap_count - n == 2 ? trap_prev_cause
                                                         : 0xff;
}

/* Make K3 an Encrypt locker with zv_k128, from M-mode. */
static void status_k3(void)
{
    KL_SETST(3, 0);
    PROVISION_LOAD(3, mdh_lo(0x000, 1, 0, 0), 0, zv_k128, 16);
    KL_SETST(3, ST_ENCRYPT);
}

static void test_status(void)
{
    uint64_t m, s;

    puts_("status\n");
    KL_CLEARALL();
    MLS_W(LS_ALL_INITIAL);
    SLS_W(LS_ALL_INITIAL);

    /* M-mode changes write no field. */
    status_k3();
    check("M-mode provisioning: fields stay Initial", MLS() & SLS(),
          LS_ALL_INITIAL);
    set_kls(2);
    MLS_W(LS_ALL_INITIAL);
    check("a write of mllockerstatus sets KLS Dirty",
          (csr_read(mstatus) >> 25) & 3, 3);
    set_kls(2);
    SLS_W(LS_ALL_INITIAL);
    check("a write of sllockerstatus sets KLS Dirty",
          (csr_read(mstatus) >> 25) & 3, 3);
    check("sllockerstatus from U-mode -> illegal", u_trap(u_sls),
          CAUSE_ILLEGAL);

    /* U-mode: a use that changes nothing leaves the fields alone. */
    memset(buf, 0, 16);
    check("U-mode ECB on an Initial locker", u_trap(u_ecb_k3), 0);
    check("  correct", memeq(buf, ct128, 16), 1);
    check("  ECB kl.exec leaves the fields", ls(MLS(), 3) | ls(SLS(), 3) << 2,
          LS_INITIAL | LS_INITIAL << 2);
    MLS_W(ls_set(LS_ALL_INITIAL, 3, LS_CLEAN));
    SLS_W(ls_set(LS_ALL_INITIAL, 3, LS_CLEAN));
    check("U-mode kl.getmd on a Clean locker", u_trap(u_getmd_k3), 0);
    check("  leaves it Clean", ls(MLS(), 3) | ls(SLS(), 3) << 2,
          LS_CLEAN | LS_CLEAN << 2);
    check("U-mode usage kl.setst", u_trap(u_enc_k3), 0);
    m = MLS();
    s = SLS();
    check("  makes both fields Dirty", ls(m, 3) | ls(s, 3) << 2,
          LS_DIRTY | LS_DIRTY << 2);
    check("  and no other", ls_set(m, 3, LS_INITIAL) & ls_set(s, 3, LS_INITIAL),
          LS_ALL_INITIAL);

    /* Off in mllockerstatus, then in sllockerstatus alone. */
    MLS_W(ls_set(LS_ALL_INITIAL, 3, LS_OFF));
    SLS_W(LS_ALL_INITIAL);
    memset(buf, 0, 16);
    check("U-mode kl.exec on an mllockerstatus-Off locker -> locker-Off",
          u_trap(u_ecb_k3), CAUSE_LOCKER_OFF);
    check("  no output", memeq(buf, ct128, 16), 0);
    check("  field stays Off", ls(MLS(), 3), LS_OFF);
    KL_ECB(3, 1, pt1, buf, 16);
    check("M-mode is not gated by mllockerstatus",
          memeq(buf, ct128, 16), 1);
    MLS_W(LS_ALL_INITIAL);
    SLS_W(ls_set(LS_ALL_INITIAL, 3, LS_OFF));
    check("U-mode kl.exec on an sllockerstatus-Off locker -> locker-Off",
          u_trap(u_ecb_k3), CAUSE_LOCKER_OFF);
    check("U-mode kl.getmd -> locker-Off", u_trap(u_getmd_k3),
          CAUSE_LOCKER_OFF);
    check("U-mode Error-State kl.setst -> locker-Off", u_trap(u_invalid_k3),
          CAUSE_LOCKER_OFF);
    KL_SETNLI(5);
    check("U-mode export opening -> locker-Off, before GR11",
          u_trap(u_export_k3), CAUSE_LOCKER_OFF);
    KL_SETNLI(3);
    check("U-mode kl.getmd KLNL -> locker-Off", u_trap(u_getmd_nl),
          CAUSE_LOCKER_OFF);
    check("U-mode kl.size KLNL -> locker-Off", u_trap(u_size_nl),
          CAUSE_LOCKER_OFF);
    check("U-mode kl.exec KLNL -> locker-Off", u_trap(u_ecb_nl),
          CAUSE_LOCKER_OFF);
    check("U-mode kl.load on it -> locker-Off", u_trap(u_load_nl),
          CAUSE_LOCKER_OFF);
    check("U-mode kl.load with Xl != 0 -> locker-Off, before Xl",
          u_trap(u_load_xl_nl), CAUSE_LOCKER_OFF);
    check("  K3 untouched", KL_GETST(3), ST_ENCRYPT);
    check("  klnamedlocker untouched", csr_read(0x801), 3);
    /* The gate follows klnamedlocker, not the locker field (X0, K0). */
    SLS_W(ls_set(LS_ALL_INITIAL, 0, LS_OFF));
    cpy(buf, pt1, 16);
    check("U-mode kl.exec KLNL = 3, K0 Off: no exception", u_trap(u_ecb_nl),
          0);
    check("  encrypts with K3", memeq(buf, ct128, 16), 1);
    SLS_W(ls_set(LS_ALL_INITIAL, 3, LS_OFF));
    KL_SETNLI(32);
    u_val = 1;
    check("U-mode kl.getmd KLNL without a named locker", u_trap(u_getmd_nl),
          0);
    check("  reads zeros", u_val, 0);
    check("  fields untouched", ls(MLS(), 3) | ls(SLS(), 3) << 2,
          LS_INITIAL | LS_OFF << 2);

    /* Destructive configuration instructions are exempt and make it Dirty. */
    check("U-mode kl.clear of an Off locker", u_trap(u_clear_k3), 0);
    check("  cleared", KL_GETST(3), 0);
    check("  both fields Dirty", ls(MLS(), 3) | ls(SLS(), 3) << 2,
          LS_DIRTY | LS_DIRTY << 2);
    MLS_W(ls_set(LS_ALL_INITIAL, 3, LS_OFF));
    SLS_W(ls_set(LS_ALL_INITIAL, 3, LS_OFF));
    set_kls(2);
    check("U-mode kl.clear of an Unconfigured Off locker", u_trap(u_clear_k3),
          0);
    check("  both fields Dirty", ls(MLS(), 3) | ls(SLS(), 3) << 2,
          LS_DIRTY | LS_DIRTY << 2);
    check("  and KLS Dirty", (csr_read(mstatus) >> 25) & 3, 3);
    MLS_W(ls_set(LS_ALL_INITIAL, 4, LS_OFF));
    SLS_W(ls_set(LS_ALL_INITIAL, 4, LS_OFF));
    check("U-mode provisioning of an Off locker", u_trap(u_prov_k4), 0);
    check("  provisioned", KL_GETST(4), ST_READY);
    check("  both fields Dirty", ls(MLS(), 4) | ls(SLS(), 4) << 2,
          LS_DIRTY | LS_DIRTY << 2);
    status_k3();
    MLS_W(ls_set(LS_ALL_INITIAL, 3, LS_OFF));
    SLS_W(ls_set(LS_ALL_INITIAL, 4, LS_OFF));
    check("U-mode kl.clearall with Off lockers", u_trap(u_clearall), 0);
    check("  clears them", KL_GETST(3) | KL_GETST(4), 0);
    check("  every field Dirty", MLS() & SLS(), ~0ull);

#ifndef ZKL_NO_CTR
    /* A keystream kl.exec changes the locker. */
    CTR_FRESH(5);
    KL_SETST_C(5, ST_OPERATE, zv_ctr_icb, 16);
    MLS_W(ls_set(LS_ALL_INITIAL, 5, LS_CLEAN));
    SLS_W(ls_set(LS_ALL_INITIAL, 5, LS_CLEAN));
    check("U-mode CTR kl.exec on a Clean locker", u_trap(u_ctr_k5), 0);
    check("  makes both fields Dirty", ls(MLS(), 5) | ls(SLS(), 5) << 2,
          LS_DIRTY | LS_DIRTY << 2);
    MLS_W(ls_set(LS_ALL_INITIAL, 5, LS_CLEAN));
    SLS_W(ls_set(LS_ALL_INITIAL, 5, LS_CLEAN));
    set_kls(2);
    KL_SETNLI(5);
    check("U-mode CTR kl.exec on KLNL, a Clean locker", u_trap(u_ctr_nl), 0);
    check("  makes both fields Dirty", ls(MLS(), 5) | ls(SLS(), 5) << 2,
          LS_DIRTY | LS_DIRTY << 2);
    check("  and KLS", (csr_read(mstatus) >> 25) & 3, 3);
    KL_SETNLI(32);
#endif

    KL_CLEARALL();
    MLS_W(LS_ALL_INITIAL);
    SLS_W(LS_ALL_INITIAL);
}

int main(void)
{
    test_gates();
#ifdef ZKL_NO_CTR
    test_no_ctr();
#endif
    test_ecb();
    test_scc();
    test_klnl();
    test_nested();
    test_priv();
#ifndef ZKL_NO_CTR
    test_ctr();
#endif
#ifndef ZKL_NO_GCM
    test_gcm();
#else
    test_no_gcm();
#endif
    test_status();

    puts_("checks: ");
    puthex(checks);
    puts_(failures ? "\ntest-zkl: FAILED\n" : "\ntest-zkl: PASS\n");
    return failures != 0;
}
