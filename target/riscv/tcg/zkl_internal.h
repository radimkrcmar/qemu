/*
 * RISC-V Zkl (KLE) helpers shared by the TCG files.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

#ifndef RISCV_TCG_ZKL_INTERNAL_H
#define RISCV_TCG_ZKL_INTERNAL_H

#include "cpu.h"

/* mstatus.KLS (and, when V=1, vsstatus.KLS, not implemented) is Off. */
static inline bool zkl_kls_off(CPURISCVState *env)
{
    return get_field(env->mstatus, MSTATUS_KLS) == EXT_STATUS_DISABLED;
}

/* A CSK is established and the mklcsk group is not partially written. */
static inline bool zkl_csk_ready(CPURISCVState *env)
{
    return env->kle.csk_active && !env->kle.csk_written;
}

static inline void zkl_mark_dirty(CPURISCVState *env)
{
    env->mstatus |= MSTATUS_KLS;
}

#endif
