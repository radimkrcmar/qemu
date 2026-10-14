/*
 * RISC-V translation routines for the Zkl (KLE) extension.
 *
 * All semantics, including the encoding checks, are in zkl_helper.c.  The
 * helpers may change mstatus.KLS/VS, so the TB ends after each instruction.
 *
 * SPDX-License-Identifier: GPL-2.0-or-later
 */

static bool gen_zkl(DisasContext *ctx,
                    void (*gen)(TCGv_env, TCGv_i32))
{
    if (!ctx->cfg_ptr->ext_zkl || get_xl(ctx) != MXL_RV64) {
        return false;
    }
    decode_save_opc(ctx, 0);
    gen(tcg_env, tcg_constant_i32(ctx->opcode));
    gen_update_pc(ctx, ctx->cur_insn_len);
    exit_tb(ctx);
    ctx->base.is_jmp = DISAS_NORETURN;
    return true;
}

static bool trans_kl_exec_grp(DisasContext *ctx, arg_kl_exec_grp *a)
{
    return gen_zkl(ctx, gen_helper_kl_exec_grp);
}

static bool trans_kl_setst(DisasContext *ctx, arg_kl_setst *a)
{
    return gen_zkl(ctx, gen_helper_kl_setst);
}

static bool trans_kl_load(DisasContext *ctx, arg_kl_load *a)
{
    return gen_zkl(ctx, gen_helper_kl_load);
}

static bool trans_kl_store(DisasContext *ctx, arg_kl_store *a)
{
    return gen_zkl(ctx, gen_helper_kl_store);
}
