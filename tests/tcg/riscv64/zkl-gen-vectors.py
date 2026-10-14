#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Generate zkl-vectors.h for test-zkl.c from the Zkl specification's own
executable models (src/kat/common.py, src/kat/scc-kat.py, src/kat/ctr-kat.py
and src/kat/gcm-kat.py of riscv-high-assurance-cryptography), so that the
SCC bytes, CTR keystreams and GCM results produced by QEMU are checked
against an independent implementation of <<KLE-SCC-AEAD>>,
<<KLE-keystream-modes>> and <<KLE-GCM-mode>>.

Usage: zkl-gen-vectors.py SPEC_REPO > zkl-vectors.h
"""
import contextlib
import importlib.util
import os
import sys

kat = os.path.join(sys.argv[1], 'src', 'kat')
sys.path.insert(0, kat)


def load(name):
    """Import a src/kat model; it runs its own KAT suite and exits with its verdict."""
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'),
                                                  os.path.join(kat, name + '.py'))
    mod = importlib.util.module_from_spec(spec)
    with open(os.devnull, 'w') as devnull, contextlib.redirect_stdout(devnull):
        try:
            spec.loader.exec_module(mod)
        except SystemExit as e:
            if e.code:
                sys.exit(f'{name}.py self-test failed')
    return mod


scc = load('scc-kat')
ctr = load('ctr-kat')
gcm = load('gcm-kat')
from common import b2v, v2b, mdh_pack, aes_encrypt  # noqa: E402

CSK = bytes(range(0x20))
MLOC = bytes.fromhex('6d6c6f63616c6974792d7365637265')  + b'!'
SLOC = bytes.fromhex('736c6f63616c6974792d7365637265') + b'!'
CHIPFAM = b'QEMU-ZKL-CHIPFAM'      # QEMU's ChipFamScrt (zkl_helper.c)
K128 = bytes.fromhex('000102030405060708090a0b0c0d0e0f')
K256 = bytes.fromhex('000102030405060708090a0b0c0d0e0f'
                     '101112131415161718191a1b1c1d1e1f')


def seal(mdh, content, lst):
    content += bytes(-len(content) % 16)
    blocks = [b2v(content[i:i + 16]) for i in range(0, len(content), 16)]
    ad = [mdh] + [b2v(x) for x in lst]
    siv, ct = scc.SCC_Encrypt(ad, 0, 0, blocks, b2v(CSK))
    ok, pt = scc.SCC_Decrypt(ad, 0, 0, siv, ct, b2v(CSK))
    assert ok and pt == blocks
    return v2b(mdh, 16) + v2b(siv, 16) + b''.join(v2b(c, 16) for c in ct)


# AES256_ECB, enc+dec, State Encrypt, Localities MLocality and SLocality.
mdh_a = mdh_pack(Machine=0x020, MachinePolicy=3, State=7,
                 Locality=(1 << 6) | (1 << 8))
scc_a = seal(mdh_a, K256, [MLOC, SLOC])        # LST entries 8 then 10
# AES128_ECB, enc only, State Ready, bound to ChipFamScrt.
mdh_b = mdh_pack(Machine=0x000, MachinePolicy=1, State=1, Locality=2)
scc_b = seal(mdh_b, K128, [CHIPFAM])

assert aes_encrypt(K256, bytes.fromhex('00112233445566778899aabbccddeeff')).hex() \
    == '8ea2b7ca516745bfeafc49904b496089'

# CTR: SP 800-38A F.5.1/F.5.3/F.5.5, as ctr-kat.py checks them.
CTR_K = {len(bytes.fromhex(k)): bytes.fromhex(k) for _, k, _ in ctr.SP38A_F5}
CTR_CT = {len(bytes.fromhex(k)): bytes.fromhex(c) for _, k, c in ctr.SP38A_F5}
ICB = ctr.SP38A_ICB


def ctr_locker(key, iv=None, ctr0=None, blocks=0):
    """A model locker: provisioned, then Form C IV, Form B ctr, kl.exec."""
    cl = ctr.KsLocker()
    cl.provision(ctr.build_pi(f'AES-{8 * len(key)}', b2v(key)))
    ctr.operate(cl, None if iv is None else b2v(iv), ctr0)
    return cl, ctr.keystream(cl, 16 * blocks) if blocks else b''


for n, key in CTR_K.items():
    _, ks = ctr_locker(key, ICB, int.from_bytes(ICB[12:], 'big'), 4)
    assert bytes(a ^ b for a, b in zip(ks, ctr.SP38A_PT)) == CTR_CT[n]



def ref_ctr(key, nonce, ctr0, msg):
    """SP 800-38A CTR with nonce(96) || BE32(ctr), the counter wrapping.

    ctr-kat.py's own ref_ctr calls its module-level ref, which the module
    rebinds to a KsLocker when it runs its tests (9e4dc5b0ebfc), so it
    cannot be called after the import.
    """
    ks = b''.join(aes_encrypt(key, nonce + ((ctr0 + i) % 2**32).to_bytes(
        4, 'big')) for i in range(-(-len(msg) // 16)))
    return bytes(a ^ b for a, b in zip(ks, msg))


# The counter wraps silently under one IV.
WRAP_IV = bytes(range(1, 13)) + bytes(4)
_, wrap_ks = ctr_locker(CTR_K[16], WRAP_IV, 0xfffffffe, 4)
assert wrap_ks == ref_ctr(CTR_K[16], WRAP_IV[:12], 0xfffffffe, bytes(64))

# AES128_CTR, enc only, in Operate after two blocks of F.5.1 (ctr-kat.py's
# Content1 check), bound to ChipFamScrt.
cl, _ = ctr_locker(CTR_K[16], ICB, int.from_bytes(ICB[12:], 'big'), 2)
assert cl.content1().hex().endswith('f0f1f2f3f4f5f6f7f8f9fafb' '01fffdfc')
mdh_c = mdh_pack(Machine=0x001, MachinePolicy=1, State=2, Locality=2)
scc_ctr128 = seal(mdh_c, cl.content1(), [CHIPFAM])
# AES192_CTR, enc+dec, in Ready with ctr set, MLocality and SLocality.
cl, _ = ctr_locker(CTR_K[24], None, 0x01020304)
mdh_d = mdh_pack(Machine=0x011, MachinePolicy=3, State=1,
                 Locality=(1 << 6) | (1 << 8))
scc_ctr192 = seal(mdh_d, cl.content1(), [MLOC, SLOC])
assert len(scc_ctr128) == 64 and len(scc_ctr192) == 80


# GCM: McGrew-Viega tc1-6 and 13-18 as gcm-kat.py checks them, and tc4's
# shape with an AES-192 key from its byte-string reference: (key, IV, AAD,
# plaintext, ciphertext, tag), each encrypted by the model locker too.
GCM_V = [tuple(map(bytes.fromhex, v[1:])) for v in gcm.VECTORS]
K192 = bytes(range(0x40, 0x58))
GCM_V.append((K192, gcm.IV, gcm.A, gcm.P) + gcm.ref_gcm(K192, gcm.IV, gcm.A, gcm.P))
for k_, iv_, a_, p_, c_, t_ in GCM_V:
    c, t, cl = gcm.kl_encrypt(k_, iv_, a_, p_)
    assert (c, t, cl.state) == (c_, t_, gcm.SUCC)


def gcm_scc(cl, state):
    """An AES256_GCM model locker sealed as QEMU exports it (ChipFamScrt)."""
    v, bits = cl.export()
    mdh = mdh_pack(Machine=0x024, MachinePolicy=3, State=state, Locality=2)
    return seal(mdh, v2b(v, bits // 8), [CHIPFAM])


# tc16's key (AES-256) in Ready; in Set_Aux_Value after 16 bytes of tc18's
# 60-byte IV; in Encrypt after tc16's IV, AAD and first block.
K256G, IV60, P60, A20 = gcm.SRC, gcm.IV60B, gcm.P, gcm.A
scc_gcm_ready = gcm_scc(gcm.Gcm.provisioned(K256G), gcm.READY)
cl = gcm.Gcm.provisioned(K256G)
cl.setst(gcm.SAV, 'B', 480)
gcm.feed(cl, IV60[:16])
scc_gcm_sav = gcm_scc(cl, gcm.SAV)
cl = gcm.Gcm.provisioned(K256G)
cl.setst(gcm.SAV, 'B', 96)
gcm.feed(cl, gcm.IV)
gcm.feed(cl, A20 + bytes(12))
cl.setst(gcm.ENC)
c1 = gcm.v2b(cl.exec('A', b2v(P60[:16]), 128), 16)
assert c1 == GCM_V[9][4][:16]          # tc16
scc_gcm_enc = gcm_scc(cl, gcm.ENC)
# The counter limit: in Encrypt with ctr ffffffff and start_ctr 1, the
# first block of three is processed, the second would reach start_ctr - 1.
cl.setst(gcm.READY)
cl.setst(gcm.SAV, 'B', 96)
gcm.feed(cl, gcm.IV)
cl.setst(gcm.ENC)
gcm.seed(cl, 0xfffffffe)
scc_gcm_lim = gcm_scc(cl, gcm.ENC)
gcm_lim_out = gcm.v2b(cl.exec('A', b2v(P60[:48]), 384), 48)
assert cl.state == gcm.INV and gcm_lim_out[16:] == bytes(32)
assert len(scc_gcm_ready) == 112 and len(scc_gcm_sav) == 112


def arr(name, b):
    body = ', '.join(f'0x{x:02x}' for x in b)
    return f'static const uint8_t {name}[{len(b)}] __attribute__((aligned(16))) = {{ {body} }};'


print('/* Generated by zkl-gen-vectors.py from the Zkl spec KAT models. */')
print('/* SPDX-License-Identifier: GPL-2.0-or-later */')
for name, b in (('zv_csk', CSK), ('zv_mloc', MLOC), ('zv_sloc', SLOC),
                ('zv_k128', K128), ('zv_k256', K256),
                ('zv_scc_a', scc_a), ('zv_scc_b', scc_b),
                ('zv_ctr_pt', ctr.SP38A_PT), ('zv_ctr_icb', ICB),
                ('zv_ctr_k128', CTR_K[16]), ('zv_ctr_ct128', CTR_CT[16]),
                ('zv_ctr_k192', CTR_K[24]), ('zv_ctr_ct192', CTR_CT[24]),
                ('zv_ctr_k256', CTR_K[32]), ('zv_ctr_ct256', CTR_CT[32]),
                ('zv_ctr_wrap_iv', WRAP_IV), ('zv_ctr_wrap_ks', wrap_ks),
                ('zv_scc_ctr128', scc_ctr128), ('zv_scc_ctr192', scc_ctr192),
                ('zv_scc_gcm_ready', scc_gcm_ready), ('zv_scc_gcm_sav', scc_gcm_sav),
                ('zv_scc_gcm_enc', scc_gcm_enc), ('zv_scc_gcm_lim', scc_gcm_lim),
                ('zv_gcm_lim_out', gcm_lim_out), ('zv_gcm_p60', P60)):
    print(arr(name, b))

# The GCM vectors as a table; an empty field gets a one-byte array.
rows = []
for i, v in enumerate(GCM_V):
    names = []
    for f, b in zip(('k', 'iv', 'a', 'p', 'c', 't'), v):
        print(arr(f'zv_gcm{i}_{f}', b or bytes(1)))
        names.append(f'zv_gcm{i}_{f}')
    rows.append('    { ' + ', '.join(names) + ', ' +
                ', '.join(str(len(b)) for b in v[:4]) + ' },')
print('static const struct zv_gcm {')
print('    const uint8_t *k, *iv, *a, *p, *c, *t;')
print('    uint32_t klen, ivlen, alen, plen;')
print('} zv_gcm[] = {')
print('\n'.join(rows))
print('};')
