#!/usr/bin/env python3
# Codegen prototype: emit the MintTo refinement wiring from the lift's atoms.
# MintTo refines the tokenMintTo intrinsic: mint.supply += amount and
# dest.amount += amount. Mint account at base addr5+88 (supply at +36 = addr5+124);
# dest token account at base addr4+88 (amount at +64 = addr4+152). Both bases are
# abstracted (alignment-rounded account pointers), carried as Nat params.

MINT_BASE = ('addr5', 88)   # mint account base
DEST_BASE = ('addr4', 88)   # dest token account base

# Mint-account cells the lift owns: addr5+off -> (mint-relative offset).
MINT_CELLS = {88: 0, 92: 4, 100: 12, 108: 20, 116: 28, 124: 36, 133: 45}
# Dest-account cells the lift owns: addr4+off -> dest-relative offset.
DEST_CELLS = {88: 0, 96: 8, 104: 16, 112: 24, 152: 64, 196: 108, 197: 109}

# Full pre atom list (balance-correct corollary form), transcribed from the lift.
# (reg, value) for registers; (m, base, off, width, val) for memory.
pre = [
 ('r1','baseAddr'), ('m','baseAddr',0,'B','oldMemB_0'), ('r2','vR2Old'),
 ('m','baseAddr',88,'D','oldMemD_1'), ('r0','vR0Old'), ('m','baseAddr',0,'D','oldMemD_2'),
 ('r7','vR7Old'), ('r10','vR10Old'), ('m','vR10Old',-2072,'D','oldMemD_3'),
 ('r3','vR3Old'), ('m','addr0',0,'B','oldMemB_4'), ('m','addr1',8,'D','oldMemD_5'),
 ('m','addr0',80,'D','oldMemD_6'), ('m','addr2',0,'B','oldMemB_7'),
 ('m','addr1',16,'D','oldMemD_8'), ('m','addr2',80,'D','oldMemD_9'), ('r4','vR4Old'),
 ('m','addr3',0,'D','oldMemD_10'), ('r9','vR9Old'), ('m','addr3',8,'B','oldMemB_11'),
 ('r5','vR5Old'), ('r8','vR8Old'), ('r6','vR6Old'), ('m','vR10Old',-2064,'D','addr4'),
 ('m','addr4',80,'D','oldMemD_13'), ('m','addr4',196,'B','oldMemB_14'),
 ('m','addr4',197,'B','oldMemB_15'), ('m','addr4',88,'D','oldMemD_16'),
 ('m','addr5',8,'D','oldMemD_17'), ('m','addr4',96,'D','oldMemD_18'),
 ('m','addr5',16,'D','oldMemD_19'), ('m','addr4',104,'D','oldMemD_20'),
 ('m','addr5',24,'D','oldMemD_21'), ('m','addr4',112,'D','oldMemD_22'),
 ('m','addr5',32,'D','oldMemD_23'), ('m','addr5',80,'D','oldMemD_24'),
 ('m','addr5',133,'B','oldMemB_25'), ('m','addr5',88,'B','oldMemB_26'),
 ('m','vR10Old',-2056,'D','addr6'), ('m','addr6',8,'D','oldMemD_28'),
 ('m','addr5',92,'D','oldMemD_29'), ('m','addr6',16,'D','oldMemD_30'),
 ('m','addr5',100,'D','oldMemD_31'), ('m','addr6',24,'D','oldMemD_32'),
 ('m','addr5',108,'D','oldMemD_33'), ('m','addr6',32,'D','oldMemD_34'),
 ('m','addr5',116,'D','oldMemD_35'), ('m','addr7',0,'D','oldMemD_36'),
 ('m','addr6',80,'D','oldMemD_37'), ('m','addr6',1,'B','oldMemB_38'),
 ('m','addr5',124,'D','oldMemD_39'), ('m','addr4',152,'D','oldMemD_40'),
]
post_reg = {'r1':'wrapAdd oldMemD_40 oldMemD_36',
            'r2':'((toU64 0) &&& toU64 1) % U64_MODULUS', 'r0':'toU64 0', 'r7':'addr5',
            'r3':'addr4', 'r4':'oldMemD_36', 'r9':'toU64 4', 'r5':'oldMemD_39',
            'r8':'addr7', 'r6':'toU64 0'}
post_mem = {  # value changes pre->post (the lift's raw scattered form carries ALL
              # of them, including the account supply/amount the codec re-views).
 ('vR10Old',-2072):'addr5', ('addr1',8):'addr0', ('addr1',16):'addr2',
 ('addr5',124):'oldMemD_39 + oldMemD_36', ('addr4',152):'oldMemD_40 + oldMemD_36'}

def lean_off(off):
    return f"({off})" if off < 0 else f"{off}"

def atom(a, post=False):
    if a[0][0] == 'r' and a[0] != 'm':
        v = post_reg.get(a[0], a[1]) if post else a[1]
        return f"(.{a[0]} ↦ᵣ {v})"
    _, base, off, w, val = a
    if post: val = post_mem.get((base,off), val)
    arrow = '↦ₘ' if w == 'B' else '↦U64'
    return f"(effectiveAddr {base} {lean_off(off)} {arrow} {val})"

def chain(atoms, post=False):
    return " **\n      ".join(atom(a, post) for a in atoms)

def classify(a):
    if a[0][0] == 'r' and a[0] != 'm': return 'other'
    _, base, off, w, val = a
    if base == MINT_BASE[0] and off in MINT_CELLS: return 'mint'
    if base == DEST_BASE[0] and off in DEST_CELLS: return 'dest'
    return 'other'

others = [a for a in pre if classify(a) == 'other']
print("setupPre count:", len(others))

nat_vars = ("baseAddr oldMemB_0 vR2Old oldMemD_1 vR0Old oldMemD_2 vR7Old vR10Old oldMemD_3 "
 "vR3Old oldMemB_4 oldMemD_5 oldMemD_6 oldMemB_7 oldMemD_8 oldMemD_9 vR4Old oldMemD_10 "
 "vR9Old oldMemB_11 vR5Old vR8Old vR6Old oldMemD_13 oldMemB_14 oldMemB_15 oldMemD_16 "
 "oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 "
 "oldMemB_25 oldMemB_26 oldMemD_28 oldMemD_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 "
 "oldMemD_34 oldMemD_35 oldMemD_36 oldMemD_37 oldMemB_38 oldMemD_39 oldMemD_40 "
 "addr0 addr1 addr2 addr3 addr4 addr5 addr6 addr7")

liftPre = chain(pre, False)
liftPost = chain(pre, True)
setupPre = chain(others, False)
setupPost = chain(others, True)

# Mint record: preAuth = tag byte + 3B gap + 4 pubkey dwords; rest = 1B gap + is_init byte + 36B gap.
MINT_REC = ("{ preAuth := PartialState.byteBA oldMemB_26 ++ (gA ++\n"
 "          (PartialState.u64LE oldMemD_29 ++ (PartialState.u64LE oldMemD_31 ++\n"
 "            (PartialState.u64LE oldMemD_33 ++ PartialState.u64LE oldMemD_35)))),\n"
 "        supply := oldMemD_39,\n"
 "        rest := gD ++ (PartialState.byteBA oldMemB_25 ++ gF) }")
# Dest token record: mint dwords, owner framed, amount, rest owns bytes 108/109.
DEST_REC = ("{ mint := ⟨oldMemD_16, oldMemD_18, oldMemD_20, oldMemD_22⟩,\n"
 "        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_40,\n"
 "        rest := g3 ++ (PartialState.byteBA oldMemB_14 ++ (PartialState.byteBA oldMemB_15 ++ g4)) }")

# aggregation rw argument tails
MINT_ARGS = "oldMemB_26 oldMemD_29 oldMemD_31 oldMemD_33 oldMemD_35"
DEST_ARGS = "oldMemD_16 oldMemD_18 oldMemD_20 oldMemD_22 o0 o1 o2 o3"

out = f"""\
/-
  MintTo asm-refines-intrinsic theorem — refines the `tokenMintTo` intrinsic
  (mint.supply += amount, dest.amount += amount). Generated by
  `gen_mintto_refinement.py`. The mint account sits at base `addr5 + 88`
  (supply at +36) and the dest token account at `addr4 + 88` (amount at +64);
  both bases are abstracted account pointers. Uses `mint_account_eq` (supply
  codec) + `dest_account_eq` (token codec, rest owns bytes 108/109) from
  `MintAggregation`. The decimals-gap / authority-gap / dst-owner cells the lift
  doesn't read are framed in. Same scoping note as the other refinements (no
  `open SVM.Solana.Abstract`; codec-fold `simp` before `sl_exact`).
-/

import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Refinement
import Generated.PTokenMintToTracedLifted
import PToken.MintAggregation

namespace Examples.PTokenMintToRefinement
open SVM SVM.SBPF SVM.SBPF.Memory
open Examples.PTokenMintAggregation

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_vars} : Nat)
    (o0 o1 o2 o3 : Nat) (gA gD gF g3 g4 : ByteArray)
    (hgA : gA.size = 3) (hgD : gD.size = 1) (hg3 : g3.size = 36)
    (hb0 : oldMemB_26 < 256) (hb45 : oldMemB_25 < 256)
    (hb108 : oldMemB_14 < 256) (hb109 : oldMemB_15 < 256)
    (lift : cuTripleWithinMem 119 0 198 3542 cr
      ({liftPre})
      ({liftPost}) rr) :
    SVM.Solana.Abstract.AsmRefinesTokenMintTo cr 119 0 198 3542 rr (addr5 + 88) (addr4 + 88)
      {MINT_REC}
      {DEST_REC}
      oldMemD_36
      ({setupPre})
      ({setupPost}) := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenMintTo
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [mint_account_eq (addr5 + 88) {MINT_ARGS} oldMemD_39 oldMemB_25
        gA gD gF hgA hgD hb0 hb45,
      dest_account_eq (addr4 + 88) {DEST_ARGS} oldMemD_40 oldMemB_14 oldMemB_15
        g3 g4 hg3 hb108 hb109,
      mint_account_eq (addr5 + 88) {MINT_ARGS} (oldMemD_39 + oldMemD_36) oldMemB_25
        gA gD gF hgA hgD hb0 hb45,
      dest_account_eq (addr4 + 88) {DEST_ARGS} (oldMemD_40 + oldMemD_36) oldMemB_14 oldMemB_15
        g3 g4 hg3 hb108 hb109]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( memBytesIs (addr5 + 89) gA ** memBytesIs (addr5 + 132) gD ** memBytesIs (addr5 + 134) gF **
      (effectiveAddr addr4 120 ↦U64 o0) ** (effectiveAddr addr4 128 ↦U64 o1) **
      (effectiveAddr addr4 136 ↦U64 o2) ** (effectiveAddr addr4 144 ↦U64 o3) **
      memBytesIs (addr4 + 160) g3 ** memBytesIs (addr4 + 198) g4 )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

end Examples.PTokenMintToRefinement
"""
open('/Users/abishek/code/qedsvm/examples/lean/PToken/MintToRefinement.lean','w').write(out)
print("wrote MintToRefinement.lean")
