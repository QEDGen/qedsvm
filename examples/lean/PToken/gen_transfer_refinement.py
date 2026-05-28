#!/usr/bin/env python3
# Codegen prototype: emit the transfer refinement wiring from the lift's atoms.
# (This logic is what qedlift will emit per-arm.)

SRC = 96      # src account base offset (from baseAddr): debit cell at +160 → base 96
DST = 10600   # dst account base offset: credit cell at +10664 → base 10600

# (kind, addr_base, off, value)  — kind: 'r'<n> for reg, 'm' for mem.
# pre atoms (balance_correct pre)
pre = [
 ('r1','baseAddr'), ('m','baseAddr',0,'B','oldMemB_0'), ('r2','vR2Old'),
 ('m','baseAddr',88,'D','oldMemD_1'), ('m','baseAddr',10512,'B','oldMemB_2'),
 ('m','baseAddr',10592,'D','oldMemD_3'), ('m','baseAddr',21016,'B','oldMemB_4'),
 ('m','baseAddr',21096,'D','oldMemD_5'), ('r4','vR4Old'), ('r3','vR3Old'),
 ('m','addr0',31352,'D','oldMemD_6'), ('m','addr0',31360,'B','oldMemB_7'),
 ('r6','vR6Old'), ('r7','vR7Old'), ('m','baseAddr',204,'B','oldMemB_8'),
 ('m','baseAddr',10708,'B','oldMemB_9'), ('r5','vR5Old'),
 ('m','addr0',31361,'D','oldMemD_10'), ('m','baseAddr',160,'D','oldMemD_11'),
 ('m','baseAddr',10600,'D','oldMemD_12'), ('m','baseAddr',96,'D','oldMemD_13'),
 ('r0','vR0Old'), ('m','baseAddr',10608,'D','oldMemD_14'),
 ('m','baseAddr',104,'D','oldMemD_15'), ('m','baseAddr',10616,'D','oldMemD_16'),
 ('m','baseAddr',112,'D','oldMemD_17'), ('m','baseAddr',10624,'D','oldMemD_18'),
 ('m','baseAddr',120,'D','oldMemD_19'), ('m','baseAddr',21024,'D','oldMemD_20'),
 ('m','baseAddr',168,'B','oldMemB_21'), ('m','baseAddr',128,'D','oldMemD_22'),
 ('m','baseAddr',21032,'D','oldMemD_23'), ('m','baseAddr',136,'D','oldMemD_24'),
 ('m','baseAddr',21040,'D','oldMemD_25'), ('m','baseAddr',144,'D','oldMemD_26'),
 ('m','baseAddr',21048,'D','oldMemD_27'), ('m','baseAddr',152,'D','oldMemD_28'),
 ('m','baseAddr',21017,'B','oldMemB_29'), ('m','baseAddr',10664,'D','oldMemD_30'),
 ('m','baseAddr',205,'B','oldMemB_31'),
]
# post: reg/value changes; balance cells clean.
post_reg = {'r1':'baseAddr','r2':'oldMemD_10','r3':'oldMemB_31 % 256','r4':'oldMemB_29 % 256',
            'r5':'oldMemD_27','r6':'toU64 0','r7':'toU64 4','r0':'toU64 0'}
post_mem = {  # (base,off) -> value override; default unchanged
 ('baseAddr',160):'oldMemD_11 - oldMemD_10', ('baseAddr',10664):'oldMemD_30 + oldMemD_10'}

def atom(a, post=False):
    if a[0].startswith('r'):
        v = post_reg[a[0]] if post else a[1]
        return f"(.{a[0]} ↦ᵣ {v})"
    _, base, off, w, val = a
    if post: val = post_mem.get((base,off), val)
    arrow = '↦ₘ' if w=='B' else '↦U64'
    return f"(effectiveAddr {base} {off} {arrow} {val})"

def chain(atoms, post=False):
    return " **\n      ".join(atom(a, post) for a in atoms)

# classify mem atoms into src-field / dst-field / other
def classify(a):
    if a[0].startswith('r'): return 'other'
    _, base, off, w, val = a
    if base=='baseAddr' and SRC <= off < SRC+165: return 'src'
    if base=='baseAddr' and DST <= off < DST+165: return 'dst'
    return 'other'

others = [a for a in pre if classify(a)=='other']
print("setupPre count:", len(others))
# value vars
nat_vars = "baseAddr addr0 oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 oldMemB_4 oldMemD_5 vR4Old vR3Old oldMemD_6 oldMemB_7 vR6Old vR7Old oldMemB_8 oldMemB_9 vR5Old oldMemD_10 oldMemD_11 oldMemD_12 oldMemD_13 vR0Old oldMemD_14 oldMemD_15 oldMemD_16 oldMemD_17 oldMemD_18 oldMemD_19 oldMemD_20 oldMemB_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 oldMemD_26 oldMemD_27 oldMemD_28 oldMemB_29 oldMemD_30 oldMemB_31"

liftPre = chain(pre, False)
liftPost = chain(pre, True)
setupPre = chain(others, False)
setupPost = chain(others, True)

out = f"""\
import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Refinement
import Generated.PTokenTransferTracedLifted
import PToken.TransferAggregation

namespace Examples.PTokenTransferRefinement
open SVM SVM.SBPF SVM.Solana SVM.Solana.Abstract
open Examples.PTokenTransferAggregation

-- Generic wiring: any lift with the transfer happy-path shape refines
-- the tokenTransfer intrinsic's asm obligation. cr/rr/lift abstract.
set_option maxHeartbeats 4000000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_vars} : Nat)
    (o0 o1 o2 o3 : Nat) (g1 g2 g3 g4 : ByteArray)
    (hg1 : g1.size = 35) (hg3 : g3.size = 36)
    (h72 : oldMemB_21 < 256) (h108s : oldMemB_8 < 256)
    (h109s : oldMemB_31 < 256) (h108d : oldMemB_9 < 256)
    (lift : cuTripleWithinMem 75 0 198 3542 cr
      ({liftPre})
      ({liftPost}) rr) :
    AsmRefinesTokenTransfer cr 75 0 198 3542 rr (baseAddr + 96) (baseAddr + 10600)
      {{ mint := ⟨oldMemD_13, oldMemD_15, oldMemD_17, oldMemD_19⟩,
        owner := ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_28⟩, amount := oldMemD_11,
        rest := PartialState.byteBA oldMemB_21 ++ (g1 ++
          (PartialState.byteBA oldMemB_8 ++ (PartialState.byteBA oldMemB_31 ++ g2))) }}
      {{ mint := ⟨oldMemD_12, oldMemD_14, oldMemD_16, oldMemD_18⟩,
        owner := ⟨o0, o1, o2, o3⟩, amount := oldMemD_30,
        rest := g3 ++ (PartialState.byteBA oldMemB_9 ++ g4) }}
      oldMemD_10
      ({setupPre})
      ({setupPost}) := by
  unfold AsmRefinesTokenTransfer
  simp only [TokenAccount.withAmount, TokenAccount.amount]
  rw [src_account_eq (baseAddr + 96) oldMemD_13 oldMemD_15 oldMemD_17 oldMemD_19
        oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_28 oldMemD_11 oldMemB_21 oldMemB_8 oldMemB_31
        g1 g2 hg1 h72 h108s h109s,
      dst_account_eq (baseAddr + 10600) oldMemD_12 oldMemD_14 oldMemD_16 oldMemD_18
        o0 o1 o2 o3 oldMemD_30 oldMemB_9 g3 g4 hg3 h108d,
      src_account_eq (baseAddr + 96) oldMemD_13 oldMemD_15 oldMemD_17 oldMemD_19
        oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_28 (oldMemD_11 - oldMemD_10) oldMemB_21 oldMemB_8 oldMemB_31
        g1 g2 hg1 h72 h108s h109s,
      dst_account_eq (baseAddr + 10600) oldMemD_12 oldMemD_14 oldMemD_16 oldMemD_18
        o0 o1 o2 o3 (oldMemD_30 + oldMemD_10) oldMemB_9 g3 g4 hg3 h108d]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( (effectiveAddr baseAddr 10632 ↦U64 o0) ** (effectiveAddr baseAddr 10640 ↦U64 o1) **
      (effectiveAddr baseAddr 10648 ↦U64 o2) ** (effectiveAddr baseAddr 10656 ↦U64 o3) **
      memBytesIs (baseAddr + 169) g1 ** memBytesIs (baseAddr + 206) g2 **
      memBytesIs (baseAddr + 10672) g3 ** memBytesIs (baseAddr + 10709) g4 )
    (by sl_pcfree) lift
  sl_exact framed

end Examples.PTokenTransferRefinement
"""
open('/Users/abishek/code/qedsvm/examples/lean/PToken/TransferRefinement.lean','w').write(out)
print("wrote TransferRefinement.lean")
