#!/usr/bin/env python3
# Codegen prototype: emit the Burn refinement wiring from the lift's atoms.
# Burn refines tokenBurn: account.amount -= amount, mint.supply -= amount.
# Account token acct at base addr4+88 (amount at +64 = addr4+152); mint at
# base addr5+88 (supply at +36 = addr5+124). The account owns owner + rest bytes
# 72/108/109 (Transfer's src pattern → src_account_eq); the mint reads only
# supply + is_init (preAuth fully framed → mint_supply_eq).

ACCT_BASE = ('addr4', 88)
MINT_BASE = ('addr5', 88)
# Account cells (src pattern): mint(0/8/16/24), owner(32/40/48/56), amount(64),
# rest bytes 72/108/109.
ACCT_CELLS = {88,96,104,112,120,128,136,144,152,160,196,197}
# Mint cells: supply (124 = +36), is_init byte (133 = +45).
MINT_CELLS = {124,133}

pre = [
 ('r1','baseAddr'), ('m','baseAddr',0,'B','oldMemB_0'), ('r2','vR2Old'),
 ('m','baseAddr',88,'D','oldMemD_1'), ('m','baseAddr',10512,'B','oldMemB_2'),
 ('m','baseAddr',10592,'D','oldMemD_3'), ('r0','vR0Old'), ('m','baseAddr',0,'D','oldMemD_4'),
 ('r7','vR7Old'), ('r10','vR10Old'), ('m','vR10Old',-2072,'D','oldMemD_5'),
 ('r3','vR3Old'), ('m','addr0',0,'B','oldMemB_6'), ('m','addr1',8,'D','oldMemD_7'),
 ('m','addr0',80,'D','oldMemD_8'), ('m','addr2',0,'B','oldMemB_9'),
 ('m','addr1',16,'D','oldMemD_10'), ('m','addr2',80,'D','oldMemD_11'), ('r4','vR4Old'),
 ('m','addr3',0,'D','oldMemD_12'), ('r9','vR9Old'), ('m','addr3',8,'B','oldMemB_13'),
 ('r5','vR5Old'), ('r8','vR8Old'), ('r6','vR6Old'), ('m','addr4',80,'D','oldMemD_14'),
 ('m','addr4',196,'B','oldMemB_15'), ('m','vR10Old',-2064,'D','addr5'),
 ('m','addr5',80,'D','oldMemD_17'), ('m','addr5',133,'B','oldMemB_18'),
 ('m','addr4',197,'B','oldMemB_19'), ('m','addr6',0,'D','oldMemD_20'),
 ('m','addr4',152,'D','oldMemD_21'), ('m','addr4',88,'D','oldMemD_22'),
 ('m','addr5',8,'D','oldMemD_23'), ('m','addr4',96,'D','oldMemD_24'),
 ('m','addr5',16,'D','oldMemD_25'), ('m','addr4',104,'D','oldMemD_26'),
 ('m','addr5',24,'D','oldMemD_27'), ('m','vR10Old',-2096,'D','oldMemD_28'),
 ('m','addr4',112,'D','oldMemD_29'), ('m','addr5',32,'D','oldMemD_30'),
 ('m','addr4',120,'D','oldMemD_31'), ('m','vR10Old',-2088,'D','oldMemD_32'),
 ('m','vR10Old',-2104,'D','oldMemD_33'), ('m','vR10Old',-2056,'D','addr7'),
 ('m','addr4',160,'B','oldMemB_35'), ('m','addr7',8,'D','oldMemD_36'),
 ('m','addr7',16,'D','oldMemD_37'), ('m','addr4',128,'D','oldMemD_38'),
 ('m','addr7',24,'D','oldMemD_39'), ('m','addr4',136,'D','oldMemD_40'),
 ('m','addr7',32,'D','oldMemD_41'), ('m','addr4',144,'D','oldMemD_42'),
 ('m','addr7',80,'D','oldMemD_43'), ('m','addr7',1,'B','oldMemB_44'),
 ('m','addr5',124,'D','oldMemD_45'),
]
post_reg = {'r1':'wrapSub oldMemD_45 oldMemD_20', 'r2':'oldMemD_42', 'r0':'toU64 0',
            'r7':'oldMemD_4', 'r3':'addr5', 'r4':'addr4', 'r9':'toU64 4',
            'r5':'oldMemD_20', 'r8':'addr6', 'r6':'toU64 0'}
post_mem = {
 ('vR10Old',-2072):'addr4', ('addr1',8):'addr0', ('addr1',16):'addr2',
 ('vR10Old',-2096):'oldMemD_21', ('vR10Old',-2088):'oldMemD_20',
 ('vR10Old',-2104):'wrapAdd vR10Old (toU64 (-2048))',
 ('addr4',152):'oldMemD_21 - oldMemD_20', ('addr5',124):'oldMemD_45 - oldMemD_20'}

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
    if base == ACCT_BASE[0] and off in ACCT_CELLS: return 'acct'
    if base == MINT_BASE[0] and off in MINT_CELLS: return 'mint'
    return 'other'

others = [a for a in pre if classify(a) == 'other']
print("setupPre count:", len(others))

nat_vars = ("baseAddr oldMemB_0 vR2Old oldMemD_1 oldMemB_2 oldMemD_3 vR0Old oldMemD_4 vR7Old "
 "vR10Old oldMemD_5 vR3Old oldMemB_6 oldMemD_7 oldMemD_8 oldMemB_9 oldMemD_10 oldMemD_11 "
 "vR4Old oldMemD_12 vR9Old oldMemB_13 vR5Old vR8Old vR6Old oldMemD_14 oldMemB_15 oldMemD_17 "
 "oldMemB_18 oldMemB_19 oldMemD_20 oldMemD_21 oldMemD_22 oldMemD_23 oldMemD_24 oldMemD_25 "
 "oldMemD_26 oldMemD_27 oldMemD_28 oldMemD_29 oldMemD_30 oldMemD_31 oldMemD_32 oldMemD_33 "
 "oldMemB_35 oldMemD_36 oldMemD_37 oldMemD_38 oldMemD_39 oldMemD_40 oldMemD_41 oldMemD_42 "
 "oldMemD_43 oldMemB_44 oldMemD_45 addr0 addr1 addr2 addr3 addr4 addr5 addr6 addr7")

liftPre = chain(pre, False)
liftPost = chain(pre, True)
setupPre = chain(others, False)
setupPost = chain(others, True)

# Account token record (src pattern): owner owned, rest owns bytes 72/108/109.
ACCT_REC = ("{ mint := ⟨oldMemD_22, oldMemD_24, oldMemD_26, oldMemD_29⟩,\n"
 "        owner := ⟨oldMemD_31, oldMemD_38, oldMemD_40, oldMemD_42⟩, amount := oldMemD_21,\n"
 "        rest := PartialState.byteBA oldMemB_35 ++ (g1 ++\n"
 "          (PartialState.byteBA oldMemB_15 ++ (PartialState.byteBA oldMemB_19 ++ g2))) }")
# Mint record: preAuth opaque (36B framed), is_init byte at +45.
MINT_REC = ("{ preAuth := preAuthBA, supply := oldMemD_45,\n"
 "        rest := gD ++ (PartialState.byteBA oldMemB_18 ++ gF) }")

ACCT_ARGS = "oldMemD_22 oldMemD_24 oldMemD_26 oldMemD_29 oldMemD_31 oldMemD_38 oldMemD_40 oldMemD_42"

out = f"""\
/-
  Burn asm-refines-intrinsic theorem — refines the `tokenBurn` intrinsic
  (account.amount -= amount, mint.supply -= amount). Generated by
  `gen_burn_refinement.py`. The source token account sits at base `addr4 + 88`
  (amount at +64) and reuses Transfer's `src_account_eq` (owner read + rest bytes
  72/108/109); the mint at base `addr5 + 88` (supply at +36) reads only supply +
  is_initialized, so its 36-byte authority blob is framed opaque
  (`mint_supply_eq`). Same scoping note as the other refinements.
-/

import SVM.SBPF.Tactic.SL
import SVM.Solana.Abstract.Refinement
import Generated.PTokenBurnTracedLifted
import PToken.TransferAggregation
import PToken.MintAggregation

namespace Examples.PTokenBurnRefinement
open SVM SVM.SBPF SVM.SBPF.Memory
open Examples.PTokenTransferAggregation Examples.PTokenMintAggregation

set_option maxHeartbeats 800000 in
theorem refines_asm
    (cr : CodeReq) (rr : Memory.RegionTable → Prop)
    ({nat_vars} : Nat)
    (g1 g2 gD gF preAuthBA : ByteArray)
    (hg1 : g1.size = 35) (hgD : gD.size = 1)
    (h72 : oldMemB_35 < 256) (h108 : oldMemB_15 < 256) (h109 : oldMemB_19 < 256)
    (hb45 : oldMemB_18 < 256)
    (lift : cuTripleWithinMem 130 0 198 3542 cr
      ({liftPre})
      ({liftPost}) rr) :
    SVM.Solana.Abstract.AsmRefinesTokenBurn cr 130 0 198 3542 rr (addr4 + 88) (addr5 + 88)
      {ACCT_REC}
      {MINT_REC}
      oldMemD_20
      ({setupPre})
      ({setupPost}) := by
  unfold SVM.Solana.Abstract.AsmRefinesTokenBurn
  simp only [SVM.Solana.Abstract.Mint.withSupply, SVM.Solana.Abstract.TokenAccount.withAmount]
  rw [src_account_eq (addr4 + 88) {ACCT_ARGS} oldMemD_21 oldMemB_35 oldMemB_15 oldMemB_19
        g1 g2 hg1 h72 h108 h109,
      mint_supply_eq (addr5 + 88) oldMemD_45 oldMemB_18 preAuthBA gD gF hgD hb45,
      src_account_eq (addr4 + 88) {ACCT_ARGS} (oldMemD_21 - oldMemD_20) oldMemB_35 oldMemB_15 oldMemB_19
        g1 g2 hg1 h72 h108 h109,
      mint_supply_eq (addr5 + 88) (oldMemD_45 - oldMemD_20) oldMemB_18 preAuthBA gD gF hgD hb45]
  simp only [pubkeyIs]
  have framed := cuTripleWithinMem_frame_right
    ( memBytesIs (addr4 + 161) g1 ** memBytesIs (addr4 + 198) g2 **
      memBytesIs (addr5 + 88) preAuthBA **
      memBytesIs (addr5 + 132) gD ** memBytesIs (addr5 + 134) gF )
    (by sl_pcfree) lift
  simp only [Nat.add_assoc, Nat.reduceAdd]
  sl_exact framed

end Examples.PTokenBurnRefinement
"""
open('/Users/abishek/code/qedsvm/examples/lean/PToken/BurnRefinement.lean','w').write(out)
print("wrote BurnRefinement.lean")
