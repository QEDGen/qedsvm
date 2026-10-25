/-
  What a successful p_token Transfer requires of its input, stated over the input bytes.
  Every top-level run of the decoded `.text` from the entrypoint that reaches the Transfer
  success edge (PC 4825) started from an input where:

  * the instruction is Transfer (discriminator 3), the source and destination are 165-byte
    token accounts, and the destination and authority are not duplicates of earlier accounts;
  * source and destination are Initialized (state byte 1: neither Uninitialized nor Frozen);
  * source and destination have the same mint;
  * the authority is the source's owner or its delegate (delegate set), and either signed,
    or is an initialized 355-byte multisig with `m = 0`.

  Offsets are into the serialized input: account 0 (source) data at 96, account 1
  (destination) data at 10600, account 2 (authority) key at 21024 and flags at 21016. In a
  token account, the mint is at +0, the owner at +32, the delegate tag and key at +72/+76,
  and the state byte at +108.

  The last route is the multisig with no signers: `m = 0` passes trivially. A multisig made
  by `InitializeMultisig` always has `1 <= m`, so the route needs an account the token
  program never creates. The amount checks (`amount != 0`, `amount <= balance`,
  `amount <= delegated_amount`) are proven in `SuccessPaths` as facts about the register the
  program debits; that register is read through a length-dependent pointer and is not pinned
  to a fixed input field here.
-/
import PToken.SuccessInputs

namespace Examples.PTokenTransferSpec

open SVM.SBPF Examples.PTokenErrorTail Examples.PTokenSuccessPaths

/-- Byte at input offset `off` of the initial state. -/
abbrev inByte (s0 : State) (off : Nat) : Nat :=
  Memory.readByWidth s0.mem (Memory.INPUT_START + off) .byte

/-- Little-endian u64 at input offset `off` of the initial state. -/
abbrev inU64 (s0 : State) (off : Nat) : Nat :=
  Memory.readByWidth s0.mem (Memory.INPUT_START + off) .dword

/-- The 32-byte keys at offsets `a` and `b` are equal (as four u64 words). -/
def keyEq (s0 : State) (a b : Nat) : Prop :=
  inU64 s0 a = inU64 s0 b ∧ inU64 s0 (a + 8) = inU64 s0 (b + 8) ∧
    inU64 s0 (a + 16) = inU64 s0 (b + 16) ∧ inU64 s0 (a + 24) = inU64 s0 (b + 24)

/-- The authority is a multisig with no required signers. -/
def multisigNoSigners (s0 : State) : Prop :=
  inU64 s0 21096 = 355 ∧ inByte s0 21106 = 1 ∧ inByte s0 21104 = 0

/-- A token-account state byte that is at most 2, not 0 and not 2 is 1 (Initialized). -/
theorem state_one {x : Nat} (h1 : x ≤ 2) (h2 : ¬x = 0) (h3 : ¬x = 2) : x = 1 := by omega

/-- **Transfer's input requirements.** -/
theorem transfer_requires (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (h1 : s0.regs.r1 = Memory.INPUT_START)
    (h10 : s0.regs.r10 = STACK_TOP) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 4825) :
    -- instruction and layout
    inByte s0 0 = 3 ∧ inU64 s0 88 = 165 ∧ inByte s0 10512 = 255 ∧ inU64 s0 10592 = 165 ∧
    inByte s0 21016 = 255 ∧
    -- both accounts Initialized
    inByte s0 204 = 1 ∧ inByte s0 10708 = 1 ∧
    -- same mint
    keyEq s0 96 10600 ∧
    -- authority: owner or delegate, signed or a multisig with no required signers
    ((keyEq s0 128 21024 ∧ inByte s0 21017 ≠ 0) ∨
     (keyEq s0 128 21024 ∧ multisigNoSigners s0) ∨
     (inByte s0 168 = 1 ∧ keyEq s0 172 21024 ∧ inByte s0 21017 ≠ 0) ∨
     (inByte s0 168 = 1 ∧ keyEq s0 172 21024 ∧ multisigNoSigners s0)) := by
  obtain ⟨hdom, c, ip, iq, hr, hip, hiq⟩ :=
    inputs4825 insns hp s0 hpc hcs (ptInit_concrete s0 h1 h10) n hend
  simp only [idom4825, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hdom
  simp at hdom
  obtain ⟨h0, h88, h10512, h10592, h21016, hs1, hs2, hd1, hd2, hs3, hd3, hm1, hm2, hm3, hm4⟩ :=
    hdom
  simp only [keyEq, multisigNoSigners, inByte, inU64, Nat.reduceAdd]
  refine ⟨h0, h88, h10512, h10592, h21016, state_one hs1 hs2 hs3, state_one hd1 hd2 hd3,
    ⟨hm1, hm2, hm3, hm4⟩, ?_⟩
  simp only [iroutes4825, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [ipre4825_4816, ipost4825_4816, ipre4825_5216, ipost4825_5216, ipre4825_5715,
      ipost4825_5715, ipre4825_6233, ipost4825_6233, List.mem_cons, List.mem_nil_iff,
      or_false, forall_eq_or_imp, forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond,
      AVal.val] at hip hiq <;>
    simp at hip hiq
  · -- owner, signer
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ho1, ho2, ho3, ho4⟩ := hip
    exact Or.inl ⟨⟨ho1, ho2, ho3, ho4⟩, hiq⟩
  · -- delegate, signer
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ht, hk1, hk2, hk3, hk4⟩ := hip
    exact Or.inr (Or.inr (Or.inl ⟨ht, ⟨hk1, hk2, hk3, hk4⟩, hiq⟩))
  · -- owner, multisig
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ho1, ho2, ho3, ho4, hl, hi⟩ := hip
    exact Or.inr (Or.inl ⟨⟨ho1, ho2, ho3, ho4⟩, hl, hi, hiq⟩)
  · -- delegate, multisig
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ht, hk1, hk2, hk3, hk4, hl, hi⟩ := hip
    exact Or.inr (Or.inr (Or.inr ⟨ht, ⟨hk1, hk2, hk3, hk4⟩, hl, hi, hiq⟩))

end Examples.PTokenTransferSpec
