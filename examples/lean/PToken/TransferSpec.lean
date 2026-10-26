/-
  What a successful p_token Transfer requires of its input, stated over the input bytes, for
  its three loop-free success edges:

  * `transfer_requires` (4825, amount moved),
  * `transfer_native_requires` (4832, native-SOL source: also requires `is_native` set),
  * `transfer_zero_requires` (5250, amount 0: also requires both accounts to be owned by the
    token program).

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
import PToken.ReadableFields

namespace Examples.PTokenTransferSpec

open SVM.SBPF Examples.PTokenErrorTail Examples.PTokenSuccessPaths Examples.PTokenReadableFields

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
  inU64 s0 field_authority_data_length = 355 ∧ inByte s0 field_authority_multisig_initialized = 1 ∧ inByte s0 field_authority_multisig_m = 0

/-- A token-account state byte that is at most 2, not 0 and not 2 is 1 (Initialized). -/
theorem state_one {x : Nat} (h1 : x ≤ 2) (h2 : ¬x = 0) (h3 : ¬x = 2) : x = 1 := by omega

/-- **Transfer's input requirements.** -/
theorem transfer_requires (insns : Array Insn) (hp : ptokenInsns = some insns) (s0 : State)
    (hpc : s0.pc = 198) (hcs : s0.callStack = []) (h1 : s0.regs.r1 = Memory.INPUT_START)
    (h10 : s0.regs.r10 = STACK_TOP) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 4825) :
    -- instruction and layout
    inByte s0 field_account_count = 3 ∧ inU64 s0 field_source_data_length = 165 ∧ inByte s0 field_destination_duplicate_marker = 255 ∧ inU64 s0 field_destination_data_length = 165 ∧
    inByte s0 field_authority_duplicate_marker = 255 ∧
    -- both accounts Initialized
    inByte s0 field_source_state = 1 ∧ inByte s0 field_destination_state = 1 ∧
    -- same mint
    keyEq s0 field_source_mint field_destination_mint ∧
    -- authority: owner or delegate, signed or a multisig with no required signers
    ((keyEq s0 field_source_owner field_authority_key ∧ inByte s0 field_authority_is_signer ≠ 0) ∨
     (keyEq s0 field_source_owner field_authority_key ∧ multisigNoSigners s0) ∨
     (inByte s0 field_source_delegate_tag = 1 ∧ keyEq s0 field_source_delegate field_authority_key ∧ inByte s0 field_authority_is_signer ≠ 0) ∨
     (inByte s0 field_source_delegate_tag = 1 ∧ keyEq s0 field_source_delegate field_authority_key ∧ multisigNoSigners s0)) := by
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

/-! ## The native-SOL and zero-amount Transfer edges -/

/-- The SPL Token program id (`TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`) as four
    little-endian u64 words; p_token is deployed at the same address. -/
def TOKEN_PROGRAM_ID : List Nat :=
  [0x93a165d7e1f6dd06, 0xac79ebce46e1cbd9, 0x91375b5fed85b41c, 0xa900ff7e85f58c3a]

/-- The account at input offset `off` has its first `k` owner words equal to the token program
    id (owner field of the serialized account header). -/
def ownerWords (s0 : State) (off k : Nat) : Prop :=
  ∀ i < k, inU64 s0 (off + 8 * i) = TOKEN_PROGRAM_ID.getD i 0

/-- The conditions shared by every Transfer success edge: layout, both accounts Initialized,
    same mint. -/
def TransferAccounts (s0 : State) : Prop :=
  inByte s0 field_account_count = 3 ∧ inU64 s0 field_source_data_length = 165 ∧ inByte s0 field_destination_duplicate_marker = 255 ∧ inU64 s0 field_destination_data_length = 165 ∧
  inByte s0 field_authority_duplicate_marker = 255 ∧ inByte s0 field_source_state = 1 ∧ inByte s0 field_destination_state = 1 ∧ keyEq s0 field_source_mint field_destination_mint

/-- The authority requirement shared by every Transfer success edge. -/
def TransferAuthority (s0 : State) : Prop :=
  (keyEq s0 field_source_owner field_authority_key ∧ inByte s0 field_authority_is_signer ≠ 0) ∨
  (keyEq s0 field_source_owner field_authority_key ∧ multisigNoSigners s0) ∨
  (inByte s0 field_source_delegate_tag = 1 ∧ keyEq s0 field_source_delegate field_authority_key ∧ inByte s0 field_authority_is_signer ≠ 0) ∨
  (inByte s0 field_source_delegate_tag = 1 ∧ keyEq s0 field_source_delegate field_authority_key ∧ multisigNoSigners s0)

theorem transfer_accounts_of_facts (s0 : State)
    (h0 : Memory.readByWidth s0.mem (Memory.INPUT_START + 0) .byte = 3)
    (h88 : Memory.readByWidth s0.mem (Memory.INPUT_START + 88) .dword = 165)
    (h10512 : Memory.readByWidth s0.mem (Memory.INPUT_START + 10512) .byte = 255)
    (h10592 : Memory.readByWidth s0.mem (Memory.INPUT_START + 10592) .dword = 165)
    (h21016 : Memory.readByWidth s0.mem (Memory.INPUT_START + 21016) .byte = 255)
    (hs1 : Memory.readByWidth s0.mem (Memory.INPUT_START + 204) .byte ≤ 2)
    (hs2 : ¬Memory.readByWidth s0.mem (Memory.INPUT_START + 204) .byte = 0)
    (hd1 : Memory.readByWidth s0.mem (Memory.INPUT_START + 10708) .byte ≤ 2)
    (hd2 : ¬Memory.readByWidth s0.mem (Memory.INPUT_START + 10708) .byte = 0)
    (hs3 : ¬Memory.readByWidth s0.mem (Memory.INPUT_START + 204) .byte = 2)
    (hd3 : ¬Memory.readByWidth s0.mem (Memory.INPUT_START + 10708) .byte = 2)
    (hm1 : Memory.readByWidth s0.mem (Memory.INPUT_START + 96) .dword =
      Memory.readByWidth s0.mem (Memory.INPUT_START + 10600) .dword)
    (hm2 : Memory.readByWidth s0.mem (Memory.INPUT_START + 104) .dword =
      Memory.readByWidth s0.mem (Memory.INPUT_START + 10608) .dword)
    (hm3 : Memory.readByWidth s0.mem (Memory.INPUT_START + 112) .dword =
      Memory.readByWidth s0.mem (Memory.INPUT_START + 10616) .dword)
    (hm4 : Memory.readByWidth s0.mem (Memory.INPUT_START + 120) .dword =
      Memory.readByWidth s0.mem (Memory.INPUT_START + 10624) .dword) :
    TransferAccounts s0 := by
  simp only [TransferAccounts, keyEq, inByte, inU64, Nat.reduceAdd]
  exact ⟨h0, h88, h10512, h10592, h21016, state_one hs1 hs2 hs3, state_one hd1 hd2 hd3,
    ⟨hm1, hm2, hm3, hm4⟩⟩

theorem transfer_accounts_of_dom (s0 : State) (hdom : ∀ ig ∈ idom4825, ig.holds s0) :
    TransferAccounts s0 := by
  simp only [idom4825, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hdom
  simp at hdom
  obtain ⟨h0, h88, h10512, h10592, h21016, hs1, hs2, hd1, hd2, hs3, hd3, hm1, hm2, hm3, hm4⟩ :=
    hdom
  exact transfer_accounts_of_facts s0 h0 h88 h10512 h10592 h21016 hs1 hs2 hd1 hd2 hs3 hd3
    hm1 hm2 hm3 hm4

/-- The pre-checkpoint facts of the two owner routes and the two delegate routes. -/
theorem owner_of_pre (s0 : State) (hip : ∀ ig ∈ ipre4825_4816, ig.holds s0) :
    keyEq s0 field_source_owner field_authority_key := by
  simp only [ipre4825_4816, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hip
  simp at hip
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ho1, ho2, ho3, ho4⟩ := hip
  exact ⟨ho1, ho2, ho3, ho4⟩

theorem delegate_of_pre (s0 : State) (hip : ∀ ig ∈ ipre4825_5216, ig.holds s0) :
    inByte s0 field_source_delegate_tag = 1 ∧ keyEq s0 field_source_delegate field_authority_key := by
  simp only [ipre4825_5216, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hip
  simp at hip
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ht, hk1, hk2, hk3, hk4⟩ := hip
  exact ⟨ht, hk1, hk2, hk3, hk4⟩

theorem ownerMs_of_pre (s0 : State) (hip : ∀ ig ∈ ipre4825_5715, ig.holds s0) :
    keyEq s0 field_source_owner field_authority_key ∧ inU64 s0 field_authority_data_length = 355 ∧ inByte s0 field_authority_multisig_initialized = 1 := by
  simp only [ipre4825_5715, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hip
  simp at hip
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ho1, ho2, ho3, ho4, hl, hi⟩ := hip
  exact ⟨⟨ho1, ho2, ho3, ho4⟩, hl, hi⟩

theorem delegateMs_of_pre (s0 : State) (hip : ∀ ig ∈ ipre4825_6233, ig.holds s0) :
    inByte s0 field_source_delegate_tag = 1 ∧ keyEq s0 field_source_delegate field_authority_key ∧ inU64 s0 field_authority_data_length = 355 ∧ inByte s0 field_authority_multisig_initialized = 1 := by
  simp only [ipre4825_6233, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hip
  simp at hip
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ht, hk1, hk2, hk3, hk4, hl, hi⟩ := hip
  exact ⟨ht, ⟨hk1, hk2, hk3, hk4⟩, hl, hi⟩

/-- The three Transfer edges share their routes' guards up to the authority checkpoint (the
    generated lists are identical). -/
theorem transfer_lists_shared :
    ipre4832_4816 = ipre4825_4816 ∧ ipre4832_5216 = ipre4825_5216 ∧
    ipre4832_5715 = ipre4825_5715 ∧ ipre4832_6233 = ipre4825_6233 ∧
    ipre5250_4816 = ipre4825_4816 ∧ ipre5250_5216 = ipre4825_5216 ∧
    ipre5250_5715 = ipre4825_5715 ∧ ipre5250_6233 = ipre4825_6233 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Native-SOL Transfer's input requirements** (edge 4832, the fall-through of 4825 that also
    moves lamports). Transfer's conditions, and the source is a native-SOL account: its
    `is_native` tag (token-account offset +109, input offset 205) is `Some`. -/
theorem transfer_native_requires (insns : Array Insn) (hp : ptokenInsns = some insns)
    (s0 : State) (hpc : s0.pc = 198) (hcs : s0.callStack = [])
    (h1 : s0.regs.r1 = Memory.INPUT_START) (h10 : s0.regs.r10 = STACK_TOP) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 4832) :
    TransferAccounts s0 ∧ TransferAuthority s0 ∧ inByte s0 field_source_is_native = 1 := by
  obtain ⟨hdom, c, ip, iq, hr, hip, hiq⟩ :=
    inputs4832 insns hp s0 hpc hcs (ptInit_concrete s0 h1 h10) n hend
  obtain ⟨hp1, hp2, hp3, hp4, -⟩ := transfer_lists_shared
  -- the 15 shared dominating guards, then the native-SOL check (it dominates 4832)
  simp only [idom4832, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hdom
  simp at hdom
  obtain ⟨h0, h88, h10512, h10592, h21016, hs1, hs2, hd1, hd2, hs3, hd3, hm1, hm2, hm3, hm4,
    hnat⟩ := hdom
  refine ⟨transfer_accounts_of_facts s0 h0 h88 h10512 h10592 h21016 hs1 hs2 hd1 hd2 hs3 hd3
    hm1 hm2 hm3 hm4, ?_, hnat⟩
  simp only [iroutes4832, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [ipost4832_4816, ipost4832_5216, ipost4832_5715, ipost4832_6233,
      List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, IGuard.holds,
      Insn.jumpOps?, jumpCond, AVal.val] at hiq <;>
    simp at hiq
  · rw [hp1] at hip; exact Or.inl ⟨owner_of_pre s0 hip, hiq.1⟩
  · rw [hp2] at hip
    exact Or.inr (Or.inr (Or.inl ⟨(delegate_of_pre s0 hip).1, (delegate_of_pre s0 hip).2,
      hiq.2⟩))
  · rw [hp3] at hip
    obtain ⟨ho, hl, hi⟩ := ownerMs_of_pre s0 hip
    exact Or.inr (Or.inl ⟨ho, hl, hi, hiq.2⟩)
  · rw [hp4] at hip
    obtain ⟨ht, hk, hl, hi⟩ := delegateMs_of_pre s0 hip
    exact Or.inr (Or.inr (Or.inr ⟨ht, hk, hl, hi, hiq.2⟩))

/-- **Zero-amount Transfer's input requirements** (edge 5250, `jeq r1, r2, 3542`). Transfer's
    account and authority conditions, and both accounts are owned by the token program: all
    four owner words of the source and the first three of the destination. The destination's
    last owner word is the edge's own comparison, so success through this edge also requires
    it; standing at the edge does not. -/
theorem transfer_zero_requires (insns : Array Insn) (hp : ptokenInsns = some insns)
    (s0 : State) (hpc : s0.pc = 198) (hcs : s0.callStack = [])
    (h1 : s0.regs.r1 = Memory.INPUT_START) (h10 : s0.regs.r10 = STACK_TOP) (n : Nat)
    (hend : (executeFn (Runner.fetchFromArray insns) s0 n).callStack = [] ∧
      (executeFn (Runner.fetchFromArray insns) s0 n).pc = 5250) :
    TransferAccounts s0 ∧ TransferAuthority s0 ∧ ownerWords s0 field_source_program_owner 4 ∧ ownerWords s0 field_destination_program_owner 3 := by
  obtain ⟨hdom, c, ip, iq, hr, hip, hiq⟩ :=
    inputs5250 insns hp s0 hpc hcs (ptInit_concrete s0 h1 h10) n hend
  obtain ⟨-, -, -, -, hp1, hp2, hp3, hp4⟩ := transfer_lists_shared
  -- the 15 shared dominating guards, then both accounts' owner checks (they dominate 5250)
  simp only [idom5250, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, IGuard.holds, Insn.jumpOps?, jumpCond, AVal.val] at hdom
  simp at hdom
  obtain ⟨h0, h88, h10512, h10592, h21016, hs1, hs2, hd1, hd2, hs3, hd3, hm1, hm2, hm3, hm4,
    w0, w1, w2, w3, d0, d1, d2⟩ := hdom
  refine ⟨transfer_accounts_of_facts s0 h0 h88 h10512 h10592 h21016 hs1 hs2 hd1 hd2 hs3 hd3
    hm1 hm2 hm3 hm4, ?_, ?_⟩
  rotate_left
  · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
        simpa [TOKEN_PROGRAM_ID, inU64]
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simpa [TOKEN_PROGRAM_ID, inU64]
  simp only [iroutes5250, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp only [ipost5250_4816, ipost5250_5216, ipost5250_5715, ipost5250_6233,
      List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, IGuard.holds,
      Insn.jumpOps?, jumpCond, AVal.val] at hiq <;>
    simp at hiq
  · rw [hp1] at hip
    exact Or.inl ⟨owner_of_pre s0 hip, hiq.1⟩
  · rw [hp2] at hip
    exact Or.inr (Or.inr (Or.inl ⟨(delegate_of_pre s0 hip).1, (delegate_of_pre s0 hip).2,
      hiq.1⟩))
  · rw [hp3] at hip
    obtain ⟨-, -, -, -, -, -, -, hm⟩ := hiq
    obtain ⟨ho, hl, hi⟩ := ownerMs_of_pre s0 hip
    exact Or.inr (Or.inl ⟨ho, hl, hi, hm⟩)
  · rw [hp4] at hip
    obtain ⟨-, -, -, -, -, -, -, hm⟩ := hiq
    obtain ⟨ht, hk, hl, hi⟩ := delegateMs_of_pre s0 hip
    exact Or.inr (Or.inr (Or.inr ⟨ht, hk, hl, hi, hm⟩))

end Examples.PTokenTransferSpec
