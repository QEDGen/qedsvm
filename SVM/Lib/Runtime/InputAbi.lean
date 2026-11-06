/-
  The aligned account input a program finds at `r1` (#145): agave's
  `serialize_parameters_for_abiv1`, with SIMD-0449 on as under Mollusk's `all_enabled`.

      8   account count
      then per instruction account, either a duplicate (8 bytes)
        1   position of the first reference to this account
        7   zeros
      or a record (`88 + data + pad + 10240 + 8` bytes)
        1   0xff
        3   is_signer, is_writable, is_executable
        4   zeros (`original_data_len`: a program may keep a length there, the runtime never does)
        32  key
        32  owner
        8   lamports
        8   data_len
        ..  data, zeros to 8, 10240 zeros
        8   rent_epoch, always `u64::MAX`
      8   instruction data length
      ..  instruction data
      32  program id
      ..  zeros to 8
      8   per instruction account: the address of its record (SIMD-0449)

  `serialize` is that buffer, `parse` its inverse. `parse` accepts exactly the buffers
  `serialize` produces from a well-formed input, so nothing is canonicalized:
  `parse_serialize` and `serialize_of_parse` are the two directions of the roundtrip.
  Malformed duplicate references, nonzero padding and unknown markers do not parse.

  A duplicate holds no state of its own. `Input.resolve` reads it through its original,
  and `resolve_dup` and `pointer_dup` say that both references are one account, at one
  address. `ofInstruction` builds an input the way the runtime does, from an instruction's
  metas, whose flags are the OR over an account's references.

  What this does not say:
  - The realloc room is address space. Under direct mapping agave faults on any access
    beyond an account's current length, where this file and the runner's flat region
    show zeros. The bytes agave does map agree (`input_abi_matches_mollusk`); which
    accesses it refuses belongs to #158.
  - After a program runs, the buffer need not parse: it may hold anything in the padding
    and any `data_len`. Reading it back is `AccountWrites`, and #146 connects the two.
  - Loader-v1 unaligned input and transaction-level validation are out of scope.
-/
import SVM.Lib.Runtime.Checks
import SVM.Solana.InputLayout

namespace SVM.Runtime

open SVM.Pubkey (Pubkey)

/-- Where the runtime maps the input, which the SIMD-0449 pointers are relative to. -/
def MM_INPUT_START : Nat := 0x400000000

/-- `MAX_ACCOUNTS_PER_INSTRUCTION`. A position fits below `NON_DUP_MARKER`. -/
def MAX_ACCOUNTS : Nat := 255

def NON_DUP_MARKER : Nat := 0xff

/-- Agave serializes this for every account, whatever the account holds. -/
def RENT_EPOCH_MASKED : Nat := 18446744073709551615

/-- An instruction account's record: the account and how this instruction holds it. -/
structure InputAccount where
  key      : Pubkey
  isSigner : Bool
  isWritable : Bool
  state    : AccountState
  deriving Repr, DecidableEq

/-- One position in the instruction's account list. -/
inductive InputEntry where
  | account (a : InputAccount)
  | dup (pos : Nat)
  deriving Repr, DecidableEq

/-- The semantic content of an input buffer. -/
structure Input where
  entries   : List InputEntry
  instrData : List UInt8
  programId : Pubkey
  deriving Repr, DecidableEq

/-! ## Bytes -/

/-- Little-endian bytes of a `w`-byte integer. -/
def leN : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat n :: leN w (n / 256)

/-- The integer in the first `w` bytes. -/
def rdN : Nat → List UInt8 → Nat
  | 0, _ => 0
  | w + 1, bs => (bs.headD 0).toNat + 256 * rdN w bs.tail

@[irreducible] def le64 (n : Nat) : List UInt8 := leN 8 n

@[irreducible] def rd64 (bs : List UInt8) : Nat := rdN 8 bs

def zeros (n : Nat) : List UInt8 := List.replicate n 0

def flagByte (b : Bool) : UInt8 := if b then 1 else 0

def pubkeyBytes (k : Pubkey) : List UInt8 :=
  le64 k.c0 ++ le64 k.c1 ++ le64 k.c2 ++ le64 k.c3

/-- Padding that takes a length to a multiple of 8 (`BPF_ALIGN_OF_U128`). -/
def alignPad (n : Nat) : Nat := (8 - n % 8) % 8

def recordBytes (a : InputAccount) : List UInt8 :=
  [UInt8.ofNat NON_DUP_MARKER, flagByte a.isSigner, flagByte a.isWritable,
    flagByte a.state.executable] ++ zeros 4 ++ pubkeyBytes a.key ++ pubkeyBytes a.state.owner
    ++ le64 a.state.lamports ++ le64 a.state.data.length ++ a.state.data
    ++ zeros (alignPad a.state.data.length + SVM.Runtime.MAX_PERMITTED_DATA_INCREASE)
    ++ le64 a.state.rentEpoch

def entryBytes : InputEntry → List UInt8
  | .account a => recordBytes a
  | .dup pos => UInt8.ofNat pos :: zeros 7

/-! ## Layout -/

/-- A record's size, by its data length. -/
def recordSize (dataLen : Nat) : Nat :=
  88 + dataLen + alignPad dataLen + SVM.Runtime.MAX_PERMITTED_DATA_INCREASE + 8

def entrySize : InputEntry → Nat
  | .account a => recordSize a.state.data.length
  | .dup _ => 8

/-- Offset of position `k`: the count, then every earlier entry. -/
def slotOff (es : List InputEntry) (k : Nat) : Nat :=
  8 + ((es.take k).map entrySize).sum

/-- Offset of the instruction data length. -/
def instrLenOff (es : List InputEntry) : Nat := slotOff es es.length

def instrDataOff (es : List InputEntry) : Nat := instrLenOff es + 8

def programIdOff (es : List InputEntry) (ixLen : Nat) : Nat := instrDataOff es + ixLen

/-- Offset of the pointer array. -/
def pointersOff (es : List InputEntry) (ixLen : Nat) : Nat :=
  programIdOff es ixLen + 32 + alignPad ixLen

/-- Offset of a record's fields, from the record's start. -/
def KEY_OFF : Nat := 8
def OWNER_OFF : Nat := 40
def LAMPORTS_OFF : Nat := 72
def DATA_LEN_OFF : Nat := 80
def DATA_OFF : Nat := 88

/-- Offset of a record's rent epoch, from the record's start. -/
def rentEpochOff (dataLen : Nat) : Nat :=
  88 + dataLen + alignPad dataLen + SVM.Runtime.MAX_PERMITTED_DATA_INCREASE

/-- The position a reference resolves to: itself, or the position it duplicates. -/
def resolveIdx (es : List InputEntry) (k : Nat) : Nat :=
  match es[k]? with
  | some (.dup p) => p
  | _ => k

/-- The pointer array's entry for position `k`: its record's address. -/
def pointer (es : List InputEntry) (k : Nat) : Nat :=
  MM_INPUT_START + slotOff es (resolveIdx es k)

def pointerBytes (es : List InputEntry) : List UInt8 :=
  ((List.range es.length).map (pointer es)).flatMap le64

/-! ## Serialization -/

def trailerBytes (es : List InputEntry) (data : List UInt8) (pid : Pubkey) : List UInt8 :=
  le64 data.length ++ data ++ pubkeyBytes pid ++ zeros (alignPad data.length) ++ pointerBytes es

/-- The buffer at `r1`. -/
def serialize (i : Input) : List UInt8 :=
  le64 i.entries.length ++ i.entries.flatMap entryBytes ++
    trailerBytes i.entries i.instrData i.programId

/-! ## Well-formed inputs -/

def Bounded (n : Nat) : Prop := n < 2 ^ 64

instance (n : Nat) : Decidable (Bounded n) := by unfold Bounded; infer_instance

def PubkeyBounded (k : Pubkey) : Prop :=
  Bounded k.c0 ∧ Bounded k.c1 ∧ Bounded k.c2 ∧ Bounded k.c3

instance (k : Pubkey) : Decidable (PubkeyBounded k) := by unfold PubkeyBounded; infer_instance

/-- A record agave can emit. -/
def InputAccount.WellFormed (a : InputAccount) : Prop :=
  PubkeyBounded a.key ∧ PubkeyBounded a.state.owner ∧ Bounded a.state.lamports ∧
    a.state.data.length ≤ MAX_PERMITTED_DATA_LENGTH ∧ a.state.rentEpoch = RENT_EPOCH_MASKED

instance (a : InputAccount) : Decidable a.WellFormed := by
  unfold InputAccount.WellFormed; infer_instance

/-- Position `p` of `prior` holds a record. -/
def isRecordAt (prior : List InputEntry) (p : Nat) : Bool :=
  match prior[p]? with
  | some (.account _) => true
  | _ => false

/-- No record in `prior` has this key. -/
def keyFresh (prior : List InputEntry) (k : Pubkey) : Bool :=
  prior.all fun
    | .account b => decide (b.key ≠ k)
    | .dup _ => true

/-- An entry may appear after `prior`: a record of a key not seen yet, or a duplicate
    of an earlier record. A duplicate of a duplicate never occurs, because the runtime
    names the first reference. -/
def EntryOk (prior : List InputEntry) : InputEntry → Prop
  | .account a => a.WellFormed ∧ keyFresh prior a.key = true
  | .dup p => isRecordAt prior p = true

instance (prior : List InputEntry) (e : InputEntry) : Decidable (EntryOk prior e) := by
  cases e <;> unfold EntryOk <;> infer_instance

/-- Every entry is acceptable given the ones before it. -/
def EntriesOk : List InputEntry → List InputEntry → Prop
  | _, [] => True
  | prior, e :: es => EntryOk prior e ∧ EntriesOk (prior ++ [e]) es

instance decEntriesOk : ∀ (prior es : List InputEntry), Decidable (EntriesOk prior es)
  | _, [] => isTrue trivial
  | prior, e :: es =>
    have : Decidable (EntriesOk (prior ++ [e]) es) := decEntriesOk (prior ++ [e]) es
    by unfold EntriesOk; infer_instance

/-- An input the runtime can hand a program. -/
def Input.WellFormed (i : Input) : Prop :=
  i.entries.length ≤ MAX_ACCOUNTS ∧ EntriesOk [] i.entries ∧
    Bounded i.instrData.length ∧ PubkeyBounded i.programId

instance (i : Input) : Decidable i.WellFormed := by unfold Input.WellFormed; infer_instance

/-! ## Decoding -/

def rdKey (bs : List UInt8) : Pubkey :=
  ⟨rd64 bs, rd64 (bs.drop 8), rd64 (bs.drop 16), rd64 (bs.drop 24)⟩

/-- Read one entry, ignoring padding. `parse` holds it to the exact bytes. -/
def decodeEntry (bs : List UInt8) : Option (InputEntry × List UInt8) :=
  match bs with
  | [] => none
  | m :: rest =>
    if m.toNat = NON_DUP_MARKER then
      let dataLen := rd64 (bs.drop DATA_LEN_OFF)
      let a : InputAccount :=
        { key := rdKey (bs.drop KEY_OFF)
          isSigner := bs.getD 1 0 != 0
          isWritable := bs.getD 2 0 != 0
          state :=
            { owner := rdKey (bs.drop OWNER_OFF)
              lamports := rd64 (bs.drop LAMPORTS_OFF)
              data := (bs.drop DATA_OFF).take dataLen
              executable := bs.getD 3 0 != 0
              rentEpoch := rd64 (bs.drop (rentEpochOff dataLen)) } }
      some (.account a, bs.drop (recordSize dataLen))
    else
      some (.dup m.toNat, rest.drop 7)

/-- Read `n` entries. -/
def decodeEntries : Nat → List UInt8 → Option (List InputEntry × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match decodeEntry bs with
    | none => none
    | some (e, rest) =>
      match decodeEntries n rest with
      | none => none
      | some (es, rest') => some (e :: es, rest')

/-- Read the structure of a buffer, ignoring padding. -/
def decode (bs : List UInt8) : Option Input :=
  let n := rd64 bs
  if n ≤ MAX_ACCOUNTS then
    match decodeEntries n (bs.drop 8) with
    | none => none
    | some (es, rest) =>
      let ixLen := rd64 rest
      some { entries := es
             instrData := (rest.drop 8).take ixLen
             programId := rdKey (rest.drop (8 + ixLen)) }
  else none

/-- Parse a buffer: its structure must be well formed and must serialize back to it. -/
def parse (bs : List UInt8) : Option Input :=
  match decode bs with
  | none => none
  | some i => if i.WellFormed ∧ serialize i = bs then some i else none

/-! ## Reading bytes back -/

theorem leN_length (w n : Nat) : (leN w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [leN, ih]

theorem le64_length (n : Nat) : (le64 n).length = 8 := by
  unfold le64; exact leN_length 8 n

theorem rdN_leN_append (w : Nat) {n : Nat} (hn : n < 256 ^ w) (t : List UInt8) :
    rdN w (leN w n ++ t) = n := by
  induction w generalizing n with
  | zero => simp at hn; simp [rdN, hn]
  | succ w ih =>
    have hd : n / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at hn
      exact Nat.div_lt_of_lt_mul (by omega)
    simp only [leN, List.cons_append, rdN, List.headD_cons, List.tail_cons, ih hd,
      UInt8.toNat_ofNat']
    omega

theorem rd64_le64_append {n : Nat} (hn : Bounded n) (t : List UInt8) :
    rd64 (le64 n ++ t) = n := by
  unfold rd64 le64
  exact rdN_leN_append 8 (by simpa [Bounded] using hn) t

theorem rdN_lt : ∀ (w : Nat) (bs : List UInt8), rdN w bs < 256 ^ w
  | 0, _ => by simp [rdN]
  | w + 1, bs => by
    have ih := rdN_lt w bs.tail
    have hb := (bs.headD 0).toNat_lt
    simp only [rdN, Nat.pow_succ]
    omega

/-- Any eight bytes read as a u64. -/
theorem rd64_bounded (bs : List UInt8) : Bounded (rd64 bs) := by
  unfold rd64 Bounded
  exact rdN_lt 8 bs

theorem rdN_append_left : ∀ (w : Nat) (xs t : List UInt8), w ≤ xs.length →
    rdN w (xs ++ t) = rdN w xs
  | 0, _, _, _ => rfl
  | w + 1, [], _, h => by simp at h
  | w + 1, x :: xs, t, h => by
    have := rdN_append_left w xs t (by simpa using h)
    simp [rdN, this]

theorem pubkeyBytes_length (k : Pubkey) : (pubkeyBytes k).length = 32 := by
  simp [pubkeyBytes, le64_length]

/-- Dropping exactly a prefix. -/
theorem drop_prefix {A B : List UInt8} {n : Nat} (h : A.length = n) : (A ++ B).drop n = B := by
  subst h; simp

theorem rdKey_pubkeyBytes_append {k : Pubkey} (hk : PubkeyBounded k) (t : List UInt8) :
    rdKey (pubkeyBytes k ++ t) = k := by
  obtain ⟨h0, h1, h2, h3⟩ := hk
  cases k with
  | mk c0 c1 c2 c3 =>
    have l := le64_length
    apply SVM.Pubkey.Pubkey.ext' <;> simp only [rdKey, pubkeyBytes, List.append_assoc]
    · exact rd64_le64_append h0 _
    · rw [drop_prefix (l _)]; exact rd64_le64_append h1 _
    · rw [show le64 c0 ++ (le64 c1 ++ (le64 c2 ++ (le64 c3 ++ t))) =
          (le64 c0 ++ le64 c1) ++ (le64 c2 ++ (le64 c3 ++ t)) by simp,
        drop_prefix (by simp [l])]
      exact rd64_le64_append h2 _
    · rw [show le64 c0 ++ (le64 c1 ++ (le64 c2 ++ (le64 c3 ++ t))) =
          (le64 c0 ++ le64 c1 ++ le64 c2) ++ (le64 c3 ++ t) by simp,
        drop_prefix (by simp [l])]
      exact rd64_le64_append h3 _

theorem zeros_length (n : Nat) : (zeros n).length = n := by simp [zeros]

theorem alignPad_add (n : Nat) : (n + alignPad n) % 8 = 0 := by unfold alignPad; omega

/-! ## The roundtrip -/

/-- A record's bytes, cut at the field `off` bytes in. -/
private theorem record_cut (a : InputAccount) (t : List UInt8) :
    let pre : List UInt8 := [UInt8.ofNat NON_DUP_MARKER, flagByte a.isSigner, flagByte a.isWritable,
      flagByte a.state.executable] ++ zeros 4
    let K := pubkeyBytes a.key
    let O := pubkeyBytes a.state.owner
    let L := le64 a.state.lamports
    let D := le64 a.state.data.length
    let d := a.state.data
    let Z := zeros (alignPad a.state.data.length + MAX_PERMITTED_DATA_INCREASE)
    let R := le64 a.state.rentEpoch
    recordBytes a ++ t = pre ++ (K ++ (O ++ (L ++ (D ++ (d ++ (Z ++ (R ++ t))))))) ∧
    recordBytes a ++ t = (pre ++ K) ++ (O ++ (L ++ (D ++ (d ++ (Z ++ (R ++ t)))))) ∧
    recordBytes a ++ t = (pre ++ K ++ O) ++ (L ++ (D ++ (d ++ (Z ++ (R ++ t))))) ∧
    recordBytes a ++ t = (pre ++ K ++ O ++ L) ++ (D ++ (d ++ (Z ++ (R ++ t)))) ∧
    recordBytes a ++ t = (pre ++ K ++ O ++ L ++ D) ++ (d ++ (Z ++ (R ++ t))) ∧
    recordBytes a ++ t = (pre ++ K ++ O ++ L ++ D ++ d ++ Z) ++ (R ++ t) ∧
    recordBytes a ++ t = (pre ++ K ++ O ++ L ++ D ++ d ++ Z ++ R) ++ t := by
  simp [recordBytes, List.append_assoc]

theorem recordBytes_length (a : InputAccount) :
    (recordBytes a).length = recordSize a.state.data.length := by
  simp [recordBytes, recordSize, zeros_length, le64_length, pubkeyBytes_length]
  omega

theorem entryBytes_length (e : InputEntry) : (entryBytes e).length = entrySize e := by
  cases e with
  | account a => exact recordBytes_length a
  | dup p => simp [entryBytes, entrySize, zeros_length]

private theorem flag_ne (b : Bool) : (flagByte b != 0) = b := by
  cases b <;> decide

theorem rentEpochMasked_bounded : Bounded RENT_EPOCH_MASKED := by
  unfold Bounded RENT_EPOCH_MASKED; omega

theorem drop_key (a : InputAccount) (t : List UInt8) : (recordBytes a ++ t).drop KEY_OFF =
    pubkeyBytes a.key ++ (pubkeyBytes a.state.owner ++ (le64 a.state.lamports ++
      (le64 a.state.data.length ++ (a.state.data ++
        (zeros (alignPad a.state.data.length + MAX_PERMITTED_DATA_INCREASE) ++
          (le64 a.state.rentEpoch ++ t)))))) := by
  rw [(record_cut a t).1]; exact drop_prefix (by simp [zeros_length, KEY_OFF])

theorem drop_owner (a : InputAccount) (t : List UInt8) : (recordBytes a ++ t).drop OWNER_OFF =
    pubkeyBytes a.state.owner ++ (le64 a.state.lamports ++
      (le64 a.state.data.length ++ (a.state.data ++
        (zeros (alignPad a.state.data.length + MAX_PERMITTED_DATA_INCREASE) ++
          (le64 a.state.rentEpoch ++ t))))) := by
  rw [(record_cut a t).2.1]
  exact drop_prefix (by simp [zeros_length, pubkeyBytes_length, OWNER_OFF])

theorem drop_lamports (a : InputAccount) (t : List UInt8) :
    (recordBytes a ++ t).drop LAMPORTS_OFF =
    le64 a.state.lamports ++ (le64 a.state.data.length ++ (a.state.data ++
        (zeros (alignPad a.state.data.length + MAX_PERMITTED_DATA_INCREASE) ++
          (le64 a.state.rentEpoch ++ t)))) := by
  rw [(record_cut a t).2.2.1]
  exact drop_prefix (by simp [zeros_length, pubkeyBytes_length, LAMPORTS_OFF])

theorem drop_dataLen (a : InputAccount) (t : List UInt8) :
    (recordBytes a ++ t).drop DATA_LEN_OFF =
    le64 a.state.data.length ++ (a.state.data ++
        (zeros (alignPad a.state.data.length + MAX_PERMITTED_DATA_INCREASE) ++
          (le64 a.state.rentEpoch ++ t))) := by
  rw [(record_cut a t).2.2.2.1]
  exact drop_prefix (by simp [zeros_length, pubkeyBytes_length, le64_length, DATA_LEN_OFF])

theorem drop_data (a : InputAccount) (t : List UInt8) : (recordBytes a ++ t).drop DATA_OFF =
    a.state.data ++ (zeros (alignPad a.state.data.length + MAX_PERMITTED_DATA_INCREASE) ++
          (le64 a.state.rentEpoch ++ t)) := by
  rw [(record_cut a t).2.2.2.2.1]
  exact drop_prefix (by simp [zeros_length, pubkeyBytes_length, le64_length, DATA_OFF])

theorem drop_rent (a : InputAccount) (t : List UInt8) :
    (recordBytes a ++ t).drop (rentEpochOff a.state.data.length) =
      le64 a.state.rentEpoch ++ t := by
  rw [(record_cut a t).2.2.2.2.2.1]
  exact drop_prefix (by
    simp [zeros_length, pubkeyBytes_length, le64_length, rentEpochOff]; omega)

theorem decodeEntry_record {a : InputAccount} (h : a.WellFormed) (t : List UInt8) :
    decodeEntry (recordBytes a ++ t) = some (.account a, t) := by
  obtain ⟨hk, ho, hl, hd, hr⟩ := h
  have hdb : Bounded a.state.data.length := by
    unfold Bounded MAX_PERMITTED_DATA_LENGTH at *; omega
  have hrb : Bounded a.state.rentEpoch := by rw [hr]; exact rentEpochMasked_bounded
  have fKey := drop_key a t
  have fOwn := drop_owner a t
  have fLam := drop_lamports a t
  have fLen := drop_dataLen a t
  have fDat := drop_data a t
  have fRent := drop_rent a t
  have fEnd : (recordBytes a ++ t).drop (recordSize a.state.data.length) = t :=
    drop_prefix (recordBytes_length a)
  have hdl : rd64 ((recordBytes a ++ t).drop DATA_LEN_OFF) = a.state.data.length := by
    rw [fLen]; exact rd64_le64_append hdb _
  -- The head is the marker, and the flags sit behind it.
  have hhead : recordBytes a ++ t = UInt8.ofNat NON_DUP_MARKER :: flagByte a.isSigner ::
      flagByte a.isWritable :: flagByte a.state.executable ::
      (zeros 4 ++ pubkeyBytes a.key ++ pubkeyBytes a.state.owner ++ le64 a.state.lamports ++
        le64 a.state.data.length ++ a.state.data ++
        zeros (alignPad a.state.data.length + MAX_PERMITTED_DATA_INCREASE) ++
        le64 a.state.rentEpoch ++ t) := by
    simp [recordBytes]
  have hs : (recordBytes a ++ t).getD 1 0 = flagByte a.isSigner := by rw [hhead]; rfl
  have hw : (recordBytes a ++ t).getD 2 0 = flagByte a.isWritable := by rw [hhead]; rfl
  have hx : (recordBytes a ++ t).getD 3 0 = flagByte a.state.executable := by rw [hhead]; rfl
  have hm : ∃ rest, recordBytes a ++ t = UInt8.ofNat NON_DUP_MARKER :: rest := ⟨_, hhead⟩
  obtain ⟨rest, hrest⟩ := hm
  have hdec : ∀ bs : List UInt8, bs = recordBytes a ++ t →
      decodeEntry bs = some (.account
        { key := rdKey (bs.drop KEY_OFF)
          isSigner := bs.getD 1 0 != 0
          isWritable := bs.getD 2 0 != 0
          state :=
            { owner := rdKey (bs.drop OWNER_OFF)
              lamports := rd64 (bs.drop LAMPORTS_OFF)
              data := (bs.drop DATA_OFF).take (rd64 (bs.drop DATA_LEN_OFF))
              executable := bs.getD 3 0 != 0
              rentEpoch := rd64 (bs.drop (rentEpochOff (rd64 (bs.drop DATA_LEN_OFF)))) } },
        bs.drop (recordSize (rd64 (bs.drop DATA_LEN_OFF)))) := by
    intro bs hb
    subst hb
    rw [hrest]
    simp only [decodeEntry]
    rw [if_pos (by decide)]
  rw [hdec _ rfl, hdl, fKey, fOwn, fLam, fDat, fRent, fEnd, hs, hw, hx]
  rw [rdKey_pubkeyBytes_append hk, rdKey_pubkeyBytes_append ho, rd64_le64_append hl,
    rd64_le64_append hrb, flag_ne, flag_ne, flag_ne]
  simp

theorem decodeEntry_dup {p : Nat} (hp : p < NON_DUP_MARKER) (t : List UInt8) :
    decodeEntry (entryBytes (.dup p) ++ t) = some (.dup p, t) := by
  have hv : (UInt8.ofNat p).toNat = p := by
    rw [UInt8.toNat_ofNat']; unfold NON_DUP_MARKER at hp; omega
  simp only [entryBytes, List.cons_append, decodeEntry]
  rw [if_neg (by rw [hv]; omega), hv, drop_prefix (zeros_length 7)]

/-- Facts about an entry that hold given the ones before it. -/
theorem decodeEntries_flatMap : ∀ (es prior : List InputEntry) (t : List UInt8),
    EntriesOk prior es → prior.length + es.length ≤ MAX_ACCOUNTS →
    decodeEntries es.length (es.flatMap entryBytes ++ t) = some (es, t)
  | [], _, _, _, _ => rfl
  | e :: es, prior, t, ⟨he, hes⟩, hlen => by
    have hrec := decodeEntries_flatMap es (prior ++ [e]) t hes (by simp at hlen ⊢; omega)
    have hdec : decodeEntry (entryBytes e ++ (es.flatMap entryBytes ++ t)) =
        some (e, es.flatMap entryBytes ++ t) := by
      cases e with
      | account a => exact decodeEntry_record he.1 _
      | dup p =>
        apply decodeEntry_dup
        have hp : p < prior.length := by
          simp only [EntryOk, isRecordAt] at he
          rcases Nat.lt_or_ge p prior.length with hlt | hge
          · exact hlt
          · rw [List.getElem?_eq_none hge] at he
            simp at he
        simp only [List.length_cons] at hlen
        unfold MAX_ACCOUNTS at hlen
        unfold NON_DUP_MARKER
        omega
    simp only [List.flatMap_cons, List.append_assoc, decodeEntries, hdec, hrec]

private theorem decode_eq (bs : List UInt8) : decode bs =
    if rd64 bs ≤ MAX_ACCOUNTS then
      match decodeEntries (rd64 bs) (bs.drop 8) with
      | none => none
      | some (es, rest) =>
        some { entries := es
               instrData := (rest.drop 8).take (rd64 rest)
               programId := rdKey (rest.drop (8 + rd64 rest)) }
    else none := rfl

/-- Decoding a well-formed input's bytes recovers it. -/
theorem decode_serialize {i : Input} (h : i.WellFormed) : decode (serialize i) = some i := by
  obtain ⟨hn, hes, hix, hpid⟩ := h
  cases i with
  | mk es data pid =>
    simp only at hn hes hix hpid
    have hb : Bounded es.length := by
      unfold Bounded; unfold MAX_ACCOUNTS at hn; omega
    have hdrop : (le64 es.length ++ es.flatMap entryBytes ++ trailerBytes es data pid).drop 8 =
        es.flatMap entryBytes ++ trailerBytes es data pid := by
      rw [List.append_assoc]; exact drop_prefix (le64_length _)
    have hrd : rd64 (le64 es.length ++ es.flatMap entryBytes ++ trailerBytes es data pid) =
        es.length := by
      rw [List.append_assoc]; exact rd64_le64_append hb _
    have hrec := decodeEntries_flatMap es [] (trailerBytes es data pid) hes (by simpa using hn)
    have hixLen : rd64 (trailerBytes es data pid) = data.length := by
      simp only [trailerBytes, List.append_assoc]
      exact rd64_le64_append hix _
    have hd8 : (trailerBytes es data pid).drop 8 =
        data ++ (pubkeyBytes pid ++ (zeros (alignPad data.length) ++ pointerBytes es)) := by
      simp only [trailerBytes, List.append_assoc]
      exact drop_prefix (le64_length _)
    have hdk : (trailerBytes es data pid).drop (8 + data.length) =
        pubkeyBytes pid ++ (zeros (alignPad data.length) ++ pointerBytes es) := by
      rw [show trailerBytes es data pid = (le64 data.length ++ data) ++
        (pubkeyBytes pid ++ (zeros (alignPad data.length) ++ pointerBytes es)) by
          simp [trailerBytes, List.append_assoc]]
      exact drop_prefix (by simp [le64_length])
    show decode (le64 es.length ++ es.flatMap entryBytes ++ trailerBytes es data pid) = _
    rw [decode_eq, hrd, if_pos hn, hdrop, hrec]
    show some ({ entries := es
                 instrData := ((trailerBytes es data pid).drop 8).take (rd64 (trailerBytes es data pid))
                 programId := rdKey ((trailerBytes es data pid).drop
                   (8 + rd64 (trailerBytes es data pid))) } : Input) = _
    rw [hixLen, hd8, hdk, rdKey_pubkeyBytes_append hpid, List.take_left']
    rfl

/-- Well-formed inputs survive the bytes. -/
theorem parse_serialize {i : Input} (h : i.WellFormed) : parse (serialize i) = some i := by
  unfold parse
  rw [decode_serialize h]
  exact if_pos ⟨h, rfl⟩

/-- Whatever parses is exactly a well-formed input's bytes: nothing is canonicalized. -/
theorem serialize_of_parse {bs : List UInt8} {i : Input} (h : parse bs = some i) :
    i.WellFormed ∧ serialize i = bs := by
  unfold parse at h
  cases hd : decode bs with
  | none => simp [hd] at h
  | some j =>
    simp only [hd] at h
    split at h
    · rename_i hc
      cases h
      exact hc
    · cases h

/-! ## Entries, position by position -/

/-- What `EntriesOk` says about one position. -/
theorem entryOk_at : ∀ (es prior : List InputEntry) (k : Nat) (e : InputEntry),
    EntriesOk prior es → es[k]? = some e → EntryOk (prior ++ es.take k) e
  | [], _, _, _, _, h => by simp at h
  | x :: xs, prior, 0, e, ⟨hx, _⟩, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simpa using hx
  | x :: xs, prior, k + 1, e, ⟨_, hxs⟩, h => by
    have := entryOk_at xs (prior ++ [x]) k e hxs (by simpa using h)
    simpa [List.take_succ_cons] using this

/-- And back: position-by-position facts give `EntriesOk`. -/
theorem entriesOk_of_at : ∀ (es prior : List InputEntry),
    (∀ k e, es[k]? = some e → EntryOk (prior ++ es.take k) e) → EntriesOk prior es
  | [], _, _ => trivial
  | x :: xs, prior, h => by
    refine ⟨by simpa using h 0 x (by simp), entriesOk_of_at xs (prior ++ [x]) ?_⟩
    intro k e he
    simpa [List.take_succ_cons] using h (k + 1) e (by simpa using he)

theorem keyFresh_mem {prior : List InputEntry} {k : Pubkey} {b : InputAccount}
    (h : keyFresh prior k = true) (hb : InputEntry.account b ∈ prior) : b.key ≠ k := by
  have := List.all_eq_true.mp h _ hb
  simpa using this

theorem keyFresh_of {prior : List InputEntry} {k : Pubkey}
    (h : ∀ b, InputEntry.account b ∈ prior → b.key ≠ k) : keyFresh prior k = true := by
  refine List.all_eq_true.mpr fun e he => ?_
  cases e with
  | account b => simpa using h b he
  | dup _ => rfl

/-- A record of a well-formed input is well formed. -/
theorem record_wellFormed {i : Input} (h : i.WellFormed) {k : Nat} {a : InputAccount}
    (he : i.entries[k]? = some (.account a)) : a.WellFormed :=
  (entryOk_at _ [] k _ h.2.1 he).1

/-- A duplicate names an earlier position, and that position holds a record. -/
theorem dup_target {i : Input} (h : i.WellFormed) {k p : Nat}
    (he : i.entries[k]? = some (.dup p)) :
    p < k ∧ ∃ a, i.entries[p]? = some (.account a) := by
  have hok := entryOk_at _ [] k _ h.2.1 he
  simp only [EntryOk, isRecordAt, List.nil_append, List.getElem?_take] at hok
  split at hok
  · rename_i a hget
    split at hget
    · rename_i hlt
      exact ⟨hlt, a, hget⟩
    · cases hget
  · cases hok

/-- No two records of a well-formed input share a key, so a key is one position. -/
theorem record_key_unique {i : Input} (h : i.WellFormed) {j k : Nat} {a b : InputAccount}
    (hj : i.entries[j]? = some (.account a)) (hk : i.entries[k]? = some (.account b))
    (hkey : a.key = b.key) : j = k := by
  have only_lt : ∀ {j k : Nat} {a b : InputAccount}, j < k →
      i.entries[j]? = some (.account a) → i.entries[k]? = some (.account b) → a.key ≠ b.key := by
    intro j k a b hlt hj hk
    have hok := (entryOk_at _ [] k _ h.2.1 hk).2
    refine keyFresh_mem hok ?_
    simp only [List.nil_append]
    refine List.mem_of_getElem? (i := j) ?_
    rw [List.getElem?_take, if_pos hlt]
    exact hj
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · exact absurd hkey (only_lt hlt hj hk)
  · exact heq
  · exact absurd hkey.symm (only_lt hgt hk hj)

/-! ## Duplicates alias their original -/

/-- The account a position refers to, through a duplicate if it is one. -/
def Input.resolve (i : Input) (k : Nat) : Option InputAccount :=
  match i.entries[resolveIdx i.entries k]? with
  | some (.account a) => some a
  | _ => none

/-- A duplicate and its original are one account. -/
theorem resolve_dup {i : Input} (h : i.WellFormed) {k p : Nat}
    (he : i.entries[k]? = some (.dup p)) :
    ∃ a, i.resolve k = some a ∧ i.resolve p = some a ∧ i.entries[p]? = some (.account a) := by
  obtain ⟨_, a, ha⟩ := dup_target h he
  refine ⟨a, ?_, ?_, ha⟩
  · simp [Input.resolve, resolveIdx, he, ha]
  · simp [Input.resolve, resolveIdx, ha]

/-- Every position of a well-formed input refers to an account. -/
theorem resolve_total {i : Input} (h : i.WellFormed) {k : Nat} (hk : k < i.entries.length) :
    ∃ a, i.resolve k = some a := by
  cases he : i.entries[k]'hk with
  | account a =>
    refine ⟨a, ?_⟩
    have hg : i.entries[k]? = some (.account a) := by simp [List.getElem?_eq_getElem hk, he]
    simp [Input.resolve, resolveIdx, hg]
  | dup p =>
    have hg : i.entries[k]? = some (.dup p) := by simp [List.getElem?_eq_getElem hk, he]
    obtain ⟨a, ha, _, _⟩ := resolve_dup h hg
    exact ⟨a, ha⟩

/-- A duplicate's pointer is its original's: both name the one record. -/
theorem pointer_dup {i : Input} (h : i.WellFormed) {k p : Nat}
    (he : i.entries[k]? = some (.dup p)) : pointer i.entries k = pointer i.entries p := by
  obtain ⟨_, a, ha⟩ := dup_target h he
  simp [pointer, resolveIdx, he, ha]

/-- Two positions with one key refer to one account, at one address. -/
theorem resolve_key_alias {i : Input} (h : i.WellFormed) {j k : Nat} {a b : InputAccount}
    (hj : i.resolve j = some a) (hk : i.resolve k = some b) (hkey : a.key = b.key) :
    a = b ∧ pointer i.entries j = pointer i.entries k := by
  have split : ∀ {x : Nat} {c : InputAccount}, i.resolve x = some c →
      i.entries[resolveIdx i.entries x]? = some (.account c) := by
    intro x c hx
    simp only [Input.resolve] at hx
    split at hx
    · rename_i y hy; cases hx; exact hy
    · cases hx
  have hja := split hj
  have hkb := split hk
  have heq := record_key_unique h hja hkb hkey
  rw [heq, hkb] at hja
  have hab : a = b := by simpa using hja.symm
  exact ⟨hab, by simp [pointer, heq]⟩

/-! ## Layout facts -/

theorem flatMap_length (es : List InputEntry) :
    (es.flatMap entryBytes).length = (es.map entrySize).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [List.flatMap_cons, entryBytes_length, ih]

theorem entrySize_mod (e : InputEntry) : entrySize e % 8 = 0 := by
  cases e with
  | account a =>
    have := alignPad_add a.state.data.length
    simp only [entrySize, recordSize, MAX_PERMITTED_DATA_INCREASE]
    omega
  | dup _ => simp [entrySize]

theorem sum_entrySize_mod (es : List InputEntry) : (es.map entrySize).sum % 8 = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have := entrySize_mod e
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Every position starts on an 8-byte boundary. -/
theorem slotOff_aligned (es : List InputEntry) (k : Nat) : slotOff es k % 8 = 0 := by
  have := sum_entrySize_mod (es.take k)
  simp only [slotOff]
  omega

/-- A record's data starts on an 8-byte boundary. -/
theorem dataOff_aligned (es : List InputEntry) (k : Nat) : (slotOff es k + DATA_OFF) % 8 = 0 := by
  have := slotOff_aligned es k
  simp only [DATA_OFF]
  omega

/-- So does its rent epoch, whatever the data length: this is what the padding is for. -/
theorem rentEpochOff_aligned (es : List InputEntry) (k dataLen : Nat) :
    (slotOff es k + rentEpochOff dataLen) % 8 = 0 := by
  have := slotOff_aligned es k
  have := alignPad_add dataLen
  simp only [rentEpochOff, MAX_PERMITTED_DATA_INCREASE]
  omega

theorem instrDataOff_aligned (es : List InputEntry) : instrDataOff es % 8 = 0 := by
  have := slotOff_aligned es es.length
  simp only [instrDataOff, instrLenOff]
  omega

/-- The pointer array starts on an 8-byte boundary, whatever the instruction data's length. -/
theorem pointersOff_aligned (es : List InputEntry) (ixLen : Nat) :
    pointersOff es ixLen % 8 = 0 := by
  have := instrDataOff_aligned es
  have := alignPad_add ixLen
  simp only [pointersOff, programIdOff]
  omega

theorem sum_take_le (es : List InputEntry) (k : Nat) :
    ((es.take k).map entrySize).sum ≤ (es.map entrySize).sum := by
  induction es generalizing k with
  | nil => simp
  | cons e es ih =>
    cases k with
    | zero => simp
    | succ k =>
      have := ih k
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

/-- An entry lies between its own offset and the trailer. -/
theorem slot_within {es : List InputEntry} {k : Nat} {e : InputEntry} (he : es[k]? = some e) :
    slotOff es k + entrySize e ≤ instrLenOff es := by
  have hk : k < es.length := (List.getElem?_eq_some_iff.mp he).1
  have hget : es[k] = e := (List.getElem?_eq_some_iff.mp he).2
  have htake : es.take (k + 1) = es.take k ++ [e] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, hget]; rfl
  have hle := sum_take_le es (k + 1)
  rw [htake] at hle
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hle
  simp only [slotOff, instrLenOff, List.take_length]
  omega

theorem pointerBytes_length (es : List InputEntry) : (pointerBytes es).length = 8 * es.length := by
  have : ∀ xs : List Nat, (xs.flatMap le64).length = 8 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.flatMap_cons, le64_length, ih]; omega
  simp [pointerBytes, this]

/-- The whole buffer's length. -/
theorem serialize_length (i : Input) :
    (serialize i).length = pointersOff i.entries i.instrData.length + 8 * i.entries.length := by
  simp [serialize, trailerBytes, le64_length, entryBytes_length, pubkeyBytes_length, zeros_length,
    pointerBytes_length, pointersOff, programIdOff, instrDataOff, instrLenOff, slotOff]
  have he : (i.entries.map (fun a => entrySize a)).sum = (i.entries.map entrySize).sum := rfl
  omega

/-! ## Each field is where the layout says -/

/-- The buffer from a position on. -/
theorem serialize_drop_slot (i : Input) {k : Nat} :
    (serialize i).drop (slotOff i.entries k) =
      (i.entries.drop k).flatMap entryBytes ++
        trailerBytes i.entries i.instrData i.programId := by
  have hsplit : serialize i = (le64 i.entries.length ++ (i.entries.take k).flatMap entryBytes) ++
      ((i.entries.drop k).flatMap entryBytes ++
        trailerBytes i.entries i.instrData i.programId) := by
    have h1 : i.entries.flatMap entryBytes =
        (i.entries.take k).flatMap entryBytes ++ (i.entries.drop k).flatMap entryBytes := by
      rw [← List.flatMap_append, List.take_append_drop]
    unfold serialize
    rw [h1]
    simp [List.append_assoc]
  rw [hsplit]
  exact drop_prefix (by simp [le64_length, entryBytes_length, slotOff])

/-- At a record's position is its bytes. -/
theorem serialize_record {i : Input} {k : Nat} {a : InputAccount}
    (he : i.entries[k]? = some (.account a)) :
    ∃ t, (serialize i).drop (slotOff i.entries k) = recordBytes a ++ t := by
  have hk : k < i.entries.length := (List.getElem?_eq_some_iff.mp he).1
  have hget : i.entries[k] = .account a := (List.getElem?_eq_some_iff.mp he).2
  refine ⟨(i.entries.drop (k + 1)).flatMap entryBytes ++
    trailerBytes i.entries i.instrData i.programId, ?_⟩
  rw [serialize_drop_slot, List.drop_eq_getElem_cons hk, hget, List.flatMap_cons, List.append_assoc]
  rfl

/-- The fields of the record at a position, read from the buffer. -/
theorem record_fields {i : Input} (h : i.WellFormed) {k : Nat} {a : InputAccount}
    (he : i.entries[k]? = some (.account a)) :
    let bs := serialize i
    let off := slotOff i.entries k
    rdKey (bs.drop (off + KEY_OFF)) = a.key ∧
    rdKey (bs.drop (off + OWNER_OFF)) = a.state.owner ∧
    rd64 (bs.drop (off + LAMPORTS_OFF)) = a.state.lamports ∧
    rd64 (bs.drop (off + DATA_LEN_OFF)) = a.state.data.length ∧
    (bs.drop (off + DATA_OFF)).take a.state.data.length = a.state.data ∧
    rd64 (bs.drop (off + rentEpochOff a.state.data.length)) = RENT_EPOCH_MASKED := by
  obtain ⟨hk, ho, hl, hd, hr⟩ := record_wellFormed h he
  obtain ⟨t, ht⟩ := serialize_record he
  intro bs off
  have hdb : Bounded a.state.data.length := by
    unfold Bounded MAX_PERMITTED_DATA_LENGTH at *; omega
  have hrb : Bounded a.state.rentEpoch := by rw [hr]; exact rentEpochMasked_bounded
  have hdrop : ∀ n, bs.drop (off + n) = (recordBytes a ++ t).drop n := by
    intro n
    rw [← ht, List.drop_drop]
  simp only [hdrop]
  rw [drop_key, drop_owner, drop_lamports, drop_dataLen, drop_data, drop_rent,
    rdKey_pubkeyBytes_append hk, rdKey_pubkeyBytes_append ho, rd64_le64_append hl,
    rd64_le64_append hdb, rd64_le64_append hrb, List.take_left' rfl, hr]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The buffer from the instruction data on. -/
theorem serialize_drop_instrData (i : Input) :
    (serialize i).drop (instrDataOff i.entries) = i.instrData ++
      (pubkeyBytes i.programId ++
        (zeros (alignPad i.instrData.length) ++ pointerBytes i.entries)) := by
  have htrail : (serialize i).drop (instrLenOff i.entries) =
      trailerBytes i.entries i.instrData i.programId := by
    have := serialize_drop_slot i (k := i.entries.length)
    simpa [List.drop_length] using this
  rw [instrDataOff, ← List.drop_drop, htrail]
  simp only [trailerBytes, List.append_assoc]
  exact drop_prefix (le64_length _)

/-- A u64 inside the instruction data is at its offset in the buffer. -/
theorem instrData_word (i : Input) {n : Nat} (hn : n + 8 ≤ i.instrData.length) :
    rd64 ((serialize i).drop (instrDataOff i.entries + n)) = rd64 (i.instrData.drop n) := by
  rw [← List.drop_drop, serialize_drop_instrData, List.drop_append_of_le_length (by omega)]
  unfold rd64
  exact rdN_append_left 8 _ _ (by simp; omega)

/-- The trailer, read from the buffer. -/
theorem trailer_fields {i : Input} (h : i.WellFormed) :
    let bs := serialize i
    let ix := i.instrData.length
    rd64 (bs.drop (instrLenOff i.entries)) = ix ∧
    (bs.drop (instrDataOff i.entries)).take ix = i.instrData ∧
    rdKey (bs.drop (programIdOff i.entries ix)) = i.programId := by
  obtain ⟨_, _, hix, hpid⟩ := h
  intro bs ix
  have htrail : bs.drop (instrLenOff i.entries) =
      trailerBytes i.entries i.instrData i.programId := by
    have := serialize_drop_slot i (k := i.entries.length)
    simpa [List.drop_length] using this
  have hd8 := serialize_drop_instrData i
  refine ⟨?_, ?_, ?_⟩
  · rw [htrail]
    simp only [trailerBytes, List.append_assoc]
    exact rd64_le64_append hix _
  · rw [hd8]; exact List.take_left' rfl
  · rw [programIdOff, ← List.drop_drop, hd8, drop_prefix rfl]
    exact rdKey_pubkeyBytes_append hpid _

theorem flatMap_le64_drop : ∀ (xs : List Nat) (k : Nat) (x : Nat), xs[k]? = some x →
    ∃ t, (xs.flatMap le64).drop (8 * k) = le64 x ++ t
  | [], _, _, h => by simp at h
  | y :: ys, 0, x, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨ys.flatMap le64, by simp [List.flatMap_cons]⟩
  | y :: ys, k + 1, x, h => by
    obtain ⟨t, ht⟩ := flatMap_le64_drop ys k x (by simpa using h)
    refine ⟨t, ?_⟩
    rw [List.flatMap_cons, Nat.mul_succ, Nat.add_comm, ← List.drop_drop,
      drop_prefix (le64_length y), ht]

/-- The size of the largest possible record. -/
def MAX_RECORD : Nat := recordSize MAX_PERMITTED_DATA_LENGTH + 8

theorem entriesOk_sum : ∀ (es prior : List InputEntry), EntriesOk prior es →
    (es.map entrySize).sum ≤ es.length * MAX_RECORD
  | [], _, _ => by simp
  | e :: es, prior, ⟨he, hes⟩ => by
    have ih := entriesOk_sum es (prior ++ [e]) hes
    have hsz : entrySize e ≤ MAX_RECORD := by
      cases e with
      | account a =>
        have hd := he.1.2.2.2.1
        simp only [entrySize, MAX_RECORD, recordSize, alignPad] at *
        omega
      | dup _ => simp [entrySize, MAX_RECORD, recordSize]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Every offset of a well-formed input is far inside the address space. -/
theorem slotOff_bounded {i : Input} (h : i.WellFormed) (k : Nat) :
    Bounded (MM_INPUT_START + slotOff i.entries k) := by
  have hle := sum_take_le i.entries k
  have hs := entriesOk_sum _ [] h.2.1
  have hn := h.1
  have hm : i.entries.length * MAX_RECORD ≤ MAX_ACCOUNTS * MAX_RECORD := Nat.mul_le_mul_right _ hn
  have hv : MAX_ACCOUNTS * MAX_RECORD < 2 ^ 40 := by decide
  unfold Bounded
  simp only [slotOff, MM_INPUT_START]
  omega

/-- The pointer array holds the address of each position's record. -/
theorem pointer_field {i : Input} (h : i.WellFormed) {k : Nat} (hk : k < i.entries.length) :
    rd64 ((serialize i).drop (pointersOff i.entries i.instrData.length + 8 * k)) =
      pointer i.entries k := by
  have htrail : (serialize i).drop (pointersOff i.entries i.instrData.length) =
      pointerBytes i.entries := by
    have hall := serialize_drop_slot i (k := i.entries.length)
    simp only [List.drop_length, List.flatMap_nil, List.nil_append] at hall
    have : pointersOff i.entries i.instrData.length =
        instrLenOff i.entries + (trailerBytes i.entries i.instrData i.programId).length -
          (pointerBytes i.entries).length := by
      simp [trailerBytes, le64_length, pubkeyBytes_length, zeros_length, pointersOff,
        programIdOff, instrDataOff]
      omega
    have hT : trailerBytes i.entries i.instrData i.programId =
        (le64 i.instrData.length ++ i.instrData ++ pubkeyBytes i.programId ++
          zeros (alignPad i.instrData.length)) ++ pointerBytes i.entries := by
      simp [trailerBytes, List.append_assoc]
    have hdrop : pointersOff i.entries i.instrData.length = instrLenOff i.entries +
        (le64 i.instrData.length ++ i.instrData ++ pubkeyBytes i.programId ++
          zeros (alignPad i.instrData.length)).length := by
      simp [le64_length, pubkeyBytes_length, zeros_length, pointersOff, programIdOff,
        instrDataOff]
      omega
    rw [hdrop, ← List.drop_drop]
    change ((serialize i).drop (slotOff i.entries i.entries.length)).drop _ = _
    rw [hall, hT]
    exact drop_prefix rfl
  rw [← List.drop_drop, htrail]
  have hget : ((List.range i.entries.length).map (pointer i.entries))[k]? =
      some (pointer i.entries k) := by simp [hk]
  obtain ⟨t, ht⟩ := flatMap_le64_drop _ k _ hget
  rw [pointerBytes, ht]
  exact rd64_le64_append (slotOff_bounded h _) _

/-! ## The earlier layout, when no account repeats -/

theorem recordSize_eq_acctSlotSize (n : Nat) : recordSize n = SVM.Solana.acctSlotSize n := by
  simp only [recordSize, alignPad, MAX_PERMITTED_DATA_INCREASE, SVM.Solana.acctSlotSize,
    SVM.Solana.ACCT_HEADER_SIZE, SVM.Solana.alignUp, SVM.Solana.MAX_PERMITTED_DATA_INCREASE]
  omega

/-- Without duplicates, `slotOff` is `SVM.Solana.acctSlotOff`. -/
theorem slotOff_records (as : List InputAccount) (k : Nat) :
    slotOff (as.map .account) k =
      SVM.Solana.acctSlotOff (as.map (·.state.data.length)) k := by
  have hs : ∀ (as : List InputAccount) (k : Nat),
      (((as.map InputEntry.account).take k).map entrySize).sum =
        (((as.map (·.state.data.length)).take k).map SVM.Solana.acctSlotSize).foldr (· + ·) 0 := by
    intro as k
    induction as generalizing k with
    | nil => simp
    | cons a as ih =>
      cases k with
      | zero => simp
      | succ k =>
        simp only [List.map_cons, List.take_succ_cons, List.sum_cons, List.foldr_cons]
        rw [ih k]
        simp only [entrySize, recordSize_eq_acctSlotSize]
  simp only [slotOff, SVM.Solana.acctSlotOff, SVM.Solana.ACCTS_COUNT_SIZE, hs]

theorem instrDataOff_records (as : List InputAccount) :
    instrDataOff (as.map .account) =
      SVM.Solana.instrDataOff (as.map (·.state.data.length)) := by
  simp [instrDataOff, instrLenOff, slotOff_records, SVM.Solana.instrDataOff,
    SVM.Solana.instrLenOff]

theorem dataOff_records (as : List InputAccount) (k : Nat) :
    slotOff (as.map .account) k + DATA_OFF =
      SVM.Solana.acctDataOff (as.map (·.state.data.length)) k := by
  simp [slotOff_records, SVM.Solana.acctDataOff, SVM.Solana.ACCT_HEADER_SIZE, DATA_OFF]

/-- Every offset `SVM.Solana.p_token_transfer_input_layout` anchors, from this file's layout:
    two 165-byte token accounts. -/
theorem p_token_transfer_abi_layout {a b : InputAccount} (ha : a.state.data.length = 165)
    (hb : b.state.data.length = 165) :
    let es := [InputEntry.account a, .account b]
    slotOff es 0 + DATA_OFF = 96 ∧ slotOff es 1 + DATA_OFF = 10600 ∧
      instrLenOff es = 21016 ∧ instrDataOff es = 21024 := by
  have hl : [a, b].map (·.state.data.length) = [165, 165] := by simp [ha, hb]
  have hes : [InputEntry.account a, .account b] = [a, b].map .account := rfl
  obtain ⟨h0, h1, h2, h3⟩ := SVM.Solana.p_token_transfer_input_layout
  intro es
  have hinstr : instrLenOff es + 8 = 21024 := by
    have := instrDataOff_records [a, b]
    rw [hl, h3] at this
    exact this
  refine ⟨?_, ?_, by omega, hinstr⟩
  · have := dataOff_records [a, b] 0
    rw [hl, h0] at this
    exact this
  · have := dataOff_records [a, b] 1
    rw [hl, h1] at this
    exact this

/-! ## How the runtime builds an input -/

/-- One `AccountMeta`. -/
structure InputMeta where
  key        : Pubkey
  isSigner   : Bool
  isWritable : Bool
  deriving Repr, DecidableEq

/-- The first position of a key. -/
def firstRef (ms : List InputMeta) (key : Pubkey) : Nat :=
  ms.findIdx fun m => decide (m.key = key)

/-- The record of a key: its flags are the OR over the key's references, since the
    runtime compiles the instruction's metas by key before it serializes. -/
def recordOf (ms : List InputMeta) (acct : Pubkey → AccountState) (key : Pubkey) : InputAccount :=
  { key
    isSigner := ms.any fun m => decide (m.key = key) && m.isSigner
    isWritable := ms.any fun m => decide (m.key = key) && m.isWritable
    state := { acct key with rentEpoch := RENT_EPOCH_MASKED } }

def entryOf (ms : List InputMeta) (acct : Pubkey → AccountState) (k : Nat) (m : InputMeta) :
    InputEntry :=
  if firstRef ms m.key < k then .dup (firstRef ms m.key) else .account (recordOf ms acct m.key)

/-- The input for an instruction. Duplicates follow from the metas' keys. -/
def ofInstruction (ms : List InputMeta) (acct : Pubkey → AccountState) (data : List UInt8)
    (pid : Pubkey) : Input :=
  { entries := ms.mapIdx (entryOf ms acct)
    instrData := data
    programId := pid }

private theorem findIdx_le {p : InputMeta → Bool} : ∀ (ms : List InputMeta) (k : Nat)
    (m : InputMeta), ms[k]? = some m → p m = true → ms.findIdx p ≤ k
  | [], _, _, h, _ => by simp at h
  | x :: xs, 0, m, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [List.findIdx_cons, hp]
  | x :: xs, k + 1, m, h, hp => by
    have := findIdx_le xs k m (by simpa using h) hp
    rw [List.findIdx_cons]
    cases p x <;> simp <;> omega

private theorem findIdx_at {p : InputMeta → Bool} : ∀ (ms : List InputMeta) (k : Nat)
    (m : InputMeta), ms[k]? = some m → p m = true →
    ∃ m', ms[ms.findIdx p]? = some m' ∧ p m' = true
  | [], _, _, h, _ => by simp at h
  | x :: xs, 0, m, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨x, by simp [List.findIdx_cons, hp], hp⟩
  | x :: xs, k + 1, m, h, hp => by
    rw [List.findIdx_cons]
    cases hx : p x with
    | true => exact ⟨x, by simp, hx⟩
    | false =>
      obtain ⟨m', hm', hpm⟩ := findIdx_at xs k m (by simpa using h) hp
      exact ⟨m', by simpa using hm', hpm⟩

theorem firstRef_le {ms : List InputMeta} {k : Nat} {m : InputMeta} (h : ms[k]? = some m) :
    firstRef ms m.key ≤ k :=
  findIdx_le ms k m h (by simp)

/-- The first position of a key holds that key, and is its own first position. -/
theorem firstRef_at {ms : List InputMeta} {k : Nat} {m : InputMeta} (h : ms[k]? = some m) :
    ∃ m', ms[firstRef ms m.key]? = some m' ∧ m'.key = m.key := by
  obtain ⟨m', hm', hp⟩ := findIdx_at (p := fun x => decide (x.key = m.key)) ms k m h (by simp)
  exact ⟨m', hm', by simpa using hp⟩

theorem entries_at {ms : List InputMeta} {acct : Pubkey → AccountState} {data : List UInt8}
    {pid : Pubkey} {k : Nat} {m : InputMeta} (h : ms[k]? = some m) :
    (ofInstruction ms acct data pid).entries[k]? = some (entryOf ms acct k m) := by
  simp [ofInstruction, List.getElem?_mapIdx, h]

/-- What an instruction must supply for the runtime to build its input. -/
def StatesOk (ms : List InputMeta) (acct : Pubkey → AccountState) : Prop :=
  ∀ m ∈ ms, PubkeyBounded m.key ∧ PubkeyBounded (acct m.key).owner ∧
    Bounded (acct m.key).lamports ∧ (acct m.key).data.length ≤ MAX_PERMITTED_DATA_LENGTH

/-- An instruction's input is well formed. -/
theorem ofInstruction_wellFormed {ms : List InputMeta} {acct : Pubkey → AccountState}
    {data : List UInt8} {pid : Pubkey} (hn : ms.length ≤ MAX_ACCOUNTS) (hs : StatesOk ms acct)
    (hd : Bounded data.length) (hp : PubkeyBounded pid) :
    (ofInstruction ms acct data pid).WellFormed := by
  refine ⟨by simpa [ofInstruction] using hn, ?_, hd, hp⟩
  refine entriesOk_of_at _ _ fun k e he => ?_
  simp only [List.nil_append]
  have hkl : k < ms.length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simpa [ofInstruction] using this
  have hm : ms[k]? = some ms[k] := List.getElem?_eq_getElem hkl
  generalize ms[k] = m at hm
  rw [entries_at hm] at he
  cases he
  have hmem : m ∈ ms := List.mem_of_getElem? hm
  have hle := firstRef_le hm
  obtain ⟨m', hm', hkey⟩ := firstRef_at hm
  by_cases hlt : firstRef ms m.key < k
  · have hkey' : firstRef ms m'.key = firstRef ms m.key := by rw [hkey]
    simp only [entryOf, if_pos hlt, EntryOk, isRecordAt]
    rw [List.getElem?_take, if_pos hlt, entries_at hm']
    simp [entryOf, hkey']
  · simp only [entryOf, if_neg hlt, EntryOk]
    obtain ⟨h1, h2, h3, h4⟩ := hs m hmem
    refine ⟨⟨h1, h2, h3, h4, rfl⟩, keyFresh_of fun b hb hbk => ?_⟩
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hb
    have hjk : j < k := by
      rw [List.getElem?_take] at hj
      split at hj
      · assumption
      · cases hj
    rw [List.getElem?_take, if_pos hjk] at hj
    have hjl : j < ms.length := by omega
    have hmj : ms[j]? = some ms[j] := List.getElem?_eq_getElem hjl
    generalize ms[j] = mj at hmj
    rw [entries_at hmj] at hj
    simp only [Option.some.injEq, entryOf] at hj
    split at hj
    · cases hj
    · cases hj
      have hjkey : mj.key = m.key := hbk
      have := firstRef_le hmj
      rw [hjkey] at this
      omega

/-- Every reference to a key resolves to that key's record, duplicate or not. -/
theorem ofInstruction_resolve {ms : List InputMeta} {acct : Pubkey → AccountState}
    {data : List UInt8} {pid : Pubkey} {k : Nat} {m : InputMeta} (h : ms[k]? = some m) :
    (ofInstruction ms acct data pid).resolve k = some (recordOf ms acct m.key) := by
  obtain ⟨m', hm', hkey⟩ := firstRef_at h
  have hkey' : firstRef ms m'.key = firstRef ms m.key := by rw [hkey]
  have hfirst := entries_at (acct := acct) (data := data) (pid := pid) hm'
  have hrec : entryOf ms acct (firstRef ms m.key) m' = .account (recordOf ms acct m.key) := by
    simp [entryOf, hkey]
  rw [hrec] at hfirst
  have he := entries_at (acct := acct) (data := data) (pid := pid) h
  by_cases hlt : firstRef ms m.key < k
  · simp only [entryOf, if_pos hlt] at he
    simp [Input.resolve, resolveIdx, he, hfirst]
  · have heq : firstRef ms m.key = k := by
      have := firstRef_le h
      omega
    simp only [entryOf, if_neg hlt] at he
    simp [Input.resolve, resolveIdx, he]

/-- Two references to one key are one account. -/
theorem ofInstruction_alias {ms : List InputMeta} {acct : Pubkey → AccountState}
    {data : List UInt8} {pid : Pubkey} {j k : Nat} {mj mk : InputMeta}
    (hj : ms[j]? = some mj) (hk : ms[k]? = some mk) (hkey : mj.key = mk.key) :
    (ofInstruction ms acct data pid).resolve j = (ofInstruction ms acct data pid).resolve k := by
  rw [ofInstruction_resolve hj, ofInstruction_resolve hk, hkey]

/-- An account is writable in the input iff any of its references is, whichever came first. -/
theorem ofInstruction_isWritable {ms : List InputMeta} {acct : Pubkey → AccountState}
    {data : List UInt8} {pid : Pubkey} {k : Nat} {m : InputMeta} (h : ms[k]? = some m) :
    ∃ a, (ofInstruction ms acct data pid).resolve k = some a ∧
      (a.isWritable = true ↔ ∃ r ∈ ms, r.key = m.key ∧ r.isWritable = true) := by
  refine ⟨_, ofInstruction_resolve h, ?_⟩
  simp [recordOf]

/-- An account signs in the input iff any of its references does. -/
theorem ofInstruction_isSigner {ms : List InputMeta} {acct : Pubkey → AccountState}
    {data : List UInt8} {pid : Pubkey} {k : Nat} {m : InputMeta} (h : ms[k]? = some m) :
    ∃ a, (ofInstruction ms acct data pid).resolve k = some a ∧
      (a.isSigner = true ↔ ∃ r ∈ ms, r.key = m.key ∧ r.isSigner = true) := by
  refine ⟨_, ofInstruction_resolve h, ?_⟩
  simp [recordOf]

end SVM.Runtime
