/-
  Abstract Solana state for spec-to-asm refinement (Direction-A MIR, qedgen #66).

  The ABSTRACT side: reasoning over decoded account records, not byte ranges in
  `SVM.SBPF.Memory.Mem`. The CONCRETE side is the sBPF `PartialState`
  (`SVM/SBPF/SepLogic.lean`); the bridge is `Abstract/Refinement.lean`, an
  abstraction relation matching abstract accounts to concrete bytes at a layout
  offset.

  Extension protocol: add fields only when a consumer needs them. These records
  back the byte-level codecs the discharge route reshapes.
-/

import SVM.Pubkey

namespace SVM.Solana.Abstract

open SVM.Pubkey

/-! ## TokenAccount — decoded SPL Token v4 account.

Abstract-side counterpart of the byte-level Pack codec `tokenAcctBalance`
(`SVM.Solana.TokenAccount`). `rest` carries the opaque 93-byte tail (delegate /
state / is_native / delegated_amount / close_authority) as one flow-through
field; the mint/owner/amount triple is what Transfer-class theorems mutate. -/

structure TokenAccount where
  mint   : Pubkey
  owner  : Pubkey
  amount : Nat
  rest   : ByteArray
  deriving Inhabited

namespace TokenAccount

/-- Adjust the `amount` field, preserving everything else. -/
def withAmount (t : TokenAccount) (a : Nat) : TokenAccount :=
  { t with amount := a }

@[simp] theorem withAmount_amount (t : TokenAccount) (a : Nat) :
    (t.withAmount a).amount = a := rfl
@[simp] theorem withAmount_mint (t : TokenAccount) (a : Nat) :
    (t.withAmount a).mint = t.mint := rfl
@[simp] theorem withAmount_owner (t : TokenAccount) (a : Nat) :
    (t.withAmount a).owner = t.owner := rfl
@[simp] theorem withAmount_rest (t : TokenAccount) (a : Nat) :
    (t.withAmount a).rest = t.rest := rfl

end TokenAccount

/-! ## Mint — decoded SPL Token mint account.

Abstract-side counterpart of `mintAcctSupply` (`SVM.Solana.MintAccountCodec`).
Only `supply` is mutated by MintTo/Burn; `preAuth` (36-byte `COption<Pubkey>`
mint_authority) and `rest` (38-byte decimals/is_initialized/freeze_authority
tail) flow through opaque. `supply` sits at offset 36 (after `preAuth`), so it
can't be a single trailing field the way `TokenAccount.rest` is. -/

structure Mint where
  preAuth : ByteArray
  supply  : Nat
  rest    : ByteArray
  deriving Inhabited

namespace Mint

/-- Adjust the `supply` field, preserving everything else. -/
def withSupply (m : Mint) (s : Nat) : Mint :=
  { m with supply := s }

@[simp] theorem withSupply_supply (m : Mint) (s : Nat) :
    (m.withSupply s).supply = s := rfl
@[simp] theorem withSupply_preAuth (m : Mint) (s : Nat) :
    (m.withSupply s).preAuth = m.preAuth := rfl
@[simp] theorem withSupply_rest (m : Mint) (s : Nat) :
    (m.withSupply s).rest = m.rest := rfl

end Mint

/-! ## CounterAccount — decoded single-field counter account.

Abstract-side record for a NON-token program (codec `counterValOf` in
`CounterAccountCodec` is the bare `u64` at the account-data offset). Validates
the refinement machinery is layout-general, not SPL-token-shaped. -/

structure CounterAccount where
  counter : Nat
  deriving Inhabited

namespace CounterAccount

/-- Adjust the `counter` field. -/
def withCounter (c : CounterAccount) (n : Nat) : CounterAccount :=
  { c with counter := n }

@[simp] theorem withCounter_counter (c : CounterAccount) (n : Nat) :
    (c.withCounter n).counter = n := rfl

end CounterAccount

/-! ## AbstractState — partial heap of decoded accounts.

Three resource maps: `accounts`, `mints`, `counters`. Grows as later pilots
demand new resources (`signers`, `ixData`, `returnData`, `cuRemaining`, ...). -/

structure AbstractState where
  accounts : Pubkey → Option TokenAccount
  mints    : Pubkey → Option Mint
  counters : Pubkey → Option CounterAccount
  deriving Inhabited

namespace AbstractState

/-- The empty abstract state owns no accounts. -/
def empty : AbstractState :=
  { accounts := fun _ => none, mints := fun _ => none, counters := fun _ => none }

@[simp] theorem empty_accounts (k : Pubkey) :
    empty.accounts k = none := rfl

@[simp] theorem empty_mints (k : Pubkey) :
    empty.mints k = none := rfl

@[simp] theorem empty_counters (k : Pubkey) :
    empty.counters k = none := rfl

/-- Read the account at `key`. Defeq `s.accounts key`; named accessor aids
    `simp` rewriting. -/
@[inline] def get (s : AbstractState) (key : Pubkey) : Option TokenAccount :=
  s.accounts key

/-- Install `t` at `key`, leaving every other key (and all mints) unchanged. -/
def set (s : AbstractState) (key : Pubkey) (t : TokenAccount) : AbstractState :=
  { s with accounts := fun k => if k = key then some t else s.accounts k }

@[simp] theorem set_get_eq (s : AbstractState) (key : Pubkey) (t : TokenAccount) :
    (s.set key t).get key = some t := by
  unfold set get; simp

@[simp] theorem set_get_of_ne (s : AbstractState) {key key' : Pubkey}
    (t : TokenAccount) (h : key' ≠ key) :
    (s.set key t).get key' = s.get key' := by
  unfold set get; simp [h]

/-- Field-level `.accounts` variant of `set_get_eq`, for proofs that
    pattern-match on the raw field rather than `.get`. -/
@[simp] theorem set_accounts_eq (s : AbstractState) (key : Pubkey) (t : TokenAccount) :
    (s.set key t).accounts key = some t := by
  unfold set; simp

@[simp] theorem set_accounts_of_ne (s : AbstractState) {key key' : Pubkey}
    (t : TokenAccount) (h : key' ≠ key) :
    (s.set key t).accounts key' = s.accounts key' := by
  unfold set; simp [h]

/-- Apply `f` to the account at `key`; no-op if absent. The Transfer balance
    shift lands here: `s.update from (·.withAmount (preA - x))`. -/
def update (s : AbstractState) (key : Pubkey) (f : TokenAccount → TokenAccount) :
    AbstractState :=
  match s.get key with
  | some t => s.set key (f t)
  | none   => s

@[simp] theorem update_get_eq (s : AbstractState) (key : Pubkey)
    (f : TokenAccount → TokenAccount) (t : TokenAccount) (h : s.get key = some t) :
    (s.update key f).get key = some (f t) := by
  unfold update; rw [h]; exact set_get_eq s key (f t)

@[simp] theorem update_get_of_ne (s : AbstractState) {key key' : Pubkey}
    (f : TokenAccount → TokenAccount) (h : key' ≠ key) :
    (s.update key f).get key' = s.get key' := by
  unfold update
  cases hk : s.get key with
  | some t => exact set_get_of_ne s (f t) h
  | none   => rfl

/-- Setting a token account leaves the mint heap unchanged. -/
@[simp] theorem set_mints (s : AbstractState) (key : Pubkey) (t : TokenAccount) :
    (s.set key t).mints = s.mints := rfl

/-- Setting a token account leaves the counter heap unchanged. -/
@[simp] theorem set_counters (s : AbstractState) (key : Pubkey) (t : TokenAccount) :
    (s.set key t).counters = s.counters := rfl

/-! ### Mint heap accessors (mirror the token-account ones) -/

/-- Read the mint at `key`, if any. -/
@[inline] def getMint (s : AbstractState) (key : Pubkey) : Option Mint :=
  s.mints key

/-- Install mint `m` at `key`, leaving other keys and all token accounts
    unchanged. -/
def setMint (s : AbstractState) (key : Pubkey) (m : Mint) : AbstractState :=
  { s with mints := fun k => if k = key then some m else s.mints k }

@[simp] theorem setMint_getMint_eq (s : AbstractState) (key : Pubkey) (m : Mint) :
    (s.setMint key m).getMint key = some m := by
  unfold setMint getMint; simp

@[simp] theorem setMint_getMint_of_ne (s : AbstractState) {key key' : Pubkey}
    (m : Mint) (h : key' ≠ key) :
    (s.setMint key m).getMint key' = s.getMint key' := by
  unfold setMint getMint; simp [h]

@[simp] theorem setMint_mints_eq (s : AbstractState) (key : Pubkey) (m : Mint) :
    (s.setMint key m).mints key = some m := by
  unfold setMint; simp

@[simp] theorem setMint_mints_of_ne (s : AbstractState) {key key' : Pubkey}
    (m : Mint) (h : key' ≠ key) :
    (s.setMint key m).mints key' = s.mints key' := by
  unfold setMint; simp [h]

/-- Setting a mint leaves the token-account heap unchanged. -/
@[simp] theorem setMint_accounts (s : AbstractState) (key : Pubkey) (m : Mint) :
    (s.setMint key m).accounts = s.accounts := rfl

/-- Apply `f` to the mint at `key`, if it exists. No-op if absent. -/
def updateMint (s : AbstractState) (key : Pubkey) (f : Mint → Mint) :
    AbstractState :=
  match s.getMint key with
  | some m => s.setMint key (f m)
  | none   => s

@[simp] theorem updateMint_getMint_eq (s : AbstractState) (key : Pubkey)
    (f : Mint → Mint) (m : Mint) (h : s.getMint key = some m) :
    (s.updateMint key f).getMint key = some (f m) := by
  unfold updateMint; rw [h]; exact setMint_getMint_eq s key (f m)

@[simp] theorem updateMint_getMint_of_ne (s : AbstractState) {key key' : Pubkey}
    (f : Mint → Mint) (h : key' ≠ key) :
    (s.updateMint key f).getMint key' = s.getMint key' := by
  unfold updateMint
  cases hk : s.getMint key with
  | some m => exact setMint_getMint_of_ne s (f m) h
  | none   => rfl

/-- Setting a mint leaves the counter heap unchanged. -/
@[simp] theorem setMint_counters (s : AbstractState) (key : Pubkey) (m : Mint) :
    (s.setMint key m).counters = s.counters := rfl

/-! ### Counter heap accessors (mirror the token-account / mint ones) -/

/-- Read the counter at `key`, if any. -/
@[inline] def getCounter (s : AbstractState) (key : Pubkey) : Option CounterAccount :=
  s.counters key

/-- Install counter `c` at `key`, leaving other keys and all token accounts /
    mints unchanged. -/
def setCounter (s : AbstractState) (key : Pubkey) (c : CounterAccount) : AbstractState :=
  { s with counters := fun k => if k = key then some c else s.counters k }

@[simp] theorem setCounter_getCounter_eq (s : AbstractState) (key : Pubkey) (c : CounterAccount) :
    (s.setCounter key c).getCounter key = some c := by
  unfold setCounter getCounter; simp

@[simp] theorem setCounter_getCounter_of_ne (s : AbstractState) {key key' : Pubkey}
    (c : CounterAccount) (h : key' ≠ key) :
    (s.setCounter key c).getCounter key' = s.getCounter key' := by
  unfold setCounter getCounter; simp [h]

@[simp] theorem setCounter_counters_eq (s : AbstractState) (key : Pubkey) (c : CounterAccount) :
    (s.setCounter key c).counters key = some c := by
  unfold setCounter; simp

@[simp] theorem setCounter_counters_of_ne (s : AbstractState) {key key' : Pubkey}
    (c : CounterAccount) (h : key' ≠ key) :
    (s.setCounter key c).counters key' = s.counters key' := by
  unfold setCounter; simp [h]

/-- Setting a counter leaves the token-account heap unchanged. -/
@[simp] theorem setCounter_accounts (s : AbstractState) (key : Pubkey) (c : CounterAccount) :
    (s.setCounter key c).accounts = s.accounts := rfl

/-- Setting a counter leaves the mint heap unchanged. -/
@[simp] theorem setCounter_mints (s : AbstractState) (key : Pubkey) (c : CounterAccount) :
    (s.setCounter key c).mints = s.mints := rfl

/-- Apply `f` to the counter at `key`, if it exists. No-op if absent. -/
def updateCounter (s : AbstractState) (key : Pubkey) (f : CounterAccount → CounterAccount) :
    AbstractState :=
  match s.getCounter key with
  | some c => s.setCounter key (f c)
  | none   => s

@[simp] theorem updateCounter_getCounter_eq (s : AbstractState) (key : Pubkey)
    (f : CounterAccount → CounterAccount) (c : CounterAccount) (h : s.getCounter key = some c) :
    (s.updateCounter key f).getCounter key = some (f c) := by
  unfold updateCounter; rw [h]; exact setCounter_getCounter_eq s key (f c)

@[simp] theorem updateCounter_getCounter_of_ne (s : AbstractState) {key key' : Pubkey}
    (f : CounterAccount → CounterAccount) (h : key' ≠ key) :
    (s.updateCounter key f).getCounter key' = s.getCounter key' := by
  unfold updateCounter
  cases hk : s.getCounter key with
  | some c => exact setCounter_getCounter_of_ne s (f c) h
  | none   => rfl

end AbstractState
end SVM.Solana.Abstract
