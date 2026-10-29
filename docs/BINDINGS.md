# Discovered success-proof bindings

`qed-discover` reads a same-build binary pair and its concept map. It writes the
inputs that the success-proof generator needs. A person no longer enters them by
hand ([solana-skills#450](https://github.com/QEDGen/solana-skills/issues/450)).

```sh
cd qedsvm-rs
cargo run -p qed-analysis --bin qed-concept-map -- prog.so prog.debug.so > prog.concepts.json
cargo run -p qed-analysis --bin qed-discover -- prog.so prog.debug.so prog.concepts.json > prog.bindings.json
```

The tool refuses before it writes anything when the concept map does not
describe both binaries.

## Trust

Every value is an untrusted proposal (`"trust": "untrusted_discovered_bindings"`).
The generated Lean re-checks each PC, guard, route cut, no-return chain and input
pin against the decoded program. Names (handlers, fields) are labels. No theorem
depends on a name.

## JSON contract, version 1

- `schema_version`: `1`. Unknown versions and unknown fields are rejected.
- `artifact_sha256`, `debug_sha256`: the binary pair.
- `entry`: the logical entry PC.
- `noreturn`: a witness for `SVM.SBPF.noRetCheck`. `heads` are the helpers that never
  return. `steps` are `straight`, `call_local`, `branch` and `panic_call` steps, in the
  order the Lean check accepts them. `skipped` lists no-return helpers the check cannot
  model, with the reason.
- `instructions`: one entry per discriminator the dispatcher compares the first
  instruction-data byte with. `routes` are the dispatch-arm PCs. `handler` is a label
  from the concept map, or `null`. `success_edges` are the loop-free success edges the
  instruction reaches.
- `edges`: one entry per supported success edge.
  - `accounts`: the account count the program checks.
  - `assumed`: one `data_len` word per account. `checked: true` means every path to the
    edge checks `data_len == value` (at `guard_pcs`). `checked: false` means the program
    does not check it, and the theorem assumes `value` (0). Both kinds are hypotheses of
    the generated theorem.
  - `instruction_data`: the input offset of the first instruction-data byte under those
    lengths.
  - `non_duplicate`: accounts whose duplicate marker every path checks.
  - `routes`: per dispatch arm, the accounts whose `is_signer` byte is checked, and the
    key compares (an account's key against 32 bytes of another account's data).
  - `fields`: account-data offsets that guards read, with a DWARF member name when one
    struct fits. A refused label has `name: null` and the reason in `refused`.
- `unsupported`: success edges with no proof, and why: `loop`, an unpinned
  discriminator, or no dispatch arm that cuts every path.
- `diagnostics`: refused labels and skipped helpers.

## Limits

- The path layer only sees guards in the entry function. A handler in a function that
  returns is opaque. Programs must inline their handlers (p_token does).
- Routes have one level. Alternatives inside one instruction (owner, delegate or
  multisig authority) are not dominating, so they are not reported.
- Every theorem covers only inputs with the stated account lengths. Unchecked lengths
  are assumed 0.
- A loop anywhere on the way to a shared success edge marks every instruction on that
  edge unsupported.
- No concrete run yet shows that a theorem's hypotheses are satisfiable.
- sBPF V0 only, like the success-proof emitter.
