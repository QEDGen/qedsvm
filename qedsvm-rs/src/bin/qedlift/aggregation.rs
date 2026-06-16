// -----------------------------------------------------------------------------
// Account-aggregation codegen: emits `*_account_eq` lemmas from the IDL layout
// + owned-byte pattern via `rest_segments` (generic, not lift-var-specific).
// -----------------------------------------------------------------------------

enum RestSeg {
    Byte(i64),
    Gap { off: i64, len: i64 },
}

/// Segment `[start, end)` by sorted owned byte offsets: owned -> `Byte`, spans -> `Gap`.
fn rest_segments(owned: &[i64], start: i64, end: i64) -> Vec<RestSeg> {
    let mut segs = Vec::new();
    let mut cur = start;
    for &b in owned {
        if b > cur {
            segs.push(RestSeg::Gap { off: cur, len: b - cur });
        }
        segs.push(RestSeg::Byte(b));
        cur = b + 1;
    }
    if cur < end {
        segs.push(RestSeg::Gap { off: cur, len: end - cur });
    }
    segs
}

/// Emit one `tokenAcctBalanceOf` aggregation lemma for an account owning `owned` rest-bytes.
/// `owner_owned`: lift read the owner (else framed via `o0..o3`). `gap_ctr`: cross-lemma numbering.
fn render_token_agg_lemma(
    name: &str,
    owner_owned: bool,
    owned: &[i64],
    rest_start: i64,
    size: i64,
    gap_ctr: &mut u32,
) -> String {
    let segs = rest_segments(owned, rest_start, size);
    let mut gap_name: Vec<(usize, String)> = Vec::new(); // (seg idx, gN)
    for (i, s) in segs.iter().enumerate() {
        if let RestSeg::Gap { .. } = s {
            *gap_ctr += 1;
            gap_name.push((i, format!("g{}", gap_ctr)));
        }
    }
    let gname = |idx: usize| gap_name.iter().find(|(i, _)| *i == idx).unwrap().1.clone();
    let byte_offs: Vec<i64> = segs
        .iter()
        .filter_map(|s| {
            if let RestSeg::Byte(o) = s {
                Some(*o)
            } else {
                None
            }
        })
        .collect();

    let byte_vars: Vec<String> = byte_offs.iter().map(|o| format!("b{}", o)).collect();
    let gap_vars: Vec<String> = gap_name.iter().map(|(_, g)| g.clone()).collect();
    let nat_params = {
        let mut p = vec![
            "base".to_string(),
            "c0".into(),
            "c1".into(),
            "c2".into(),
            "c3".into(),
            "o0".into(),
            "o1".into(),
            "o2".into(),
            "o3".into(),
            "amount".into(),
        ];
        p.extend(byte_vars.clone());
        p.join(" ")
    };
    // Hyps: non-last gaps need a size hyp; each owned byte needs `< 256`.
    let last = segs.len().saturating_sub(1);
    let mut hyps: Vec<String> = Vec::new();
    let mut size_hyps: Vec<String> = Vec::new();
    for (i, s) in segs.iter().enumerate() {
        if let RestSeg::Gap { len, .. } = s {
            if i != last {
                let g = gname(i);
                hyps.push(format!("(h{} : {}.size = {})", g, g, len));
                size_hyps.push(format!("h{}", g));
            }
        }
    }
    for o in &byte_offs {
        hyps.push(format!("(h{} : b{} < 256)", o, o));
    }

    let term = |s: &RestSeg, i: usize| match s {
        RestSeg::Byte(o) => format!("PartialState.byteBA b{}", o),
        RestSeg::Gap { .. } => gname(i),
    };
    let chain = {
        let parts: Vec<String> = segs.iter().enumerate().map(|(i, s)| term(s, i)).collect();
        let mut acc = parts.last().cloned().unwrap_or_else(|| "ByteArray.empty".into());
        for p in parts.iter().rev().skip(1) {
            // Parenthesise only a compound tail; an atomic tail stays bare.
            acc = if acc.contains(" ++ ") {
                format!("{} ++ ({})", p, acc)
            } else {
                format!("{} ++ {}", p, acc)
            };
        }
        acc
    };
    let fine: Vec<String> = segs
        .iter()
        .enumerate()
        .map(|(i, s)| match s {
            RestSeg::Byte(o) => format!("memByteIs (base + {}) b{}", o, o),
            RestSeg::Gap { off, .. } => format!("memBytesIs (base + {}) {}", off, gname(i)),
        })
        .collect();
    let seg_list: Vec<String> = segs
        .iter()
        .enumerate()
        .map(|(i, s)| match s {
            RestSeg::Byte(o) => format!(".byte b{}", o),
            RestSeg::Gap { .. } => format!(".gap {}", gname(i)),
        })
        .collect();
    let mut bounds: Vec<String> = segs
        .iter()
        .map(|s| match s {
            RestSeg::Byte(o) => format!("h{}", o),
            RestSeg::Gap { .. } => "trivial".to_string(),
        })
        .collect();
    bounds.push("trivial".to_string()); // nil case
    let simp_sizes = if size_hyps.is_empty() {
        String::new()
    } else {
        format!("{}, ", size_hyps.join(", "))
    };

    let _ = owner_owned; // owner is always spelled via o0..o3 params either way
    format!(
"theorem {name}
    ({nat_params} : Nat)
    ({gaps} : ByteArray){hyps} :
    tokenAcctBalanceOf base
      {{ mint := ⟨c0, c1, c2, c3⟩, owner := ⟨o0, o1, o2, o3⟩, amount := amount,
        rest := {chain} }}
      = ( pubkeyIs base ⟨c0, c1, c2, c3⟩ **
          pubkeyIs (base + 32) ⟨o0, o1, o2, o3⟩ **
          memU64Is (base + 64) amount **
          ( {fine} ) ) := by
  funext h
  apply propext
  simp only [tokenAcctBalanceOf, tokenAcctBalance, MINT_OFF, OWNER_OFF, AMOUNT_OFF,
    REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
  have key := memBytesIs_segs (base + {rest_start})
    [{seg_list}]
    ⟨{bounds}⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    {simp_sizes}ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key",
        name = name,
        nat_params = nat_params,
        gaps = gap_vars.join(" "),
        hyps = if hyps.is_empty() {
            String::new()
        } else {
            format!(" {}", hyps.join(" "))
        },
        chain = chain,
        fine = fine.join(" **\n            "),
        rest_start = rest_start,
        seg_list = seg_list.join(", "),
        bounds = bounds.join(", "),
        simp_sizes = simp_sizes,
    )
}

/// Emit the token-aggregation module. `accounts` = `(lemma_name, owner_owned, owned_bytes)`.
pub(super) fn render_token_agg_module(
    ns: &str,
    accounts: &[(&str, bool, Vec<i64>)],
    rest_start: i64,
    size: i64,
) -> String {
    let mut gap_ctr = 0u32;
    let lemmas: Vec<String> = accounts
        .iter()
        .map(|(name, owner_owned, owned)| {
            render_token_agg_lemma(name, *owner_owned, owned, rest_start, size, &mut gap_ctr)
        })
        .collect();
    format!(
"/-
  Account-codec aggregation for token-account lifts.
  MECHANICALLY EMITTED by qedlift from the IDL account layout + the lift's
  owned-byte pattern (general `rest_segments`; the proof is a fixed
  `memBytesIs_segs` instance). Do not edit by hand.
-/

import SVM.SBPF.SegAggregation
import SVM.SBPF.PubkeySL
import SVM.Solana.TokenAccountCodec

namespace {ns}

open SVM.SBPF SVM.Solana

{lemmas}

end {ns}
",
        ns = ns,
        lemmas = lemmas.join("\n\n")
    )
}

/// Emit the mint-aggregation module (`mint_account_eq` full preAuth, `mint_supply_eq` opaque
/// preAuth, `dest_account_eq` token). SPL `COption<Pubkey>` at [0,36), supply at `supply_off`.
pub(super) fn render_mint_agg_module(
    ns: &str,
    supply_off: i64,
    rest_off: i64,
    mint_size: i64,
    tok_rest_start: i64,
    tok_size: i64,
) -> String {
    let b1 = rest_off + 1; // is_initialized byte offset
    let b2 = rest_off + 2; // freeze-authority gap start
    let _ = mint_size;
    let rest_proof = format!(
"  have key := memBytesIs_segs (base + {rest_off})
    [.gap gD, .byte b45, .gap gF] ⟨trivial, hb45, trivial, trivial⟩ h
  simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
    hgD, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
  exact key",
        rest_off = rest_off
    );

    let mint_account_eq = format!(
"theorem mint_account_eq
    (base b0 p0 p1 p2 p3 supply b45 : Nat) (gA gD gF : ByteArray)
    (hgA : gA.size = 3) (hgD : gD.size = 1) (hb0 : b0 < 256) (hb45 : b45 < 256) :
    mintSupplyOf base
      {{ preAuth := PartialState.byteBA b0 ++ (gA ++
          (PartialState.u64LE p0 ++ (PartialState.u64LE p1 ++
            (PartialState.u64LE p2 ++ PartialState.u64LE p3)))),
        supply := supply,
        rest := gD ++ (PartialState.byteBA b45 ++ gF) }}
      = ( ( memByteIs base b0 ** memBytesIs (base + 1) gA **
            memU64Is (base + 4) p0 ** memU64Is (base + 12) p1 **
            memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) **
          memU64Is (base + {supply_off}) supply **
          ( memBytesIs (base + {rest_off}) gD ** memByteIs (base + {b1}) b45 **
            memBytesIs (base + {b2}) gF ) ) := by
  funext h
  apply propext
  simp only [mintSupplyOf, mintAcctSupply, MINT_AUTH_OFF, SUPPLY_OFF,
    MINT_REST_OFF, Nat.add_zero]
  have keyP : ∀ h, memBytesIs base
      (PartialState.byteBA b0 ++ (gA ++ (PartialState.u64LE p0 ++
        (PartialState.u64LE p1 ++ (PartialState.u64LE p2 ++ PartialState.u64LE p3))))) h ↔
      ( memByteIs base b0 ** memBytesIs (base + 1) gA ** memU64Is (base + 4) p0 **
        memU64Is (base + 12) p1 ** memU64Is (base + 20) p2 ** memU64Is (base + 28) p3 ) h := by
    intro h
    have key := memBytesIs_segs base
      [.byte b0, .gap gA, .u64 p0, .u64 p1, .u64 p2, .u64 p3]
      ⟨hb0, trivial, trivial, trivial, trivial, trivial, trivial⟩ h
    simp only [segsBytes, segsSL, FieldSeg.bytes, FieldSeg.sl, FieldSeg.size,
      hgA, ba_append_empty, sepConj_emp_right_eq, Nat.add_assoc, Nat.reduceAdd] at key
    exact key
  refine Iff.trans (sepConj_iff_congr_left _ keyP h) ?_
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
{rest_proof}",
        supply_off = supply_off,
        rest_off = rest_off,
        b1 = b1,
        b2 = b2,
        rest_proof = rest_proof
    );

    let mint_supply_eq = format!(
"theorem mint_supply_eq
    (base supply b45 : Nat) (preAuth gD gF : ByteArray)
    (hgD : gD.size = 1) (hb45 : b45 < 256) :
    mintSupplyOf base
      {{ preAuth := preAuth, supply := supply,
        rest := gD ++ (PartialState.byteBA b45 ++ gF) }}
      = ( memBytesIs base preAuth **
          memU64Is (base + {supply_off}) supply **
          ( memBytesIs (base + {rest_off}) gD ** memByteIs (base + {b1}) b45 **
            memBytesIs (base + {b2}) gF ) ) := by
  funext h
  apply propext
  simp only [mintSupplyOf, mintAcctSupply, MINT_AUTH_OFF, SUPPLY_OFF,
    MINT_REST_OFF, Nat.add_zero]
  refine sepConj_iff_congr_right _ ?_ h; intro h
  refine sepConj_iff_congr_right _ ?_ h; intro h
{rest_proof}",
        supply_off = supply_off,
        rest_off = rest_off,
        b1 = b1,
        b2 = b2,
        rest_proof = rest_proof
    );

    let mut gap_ctr = 0u32;
    let dest = render_token_agg_lemma(
        "dest_account_eq",
        false,
        &[108, 109],
        tok_rest_start,
        tok_size,
        &mut gap_ctr,
    );
    format!(
"/-
  Account-codec aggregation for mint-account lifts (MintTo / Burn).
  MECHANICALLY EMITTED by qedlift from the IDL mint+token layouts + the
  lift's owned-byte pattern. Do not edit by hand.
-/

import SVM.SBPF.SegAggregation
import SVM.SBPF.PubkeySL
import SVM.Solana.MintAccountCodec
import SVM.Solana.TokenAccountCodec

namespace {ns}

open SVM.SBPF SVM.Solana

{mint_account_eq}

{mint_supply_eq}

{dest}

end {ns}
",
        ns = ns,
        mint_account_eq = mint_account_eq,
        mint_supply_eq = mint_supply_eq,
        dest = dest
    )
}

/// Write the emitted aggregation module to `examples/lean/<module>.lean`. Returns a log label.
pub(super) fn write_aggregation(agg: &Option<(String, String)>) -> std::io::Result<&'static str> {
    if let Some((module, lean)) = agg {
        let path = format!("examples/lean/{}.lean", module.replace('.', "/"));
        if let Some(parent) = std::path::Path::new(&path).parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&path, lean)?;
        Ok(" (+agg)")
    } else {
        Ok("")
    }
}
