//! Authority facts on one route (solana-skills#450): which accounts' `is_signer` bytes and
//! which key-against-stored-key compares every path from the route to its edge checks.
//! These name what the generated guards already pin; Lean proves the byte facts.

use crate::{
    cfg::Cfg,
    discover::dispatch::{Analysis, EdgeLayout},
    image::ProgramImage,
    input_layout::aligned_input_offsets,
    success_proofs::provenance::{abstract_map_with, AVal},
};
use solana_sbpf::ebpf;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct KeyCompare {
    /// The account whose 32-byte key is compared.
    pub account: usize,
    /// The account whose data holds the expected key.
    pub against_account: usize,
    pub against_data_offset: u64,
}

#[derive(Clone, Debug)]
pub struct RouteAuthority {
    pub route: usize,
    pub signers: Vec<usize>,
    pub key_compares: Vec<KeyCompare>,
}

/// Account regions as `(header, data, data_len)` input offsets.
pub(crate) fn regions(layout: &EdgeLayout) -> Result<Vec<(u64, u64, u64)>, String> {
    let lengths: Vec<usize> = layout
        .assumed
        .iter()
        .map(|((_, _, v), _)| *v as usize)
        .collect();
    let offsets = aligned_input_offsets(&lengths).map_err(str::to_string)?;
    Ok(offsets
        .account_data
        .iter()
        .zip(&lengths)
        .map(|(&d, &l)| (d as u64 - 88, d as u64, l as u64))
        .collect())
}

pub fn route_authority(
    image: &ProgramImage,
    cfg: &Cfg,
    layout: &EdgeLayout,
    route: usize,
) -> Result<RouteAuthority, String> {
    let an = Analysis::new(image, cfg)?;
    let map = abstract_map_with(
        image,
        cfg,
        &an.graph.succ,
        cfg.entry,
        &layout.assumed_words(),
    )?;
    let regions = regions(layout)?;
    let mut guards = an.graph.guards(cfg, cfg.entry, layout.edge);
    guards.extend(an.graph.guards(cfg, route, layout.edge));
    let mut signers = BTreeSet::new();
    // (account, other limb base) -> limbs seen
    let mut limbs: BTreeMap<(usize, u64), BTreeSet<u64>> = BTreeMap::new();
    for g in guards {
        let (Some(a), i) = (&map[g.pc], &image.insns[g.pc]) else {
            continue;
        };
        let dv = &a.regs[i.dst as usize];
        let sv = if i.opc & ebpf::BPF_X != 0 {
            a.regs[i.src as usize].clone()
        } else {
            AVal::Const(i.imm as u64)
        };
        for (n, &(header, _, _)) in regions.iter().enumerate() {
            if *dv == AVal::InLoad("byte", header + 1) {
                signers.insert(n);
            }
        }
        if let (AVal::InLoad("dword", x), AVal::InLoad("dword", y)) = (dv, &sv) {
            for (p, q) in [(*x, *y), (*y, *x)] {
                for (n, &(header, _, _)) in regions.iter().enumerate() {
                    let key = header + 8;
                    if (key..key + 32).contains(&p) && (p - key) % 8 == 0 {
                        let k = p - key;
                        if let Some(base) = q.checked_sub(k) {
                            limbs.entry((n, base)).or_default().insert(k);
                        }
                    }
                }
            }
        }
    }
    let mut key_compares = Vec::new();
    for ((account, base), ks) in limbs {
        if ks.len() != 4 {
            continue;
        }
        for (b, &(_, data, len)) in regions.iter().enumerate() {
            if base >= data && base + 32 <= data + len {
                key_compares.push(KeyCompare {
                    account,
                    against_account: b,
                    against_data_offset: base - data,
                });
            }
        }
    }
    key_compares.sort();
    Ok(RouteAuthority {
        route,
        signers: signers.into_iter().collect(),
        key_compares,
    })
}
