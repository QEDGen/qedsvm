use super::core::{canon_addr, const_of_expr, Atom, BytesVal, Expr, MemCell, Width};
use super::input::BinaryCtx;
use super::{SpecCall, SymState};

/// Emit lift artifacts for `sol_memset_(r1, r2, r3)` at logical PC `pc`, shaped to
/// `call_sol_memset_spec`. Adds a `↦Bytes` pre-atom at r1 (fresh ByteArray, size r3),
/// records post (region filled with r2%256) and `r0 := 0`. CU is data-dependent (∝r3)
/// so `nCu`/`hCu` are surfaced as hypotheses rather than discharged here.
pub(super) fn emit_sol_memset(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
) {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1);
    let r2v = state.read_reg(2);
    let r3v = state.read_reg(3);

    // H6: record writable rr for [r1V, r1V+r3V) so the goal rr matches the `containsWritable`
    // clause that `sl_block_iter` folds in from `call_sol_memset_*_spec`.
    state.rr_walk.push((
        r1v.clone(),
        0,
        Width::Byte,
        true,
        Some((r1v.clone(), r3v.clone())),
    ));

    let idx = state.fresh;
    state.fresh += 1;
    let bs_name = format!("memsetBs_{}", idx);
    let bs_sz = format!("hmemsetBs_{}_sz", idx);
    let ncu_name = format!("nCuMemset{}", idx);
    let hcu_name = format!("hCuMemset{}", idx);

    // Pre atom: `r1V ↦Bytes memsetBs_idx`; size = r3V, or prefix length under a pre-split.
    let mut size_rendered = r3v.atom_lean();
    let blob_len = const_of_expr(&r3v).unwrap_or(1).max(1);
    let (root, lo) = canon_addr(&r1v, 0);
    // Register blob for H8 Phase C split planning (a later dword read at the tail triggers a split).
    let fill_const = const_of_expr(&r2v).map(|f| f as u8);
    if const_of_expr(&r3v).is_some() {
        state.blobs.push((root.clone(), lo, blob_len, fill_const));
    }
    let split_n = state.blob_splits.get(&(root.clone(), lo)).copied();
    // PRE-SPLIT: lift already owns a dword at the blob tail (CloseAccount reads lamports BEFORE
    // zeroing). Collect trailing owned dwords at [len-8k, len-8(k-1)) for k=1,2;
    // `tail_cells[0]` = last 8 bytes. Pre-split specs own prefix-blob + those cells.
    let mut tail_cells: Vec<usize> = Vec::new();
    if const_of_expr(&r3v).is_some() && fill_const.is_some() {
        for k in 1..=2i64 {
            if blob_len < 8 * k + 1 {
                break;
            }
            let want = lo + blob_len - 8 * k;
            match state.mem.iter().position(|c| {
                matches!(c.width, Width::Dword) && {
                    let (cr, cd) = canon_addr(&c.addr_base, c.addr_off);
                    cr == root && cd + c.delta == want
                }
            }) {
                Some(i) => tail_cells.push(i),
                None => break,
            }
        }
    }
    if !tail_cells.is_empty() {
        size_rendered = format!("{}", blob_len - 8 * tail_cells.len() as i64);
    }
    state.pre.push(Atom::Bytes {
        addr: r1v.clone(),
        value: BytesVal::Sym(bs_name.clone()),
    });
    state.memset_blobs.push((bs_name.clone(), size_rendered));
    state
        .syscall_cu_vars
        .push((ncu_name.clone(), hcu_name.clone(), ".sol_memset"));
    state.syscall_pcs.insert(pc, ".sol_memset");

    // Post: r0=0; blob -> `replicateByte (r2V%256) r3V`, or under tail-split: prefix blob +
    // a `↦U64` cell with fill across all 8 lanes (`call_sol_memset_split_u64_spec`).
    state.write_reg(0, Expr::Const(0));
    let have_line = match (tail_cells.len(), split_n, fill_const) {
        (1, _, Some(fill)) => {
            let ci = tail_cells[0];
            let n = blob_len - 8;
            let w: u64 = u64::from_le_bytes([fill; 8]);
            let a_render = SymState::cell_render(&state.mem[ci]);
            let old_v = state.mem[ci].value.atom_lean();
            // Post: cell holds fill across all 8 lanes; blob shrinks to prefix.
            state.mem[ci].value = Expr::Const(w as i64);
            state.note_access(&r1v, 0, n, format!("blob:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate {
                    fill: r2v.clone(),
                    count: Expr::Const(n),
                },
            );
            let ha_name = format!("h_msplit_{}", pc);
            state
                .side_hyps
                .push((ha_name.clone(), format!("{} = {} + {}", a_render, r1v.atom_lean(), n)));
            // call_sol_memset_presplit_u64_spec r0Old r1V r2V r3V n w a
            //   oldV pc nCu bsOld hbs hn ha hw0..hw7 hCu
            format!(
                "have h_{pc} := call_sol_memset_presplit_u64_spec {r0} {r1} {r2} {r3} \
{n} {w} ({a}) {oldv} {pc} {ncu} {bs} {hbs} (by decide) {ha} \
(by decide) (by decide) (by decide) (by decide) (by decide) (by decide) \
(by decide) (by decide) {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(),
                r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(),
                r3 = r3v.atom_lean(),
                n = n,
                w = w,
                a = a_render,
                oldv = old_v,
                ha = ha_name,
                ncu = ncu_name,
                bs = bs_name,
                hbs = bs_sz,
                hcu = hcu_name,
            )
        }
        (2, _, Some(fill)) => {
            // tail_cells[0] = last 8 bytes (a2), [1] = the 8 before (a1).
            let (c2, c1) = (tail_cells[0], tail_cells[1]);
            let n = blob_len - 16;
            let w: u64 = u64::from_le_bytes([fill; 8]);
            let a1_render = SymState::cell_render(&state.mem[c1]);
            let a2_render = SymState::cell_render(&state.mem[c2]);
            let old1 = state.mem[c1].value.atom_lean();
            let old2 = state.mem[c2].value.atom_lean();
            state.mem[c1].value = Expr::Const(w as i64);
            state.mem[c2].value = Expr::Const(w as i64);
            state.note_access(&r1v, 0, n, format!("blob:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate {
                    fill: r2v.clone(),
                    count: Expr::Const(n),
                },
            );
            let ha1_name = format!("h_msplit_{}_a1", pc);
            let ha2_name = format!("h_msplit_{}_a2", pc);
            state.side_hyps.push((
                ha1_name.clone(),
                format!("{} = {} + {}", a1_render, r1v.atom_lean(), n),
            ));
            state.side_hyps.push((
                ha2_name.clone(),
                format!("{} = {} + {} + 8", a2_render, r1v.atom_lean(), n),
            ));
            // call_sol_memset_presplit_2u64_spec r0Old r1V r2V r3V n w
            //   a1 a2 oldV1 oldV2 pc nCu bsOld hbs hn ha1 ha2 hw0..hw7 hCu
            format!(
                "have h_{pc} := call_sol_memset_presplit_2u64_spec {r0} {r1} {r2} {r3} \
{n} {w} ({a1}) ({a2}) {old1} {old2} {pc} {ncu} {bs} {hbs} (by decide) {ha1} {ha2} \
(by decide) (by decide) (by decide) (by decide) (by decide) (by decide) \
(by decide) (by decide) {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(),
                r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(),
                r3 = r3v.atom_lean(),
                n = n,
                w = w,
                a1 = a1_render,
                a2 = a2_render,
                old1 = old1,
                old2 = old2,
                ha1 = ha1_name,
                ha2 = ha2_name,
                ncu = ncu_name,
                bs = bs_name,
                hbs = bs_sz,
                hcu = hcu_name,
            )
        }
        (0, Some(n), Some(fill)) => {
            // Footprints: shrunk blob + the split cell.
            state.note_access(&r1v, 0, n, format!("blob:{}", r1v.to_lean()));
            state.note_access(&r1v, n, 8, format!("blobtail:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate {
                    fill: r2v.clone(),
                    count: Expr::Const(n),
                },
            );
            // Split `↦U64` cell registered at blob-base; later aliased reads reach it via `h_alias`.
            let w: u64 = u64::from_le_bytes([fill; 8]);
            state.mem.push(MemCell {
                addr_base: r1v.clone(),
                addr_off: n,
                width: Width::Dword,
                value: Expr::Const(w as i64),
                delta: 0,
            });
            // Split-cell address equation, consumer-discharged like h_addr* abstractions.
            let ha_name = format!("h_msplit_{}", pc);
            state.side_hyps.push((
                ha_name.clone(),
                format!(
                    "effectiveAddr ({}) ({}) = {} + {}",
                    r1v.to_lean(),
                    n,
                    r1v.atom_lean(),
                    n
                ),
            ));
            // call_sol_memset_split_u64_spec r0Old r1V r2V r3V n w a pc
            //   nCu bsOld hbs hn ha hw0..hw7 hCu
            format!(
                "have h_{pc} := call_sol_memset_split_u64_spec {r0} {r1} {r2} {r3} \
{n} {w} (effectiveAddr ({r1raw}) ({n})) {pc} {ncu} {bs} {hbs} (by decide) {ha} \
(by decide) (by decide) (by decide) (by decide) (by decide) (by decide) \
(by decide) (by decide) {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(),
                r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(),
                r3 = r3v.atom_lean(),
                n = n,
                w = w,
                r1raw = r1v.to_lean(),
                ha = ha_name,
                ncu = ncu_name,
                bs = bs_name,
                hbs = bs_sz,
                hcu = hcu_name,
            )
        }
        _ => {
            // Blob overlap accounting (symbolic count => 1-byte footprint at base, no split).
            // Catches exact-base collisions; full symbolic-length support is part of H8 byte-aliasing.
            state.note_access(&r1v, 0, blob_len, format!("blob:{}", r1v.to_lean()));
            state.byte_blob_post.insert(
                r1v.to_lean(),
                BytesVal::Replicate {
                    fill: r2v.clone(),
                    count: r3v.clone(),
                },
            );
            // call_sol_memset_spec r0Old r1V r2V r3V pc nCu bsOld hbs hCu
            format!(
                "have h_{pc} := call_sol_memset_spec {r0} {r1} {r2} {r3} {pc} {ncu} {bs} {hbs} {hcu}",
                pc = pc,
                r0 = r0v.atom_lean(),
                r1 = r1v.atom_lean(),
                r2 = r2v.atom_lean(),
                r3 = r3v.atom_lean(),
                ncu = ncu_name,
                bs = bs_name,
                hbs = bs_sz,
                hcu = hcu_name,
            )
        }
    };
    spec_calls.push(SpecCall {
        hyp_name: format!("h_{}", pc),
        have_line,
    });
    block_pcs.push(pc);
}

/// Emit `sol_memcmp_(p1 = r1, p2 = r2, n = r3, out = r4)` (H6). Reads `n`
/// bytes at `[r1,r1+n)`/`[r2,r2+n)`, writes the u32-encoded i32 compare
/// result to the 4-byte cell at `r4`, sets `r0 := 0`. Shaped to
/// `call_sol_memcmp_spec`: two `↦Bytes` inputs + one `↦U32` output whose
/// post value is `memcmpResultU32 p1 p2 r3`. `rr = containsRange r1 r3 ∧
/// containsRange r2 r3 ∧ containsWritable r4 4`.
pub(super) fn emit_sol_memcmp(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
) {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1); // p1
    let r2v = state.read_reg(2); // p2
    let r3v = state.read_reg(3); // n
    let r4v = state.read_reg(4); // out

    // rr in the spec's conjunct order: p1 readable, p2 readable, then the
    // fixed 4-byte output writable.
    state.rr_walk.push((
        r1v.clone(),
        0,
        Width::Byte,
        false,
        Some((r1v.clone(), r3v.clone())),
    ));
    state.rr_walk.push((
        r2v.clone(),
        0,
        Width::Byte,
        false,
        Some((r2v.clone(), r3v.clone())),
    ));
    state.rr_walk.push((
        r4v.clone(),
        0,
        Width::Word,
        true,
        Some((r4v.clone(), Expr::Const(4))),
    ));

    let idx = state.fresh;
    state.fresh += 1;
    let p1_name = format!("memcmpP1_{}", idx);
    let p2_name = format!("memcmpP2_{}", idx);
    let size_rendered = r3v.atom_lean();
    let blob_len = const_of_expr(&r3v).unwrap_or(1).max(1);

    // Pre: `(r1V ↦Bytes p1) ** (r2V ↦Bytes p2)`.
    state.pre.push(Atom::Bytes {
        addr: r1v.clone(),
        value: BytesVal::Sym(p1_name.clone()),
    });
    state.pre.push(Atom::Bytes {
        addr: r2v.clone(),
        value: BytesVal::Sym(p2_name.clone()),
    });
    state.memset_blobs.push((p1_name.clone(), size_rendered.clone()));
    state.memset_blobs.push((p2_name.clone(), size_rendered.clone()));

    // Pre: the 4-byte `↦U32` output cell at r4 (old value = fresh var,
    // surfaced as a theorem param via `u64_load_vars` like the sysvar cells).
    let out_idx = state.fresh;
    state.fresh += 1;
    let out_name = format!("oldMemW_{}", out_idx);
    state.u64_load_vars.push((out_name.clone(), 32));
    let out_old = Expr::InitMem(out_name.clone());
    state.mem.push(MemCell {
        addr_base: r4v.clone(),
        addr_off: 0,
        width: Width::Word,
        value: out_old.clone(),
        delta: 0,
    });
    let out_ci = state.mem.len() - 1;
    state.pre.push(Atom::Mem {
        addr_base: r4v.clone(),
        addr_off: 0,
        width: Width::Word,
        value: out_old,
        delta: 0,
    });

    // Footprints: three pairwise-disjoint regions.
    state.note_access(&r1v, 0, blob_len, format!("memcmpP1:{}", r1v.to_lean()));
    state.note_access(&r2v, 0, blob_len, format!("memcmpP2:{}", r2v.to_lean()));
    state.note_access(&r4v, 0, 4, format!("memcmpOut:{}", r4v.to_lean()));

    // Post: out cell ← `memcmpResultU32 p1 p2 r3`; r0 := 0.
    state.mem[out_ci].value = Expr::Raw(format!(
        "(memcmpResultU32 {} {} {})",
        p1_name, p2_name, size_rendered
    ));
    state.write_reg(0, Expr::Const(0));

    let ncu_name = format!("nCuMemcmp{}", idx);
    let hcu_name = format!("hCuMemcmp{}", idx);
    state
        .syscall_cu_vars
        .push((ncu_name.clone(), hcu_name.clone(), ".sol_memcmp"));
    state.syscall_pcs.insert(pc, ".sol_memcmp");

    // call_sol_memcmp_spec r0Old r1V r2V r3V r4V outOld pc nCu p1 p2 hsz1 hsz2 hCu
    let have_line = format!(
        "have h_{pc} := call_sol_memcmp_spec {r0} {r1} {r2} {r3} {r4} {out} {pc} {ncu} {p1} {p2} h{p1}_sz h{p2}_sz {hcu}",
        pc = pc,
        r0 = r0v.atom_lean(),
        r1 = r1v.atom_lean(),
        r2 = r2v.atom_lean(),
        r3 = r3v.atom_lean(),
        r4 = r4v.atom_lean(),
        out = out_name,
        ncu = ncu_name,
        p1 = p1_name,
        p2 = p2_name,
        hcu = hcu_name,
    );
    spec_calls.push(SpecCall {
        hyp_name: format!("h_{}", pc),
        have_line,
    });
    block_pcs.push(pc);
}

/// The 32-byte rent sysvar id (`SysvarRent111…`), mirroring
/// `SysvarData.rentId`.
const RENT_ID_BYTES: [u8; 32] = [
    0x06, 0xa7, 0xd5, 0x17, 0x19, 0x2c, 0x5c, 0x51, 0x21, 0x8c, 0xc9, 0x4c, 0x3d, 0x4a, 0xf1,
    0x7f, 0x58, 0xda, 0xee, 0x08, 0x9b, 0xa1, 0xfd, 0x44, 0xe3, 0xdb, 0xd9, 0x8a, 0x00, 0x00,
    0x00, 0x00,
];

/// Emit `sol_get_sysvar` (H8 Phase C-2). Only the RENT id at offset 0, length 17 (pinocchio
/// `Rent::get()`) is modeled, shaped to `call_sol_get_sysvar_cells17_spec`. Out region owned as
/// two `↦U64` cells + one `↦ₘ` byte (post: mollusk-default rent 3480/2.0-bits/50); address-bound
/// and disjointness side conditions surfaced as hypotheses.
pub(super) fn emit_sol_get_sysvar(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
    ctx: &BinaryCtx,
) -> Result<(), Box<dyn std::error::Error>> {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1);
    let r2v = state.read_reg(2);
    let r3v = state.read_reg(3);
    let r4v = state.read_reg(4);
    let id_addr = const_of_expr(&r1v)
        .ok_or_else(|| format!("get_sysvar at pc {pc}: symbolic sysvar-id address"))?
        as u64;
    let off = const_of_expr(&r3v).ok_or_else(|| format!("get_sysvar at pc {pc}: symbolic offset"))?;
    let len = const_of_expr(&r4v).ok_or_else(|| format!("get_sysvar at pc {pc}: symbolic length"))?;
    let region = ctx.executable.get_ro_region();
    let rel = id_addr
        .checked_sub(region.vm_addr)
        .filter(|r| r + 32 <= region.len)
        .ok_or_else(|| {
            format!(
                "get_sysvar at pc {pc}: id address {id_addr:#x} outside the \
             RO region"
            )
        })?;
    let id_bytes: &[u8] =
        unsafe { std::slice::from_raw_parts((region.host_addr + rel) as *const u8, 32) };
    if id_bytes != RENT_ID_BYTES || off != 0 || len != 17 {
        return Err(format!(
            "get_sysvar at pc {pc}: only the RENT id with offset 0 / \
             length 17 is modelled (cells17 shape); got id {:02x?}…, \
             offset {off}, length {len}",
            &id_bytes[..8]
        )
        .into());
    }

    let idx = state.fresh;
    state.fresh += 1;
    let ncu_name = format!("nCuGetSysvar{}", idx);
    let hcu_name = format!("hCuGetSysvar{}", idx);
    state
        .syscall_cu_vars
        .push((ncu_name.clone(), hcu_name.clone(), ".sol_get_sysvar"));
    state.syscall_pcs.insert(pc, ".sol_get_sysvar");

    state.pre.push(Atom::Bytes32 {
        addr: r1v.clone(),
        name: "SysvarData.rentId".to_string(),
    });
    state.note_access(&r1v, 0, 32, format!("sysvarId:{}", r1v.to_lean()));

    let mut cells: Vec<(i64, Width, u32, i64)> = vec![
        (0, Width::Dword, 64, 3480),
        (8, Width::Dword, 64, 4611686018427387904),
        (16, Width::Byte, 8, 50),
    ];
    let mut old_names: Vec<String> = Vec::new();
    for (coff, w, bits, post) in cells.drain(..) {
        let i = state.fresh;
        state.fresh += 1;
        let name = format!(
            "{}_{}",
            if matches!(w, Width::Dword) {
                "oldMemD"
            } else {
                "oldMemB"
            },
            i
        );
        state.u64_load_vars.push((name.clone(), bits));
        let v = Expr::InitMem(name.clone());
        state.mem.push(MemCell {
            addr_base: r2v.clone(),
            addr_off: coff,
            width: w,
            value: v.clone(),
            delta: 0,
        });
        state.pre.push(Atom::Mem {
            addr_base: r2v.clone(),
            addr_off: coff,
            width: w,
            value: v,
            delta: 0,
        });
        let wl = if matches!(w, Width::Dword) { 8 } else { 1 };
        state.note_access(&r2v, coff, wl, format!("sysvarOut:{}@{}", r2v.to_lean(), coff));
        old_names.push(name);
        let ci = state.mem.len() - 1;
        state.mem[ci].value = Expr::Const(post);
    }
    state.write_reg(0, Expr::Const(0));

    // Side conditions (symbolic out address; consumer discharges by `decide`).
    let out = r2v.to_lean();
    let out_atom = r2v.atom_lean();
    let id_atom = r1v.atom_lean();
    let h_out = format!("h_sysvar_out_{}", pc);
    let h_outlen = format!("h_sysvar_outlen_{}", pc);
    let h_disj = format!("h_sysvar_disj_{}", pc);
    let ha1 = format!("h_sysvar_a1_{}", pc);
    let ha2 = format!("h_sysvar_a2_{}", pc);
    state
        .side_hyps
        .push((h_out.clone(), format!("{} < Memory.INPUT_START", out_atom)));
    state
        .side_hyps
        .push((h_outlen.clone(), format!("{} + 17 < U64_MODULUS", out_atom)));
    state.side_hyps.push((
        h_disj.clone(),
        format!(
            "{} + 32 ≤ {} ∨ {} + 17 ≤ {}",
            id_atom, out_atom, out_atom, id_atom
        ),
    ));
    state
        .side_hyps
        .push((ha1.clone(), format!("effectiveAddr ({}) (8) = {} + 8", out, out_atom)));
    state.side_hyps.push((
        ha2.clone(),
        format!("effectiveAddr ({}) (16) = {} + 8 + 8", out, out_atom),
    ));

    // call_sol_get_sysvar_cells17_spec r0Old idA outA offV lenV a1 a2
    //   oldD0 oldD1 oldB w0 w1 wb idBytes buf slice pc nCu
    //   hIdSize hBuf hInRange hOutAddr hOffLen hOutLen hLen hSliceSize
    //   hSlice hsl hwb hob ha1 ha2 h_disj hCu
    let have_line = format!(
        "have h_{pc} := call_sol_get_sysvar_cells17_spec {r0} ({id}) ({out}) 0 17 \
(effectiveAddr ({outraw}) (8)) (effectiveAddr ({outraw}) (16)) \
{o0} {o1} {o2} 3480 4611686018427387904 50 \
SysvarData.rentId SysvarData.rentBuf SysvarData.rentBuf {pc} {ncu} \
rfl SysvarData.sysvarBuffer_rent (by decide) {hout} (by decide) {houtlen} \
rfl rfl (by intro i _; rw [Nat.zero_add]) rfl (by decide) h{o2}_lt \
{ha1} {ha2} {hdisj} {hcu}",
        pc = pc,
        r0 = r0v.atom_lean(),
        id = r1v.to_lean(),
        out = out,
        outraw = out,
        o0 = old_names[0],
        o1 = old_names[1],
        o2 = old_names[2],
        ncu = ncu_name,
        hout = h_out,
        houtlen = h_outlen,
        ha1 = ha1,
        ha2 = ha2,
        hdisj = h_disj,
        hcu = hcu_name,
    );
    spec_calls.push(SpecCall {
        hyp_name: format!("h_{}", pc),
        have_line,
    });
    block_pcs.push(pc);
    Ok(())
}

/// Emit the lift artifacts for an "r0-only" host syscall — one whose
/// model effect is just `r0 := 0` (no memory, no output buffer): e.g.
/// `sol_get_sysvar` (`Misc.execGetSysvar`) and `sol_log_`
/// (`Logging.execLog`). The simplest syscall shape: a single `r0` atom,
/// with the `nCu`/`hCu` CU assumption surfaced as a hypothesis (as for
/// memset). `spec` is the proven `call_<name>_spec` (takes r0Old pc nCu
/// hCu); `ctor` is the `Syscall` constructor; `tag` names the fresh vars.
pub(super) fn emit_r0_syscall(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
    spec: &str,
    ctor: &'static str,
    tag: &str,
) {
    let r0v = state.read_reg(0);
    let idx = state.fresh;
    state.fresh += 1;
    let ncu_name = format!("nCu{}{}", tag, idx);
    let hcu_name = format!("hCu{}{}", tag, idx);
    state.syscall_cu_vars.push((ncu_name.clone(), hcu_name.clone(), ctor));
    state.syscall_pcs.insert(pc, ctor);
    state.write_reg(0, Expr::Const(0));
    // call_<name>_spec r0Old pc nCu hCu
    let have_line = format!(
        "have h_{pc} := {spec} {r0} {pc} {ncu} {hcu}",
        pc = pc,
        spec = spec,
        r0 = r0v.atom_lean(),
        ncu = ncu_name,
        hcu = hcu_name,
    );
    spec_calls.push(SpecCall {
        hyp_name: format!("h_{}", pc),
        have_line,
    });
    block_pcs.push(pc);
}

/// Emit `sol_log_(r1, r2)` (H6). Unlike `emit_r0_syscall`, `call_sol_log_spec` pins r1/r2 and
/// carries `rr = containsRange r1 r2`, so we read those registers and record the rr clause.
pub(super) fn emit_sol_log(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
) {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1);
    let r2v = state.read_reg(2);
    // The logged slice `[r1, r1+r2)` must be in a readable region.
    state.rr_walk.push((
        r1v.clone(),
        0,
        Width::Byte,
        false,
        Some((r1v.clone(), r2v.clone())),
    ));
    let idx = state.fresh;
    state.fresh += 1;
    let ncu_name = format!("nCuLog{}", idx);
    let hcu_name = format!("hCuLog{}", idx);
    state
        .syscall_cu_vars
        .push((ncu_name.clone(), hcu_name.clone(), ".sol_log_"));
    state.syscall_pcs.insert(pc, ".sol_log_");
    state.write_reg(0, Expr::Const(0));
    let have_line = format!(
        "have h_{pc} := call_sol_log_spec {r0} {r1} {r2} {pc} {ncu} {hcu}",
        pc = pc,
        r0 = r0v.atom_lean(),
        r1 = r1v.atom_lean(),
        r2 = r2v.atom_lean(),
        ncu = ncu_name,
        hcu = hcu_name,
    );
    spec_calls.push(SpecCall {
        hyp_name: format!("h_{}", pc),
        have_line,
    });
    block_pcs.push(pc);
}

/// Emit `sol_memcpy_`/`sol_memmove_(dst = r1, src = r2, n = r3)` (H6). Both share
/// `MemOps.execCopy`: copy `n` bytes src→dst, set `r0 := 0`. Shaped to
/// `call_sol_{memcpy,memmove}_spec` — two `↦Bytes` atoms (`srcBytes` at r2,
/// `bsOld` at r1) force src/dst disjoint, and the post rewrites the dst blob to
/// `srcBytes`. `rr = containsRange r2 r3 ∧ containsWritable r1 r3`. CU is
/// data-dependent (∝ r3) so `nCu`/`hCu` are surfaced as hypotheses. `is_move`
/// selects the (otherwise identical) `memmove` spec.
pub(super) fn emit_sol_memcpy(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
    is_move: bool,
) {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1); // dst
    let r2v = state.read_reg(2); // src
    let r3v = state.read_reg(3); // n

    // rr in the spec's conjunct order: src `[r2, r2+r3)` readable, then dst
    // `[r1, r1+r3)` writable. Left-fold order matches `slBlockIter`.
    state.rr_walk.push((
        r2v.clone(),
        0,
        Width::Byte,
        false,
        Some((r2v.clone(), r3v.clone())),
    ));
    state.rr_walk.push((
        r1v.clone(),
        0,
        Width::Byte,
        true,
        Some((r1v.clone(), r3v.clone())),
    ));

    let idx = state.fresh;
    state.fresh += 1;
    let (mnem, ctor, cap) = if is_move {
        ("memmove", ".sol_memmove", "Memmove")
    } else {
        ("memcpy", ".sol_memcpy", "Memcpy")
    };
    let src_name = format!("{}Src_{}", mnem, idx);
    let dst_name = format!("{}Dst_{}", mnem, idx);
    let size_rendered = r3v.atom_lean();
    let blob_len = const_of_expr(&r3v).unwrap_or(1).max(1);

    // Pre atoms in spec order: `(r2V ↦Bytes srcBytes) ** (r1V ↦Bytes bsOld)`.
    state.pre.push(Atom::Bytes {
        addr: r2v.clone(),
        value: BytesVal::Sym(src_name.clone()),
    });
    state.pre.push(Atom::Bytes {
        addr: r1v.clone(),
        value: BytesVal::Sym(dst_name.clone()),
    });
    state.memset_blobs.push((src_name.clone(), size_rendered.clone()));
    state.memset_blobs.push((dst_name.clone(), size_rendered));

    // Footprints: disjoint src-read + dst-write regions (overlap ⇒ vacuous, fail closed).
    state.note_access(&r2v, 0, blob_len, format!("{}Src:{}", mnem, r2v.to_lean()));
    state.note_access(&r1v, 0, blob_len, format!("{}Dst:{}", mnem, r1v.to_lean()));

    let ncu_name = format!("nCu{}{}", cap, idx);
    let hcu_name = format!("hCu{}{}", cap, idx);
    state.syscall_cu_vars.push((ncu_name.clone(), hcu_name.clone(), ctor));
    state.syscall_pcs.insert(pc, ctor);

    // Post: dst blob (at r1V) holds `srcBytes`; src blob unchanged; r0 := 0.
    state
        .byte_blob_post
        .insert(r1v.to_lean(), BytesVal::Sym(src_name.clone()));
    state.write_reg(0, Expr::Const(0));

    let spec = if is_move {
        "call_sol_memmove_spec"
    } else {
        "call_sol_memcpy_spec"
    };
    // call_sol_{memcpy,memmove}_spec r0Old r1V r2V r3V pc nCu srcBytes bsOld hsrc hbs hCu
    let have_line = format!(
        "have h_{pc} := {spec} {r0} {r1} {r2} {r3} {pc} {ncu} {src} {dst} h{src}_sz h{dst}_sz {hcu}",
        pc = pc,
        spec = spec,
        r0 = r0v.atom_lean(),
        r1 = r1v.atom_lean(),
        r2 = r2v.atom_lean(),
        r3 = r3v.atom_lean(),
        ncu = ncu_name,
        src = src_name,
        dst = dst_name,
        hcu = hcu_name,
    );
    spec_calls.push(SpecCall {
        hyp_name: format!("h_{}", pc),
        have_line,
    });
    block_pcs.push(pc);
}

/// Emit `sol_set_return_data(ptr = r1, len = r2)` (H6 + H7). Reads the input
/// slice `[r1, r1+r2)` and COPIES it into `State.returnData`, setting `r0 := 0`;
/// memory is unchanged. Shaped to `call_sol_set_return_data_spec`: a read-only
/// input `↦Bytes` blob at r1 (size r2) plus the framed `↦ReturnData` atom (old
/// buffer `rdOld`, flips to the input blob in the post). `rr = containsRange r1
/// r2`; the length guard `r2 ≤ MAX_RETURN_DATA` (H7) is discharged by `decide`,
/// so a trace fixture must pass a constant in-limit length (else the build fails
/// closed). CU is data-dependent (∝ r2) so `nCu`/`hCu` are surfaced as hypotheses.
pub(super) fn emit_sol_set_return_data(
    state: &mut SymState,
    spec_calls: &mut Vec<SpecCall>,
    block_pcs: &mut Vec<usize>,
    pc: usize,
) {
    let r0v = state.read_reg(0);
    let r1v = state.read_reg(1); // ptr
    let r2v = state.read_reg(2); // len

    // H6: the input slice `[r1, r1+r2)` must be in a readable region.
    state.rr_walk.push((
        r1v.clone(),
        0,
        Width::Byte,
        false,
        Some((r1v.clone(), r2v.clone())),
    ));

    let idx = state.fresh;
    state.fresh += 1;
    let blob_name = format!("setRetData_{}", idx);
    let rd_old_name = format!("retDataOld_{}", idx);
    let ncu_name = format!("nCuSetRetData{}", idx);
    let hcu_name = format!("hCuSetRetData{}", idx);

    let size_rendered = r2v.atom_lean();
    let blob_len = const_of_expr(&r2v).unwrap_or(1).max(1);

    // Pre atoms in spec order: `(r1V ↦Bytes inputBlob) ** (↦ReturnData rdOld)`.
    state.pre.push(Atom::Bytes {
        addr: r1v.clone(),
        value: BytesVal::Sym(blob_name.clone()),
    });
    state.pre.push(Atom::ReturnData {
        value: BytesVal::Sym(rd_old_name.clone()),
    });
    state.memset_blobs.push((blob_name.clone(), size_rendered));
    state.bytearray_vars.push(rd_old_name.clone());

    // Footprint: the read input slice (must be disjoint from other owned regions).
    state.note_access(&r1v, 0, blob_len, format!("setRetData:{}", r1v.to_lean()));

    state
        .syscall_cu_vars
        .push((ncu_name.clone(), hcu_name.clone(), ".sol_set_return_data"));
    state.syscall_pcs.insert(pc, ".sol_set_return_data");

    // Post: returnData holds the input blob; input blob unchanged; r0 := 0.
    state.returndata_post = Some(BytesVal::Sym(blob_name.clone()));
    state.write_reg(0, Expr::Const(0));

    // call_sol_set_return_data_spec r0Old r1V r2V pc nCu inputBlob rdOld hsize hlen hCu
    let have_line = format!(
        "have h_{pc} := call_sol_set_return_data_spec {r0} {r1} {r2} {pc} {ncu} \
         {blob} {rd} h{blob}_sz (by decide) {hcu}",
        pc = pc,
        r0 = r0v.atom_lean(),
        r1 = r1v.atom_lean(),
        r2 = r2v.atom_lean(),
        ncu = ncu_name,
        blob = blob_name,
        rd = rd_old_name,
        hcu = hcu_name,
    );
    spec_calls.push(SpecCall {
        hyp_name: format!("h_{}", pc),
        have_line,
    });
    block_pcs.push(pc);
}
