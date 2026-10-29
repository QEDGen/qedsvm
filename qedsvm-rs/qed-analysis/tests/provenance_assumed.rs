use qed_analysis::{
    cfg::Cfg,
    image::ProgramImage,
    success_proofs::provenance::{abstract_map_with, AVal, Assumed, Width},
};
use solana_sbpf::ebpf;
use std::path::Path;

fn label_vault() -> (ProgramImage, Cfg) {
    let image = ProgramImage::load(Path::new("../tests/fixtures/label_vault.so")).unwrap();
    let cfg = Cfg::build(&image).unwrap();
    (image, cfg)
}

fn succ(cfg: &Cfg) -> Vec<Vec<usize>> {
    (0..cfg.flow.len()).map(|p| cfg.successors(p)).collect()
}

/// The first `ldxb r4, [r2 + 0]`: account 1's duplicate marker.
fn dup_marker_load(image: &ProgramImage) -> usize {
    image
        .insns
        .iter()
        .position(|i| i.opc == ebpf::LD_B_REG && i.dst == 4 && i.src == 2 && i.off == 0)
        .unwrap()
}

#[test]
fn q2_assumed_data_len_makes_second_account_offset_constant() {
    let (image, cfg) = label_vault();
    let asm: Assumed = vec![(0x58, Width::Dword, 48)];
    let map = abstract_map_with(&image, &cfg, &succ(&cfg), cfg.entry, &asm).unwrap();
    let pc = dup_marker_load(&image);
    // 8 (account count) + 88 (header) + 8 (data_len) + 48 (data) + 10240 (realloc) + 8 (rent)
    assert_eq!(map[pc].as_ref().unwrap().regs[2], AVal::InPtr(0x2898));
}

#[test]
fn q2_without_assumption_second_account_offset_is_unknown() {
    let (image, cfg) = label_vault();
    let map = abstract_map_with(&image, &cfg, &succ(&cfg), cfg.entry, &[]).unwrap();
    let pc = dup_marker_load(&image);
    assert_eq!(map[pc].as_ref().unwrap().regs[2], AVal::Top);
}
