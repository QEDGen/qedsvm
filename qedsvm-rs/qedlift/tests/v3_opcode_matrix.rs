//! The sBPF V3 opcode inventory is checked against the pinned verifier, not
//! transcribed: every opcode `solana-sbpf`'s `RequisiteVerifier` accepts for
//! V3 must appear in the ISA-matrix fixture (whose single path is diff-tested
//! against Mollusk and lifted to a checked Lean theorem) or be a call form
//! covered by its own fixture.

use std::collections::BTreeSet;

use solana_sbpf::program::SBPFVersion;
use solana_sbpf::verifier::{RequisiteVerifier, Verifier};
use solana_sbpf::vm::Config;

/// Call forms proved and diff-tested by dedicated fixtures
/// (`sbpfv3_static_path.so`, `sbpfv3_callx_path.so`, `sbpfv3_cpi_*.so`).
const CALL_FORMS: [u8; 2] = [0x85, 0x8d];

fn insn(op: u8, imm: i32) -> [u8; 8] {
    let mut b = [0u8; 8];
    b[0] = op;
    b[1] = 0x21; // dst r1, src r2
    b[4..8].copy_from_slice(&imm.to_le_bytes());
    b
}

/// Opcodes the pinned V3 verifier accepts with some well-formed operands.
fn verifier_accepted() -> BTreeSet<u8> {
    let exit = insn(0x95, 0);
    (0u8..=255)
        .filter(|&op| {
            [1, 16].iter().any(|&imm| {
                let mut prog = insn(op, imm).to_vec();
                if op == 0x18 {
                    prog.extend_from_slice(&[0u8; 8]); // lddw second slot
                }
                prog.extend_from_slice(&exit);
                RequisiteVerifier::verify(&prog, &Config::default(), SBPFVersion::V3).is_ok()
            })
        })
        .collect()
}

fn fixture_opcodes() -> BTreeSet<u8> {
    let elf = std::fs::read("../tests/fixtures/sbpfv3_isa_matrix.so").expect("fixture");
    assert_eq!(
        elf[48], 3,
        "sbpfv3_isa_matrix.so must declare e_flags = 3 (V3)"
    );
    let text = &elf[120..];
    let mut ops = BTreeSet::new();
    let mut i = 0;
    while i < text.len() {
        ops.insert(text[i]);
        i += if text[i] == 0x18 { 16 } else { 8 };
    }
    ops
}

#[test]
fn isa_matrix_fixture_covers_every_verifier_accepted_v3_opcode() {
    let accepted = verifier_accepted();
    let mut covered = fixture_opcodes();
    covered.extend(CALL_FORMS);
    let missing: Vec<String> = accepted
        .difference(&covered)
        .map(|op| format!("0x{op:02x}"))
        .collect();
    let invalid: Vec<String> = covered
        .difference(&accepted)
        .map(|op| format!("0x{op:02x}"))
        .collect();
    assert!(
        missing.is_empty(),
        "V3 opcodes without matrix coverage: {missing:?}"
    );
    assert!(
        invalid.is_empty(),
        "matrix uses opcodes V3 rejects: {invalid:?}"
    );
    assert_eq!(
        accepted.len(),
        113,
        "pinned V3 verifier inventory changed size"
    );
}

/// Every fixture in the V3 manifest declares V3 in its ELF header; the
/// version is read from the bytes, never inferred from the file name.
#[test]
fn every_v3_fixture_declares_v3_in_its_elf_header() {
    let manifest = std::fs::read_to_string("../tests/fixtures/sbpfv3_fixtures.sha256")
        .expect("V3 fixture manifest");
    let mut count = 0;
    for line in manifest.lines().filter(|l| !l.trim().is_empty()) {
        let name = line.split_whitespace().nth(1).expect("sha256sum line");
        let elf = std::fs::read(format!("../tests/fixtures/{name}")).expect("fixture");
        assert_eq!(&elf[..4], b"\x7fELF", "{name} is not an ELF");
        assert_eq!(elf[48], 3, "{name} must declare e_flags = 3 (V3)");
        count += 1;
    }
    assert!(count >= 10, "V3 fixture manifest unexpectedly short");
}
