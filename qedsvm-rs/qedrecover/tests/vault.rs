use std::path::Path;
use std::process::Command;

#[test]
fn recovers_authorized_vault_after_parser_and_authorization_guards() {
    let fixtures = Path::new("../tests/fixtures").canonicalize().unwrap();
    let meta =
        std::env::temp_dir().join(format!("qedrecover-authorized-{}.toml", std::process::id()));
    let output = Command::new(env!("CARGO_BIN_EXE_qedrecover"))
        .arg("--so")
        .arg(fixtures.join("sbpfv3_vault_authorized.so"))
        .arg("--overlay")
        .arg(fixtures.join("sbpfv3_vault_authorized.qedoverlay.toml"))
        .arg("--trace")
        .arg(fixtures.join("sbpfv3_vault_authorized_success.pcs"))
        .arg("--qedmeta-out")
        .arg(&meta)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let sidecar = qed_artifacts::load_qedmeta(&meta).unwrap();
    assert_eq!(
        std::fs::read_to_string(&meta).unwrap(),
        std::fs::read_to_string(fixtures.join("sbpfv3_vault_authorized.qedmeta.toml")).unwrap()
    );
    let recovered = sidecar.instructions[0].recovered.as_ref().unwrap();
    assert_eq!(
        (
            recovered.dispatch_load_pc,
            recovered.dispatch_jeq_pc,
            recovered.arm_entry_pc
        ),
        (48, 49, 50)
    );
    std::fs::remove_file(meta).unwrap();
}

/// Nonzero-offset recovery is allowed only at the instruction-data position
/// derived from the overlay's explicit account lengths.
#[test]
fn recovers_v3_serialized_instruction_discriminator() {
    let fixtures = Path::new("../tests/fixtures").canonicalize().unwrap();
    let dir = std::env::temp_dir().join(format!("qedrecover-v3-vault-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let meta = dir.join("vault.qedmeta.toml");
    let output = Command::new(env!("CARGO_BIN_EXE_qedrecover"))
        .args([
            "--so",
            fixtures.join("sbpfv3_vault_deposit.so").to_str().unwrap(),
        ])
        .args([
            "--overlay",
            fixtures
                .join("sbpfv3_vault_deposit.qedoverlay.toml")
                .to_str()
                .unwrap(),
        ])
        .args([
            "--trace",
            fixtures
                .join("sbpfv3_vault_deposit_success.pcs")
                .to_str()
                .unwrap(),
        ])
        .args(["--qedmeta-out", meta.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        meta.exists(),
        "recovery did not emit a sidecar: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    let sidecar = qed_artifacts::load_qedmeta(&meta).unwrap();
    assert_eq!(
        std::fs::read_to_string(&meta).unwrap(),
        std::fs::read_to_string(fixtures.join("sbpfv3_vault_deposit.qedmeta.toml")).unwrap()
    );
    let recovered = sidecar.instructions[0].recovered.as_ref().unwrap();
    assert_eq!(
        (
            recovered.dispatch_load_pc,
            recovered.dispatch_jeq_pc,
            recovered.arm_entry_pc
        ),
        (1, 2, 3)
    );

    // A wrong length must not fall back to accepting any r1-relative load.
    let overlay = std::fs::read_to_string(fixtures.join("sbpfv3_vault_deposit.qedoverlay.toml"))
        .unwrap()
        .replace(
            "sbpfv3_vault_deposit.codama.json",
            fixtures
                .join("sbpfv3_vault_deposit.codama.json")
                .to_str()
                .unwrap(),
        )
        .replace("[41]", "[8]");
    let wrong_overlay = dir.join("wrong.toml");
    std::fs::write(&wrong_overlay, overlay).unwrap();
    let wrong_meta = dir.join("wrong.qedmeta.toml");
    let output = Command::new(env!("CARGO_BIN_EXE_qedrecover"))
        .args([
            "--so",
            fixtures.join("sbpfv3_vault_deposit.so").to_str().unwrap(),
        ])
        .args(["--overlay", wrong_overlay.to_str().unwrap()])
        .args(["--qedmeta-out", wrong_meta.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        !output.status.success(),
        "an explicitly requested sidecar must fail on a dispatch miss"
    );
    assert!(!wrong_meta.exists());
    std::fs::remove_dir_all(dir).unwrap();
}
