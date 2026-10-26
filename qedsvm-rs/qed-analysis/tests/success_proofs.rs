use qed_analysis::{
    image::ProgramImage,
    success_proofs::{generate, BaselineInputs},
};
use std::path::Path;

fn inputs() -> BaselineInputs {
    serde_json::from_str(include_str!(
        "../../../examples/lean/PToken/success-proof-inputs.json"
    ))
    .unwrap()
}

fn image() -> ProgramImage {
    ProgramImage::load(Path::new("../tests/fixtures/p_token.so")).unwrap()
}

#[test]
fn reproduces_existing_modules_byte_for_byte() {
    let generated = generate(&image(), &inputs()).unwrap();
    assert_eq!(
        generated.paths,
        include_str!("../../../examples/lean/PToken/SuccessPaths.lean")
    );
    assert_eq!(
        generated.inputs,
        include_str!("../../../examples/lean/PToken/SuccessInputs.lean")
    );
    assert_eq!(
        generated.readable_fields,
        include_str!("../../../examples/lean/PToken/ReadableFields.lean")
    );
    assert_eq!(generated.guard_count, 947);
    assert_eq!(generated.input_guard_count, 806);
}

#[test]
fn rejects_wrong_artifact_before_generating() {
    let mut input = inputs();
    input.artifact_sha256 = "0".repeat(64);
    assert!(generate(&image(), &input)
        .unwrap_err()
        .contains("artifact SHA-256"));
}

#[test]
fn rejects_invalid_checkpoint() {
    let mut input = inputs();
    input.edges[0].checkpoints[0] = usize::MAX;
    assert!(generate(&image(), &input)
        .unwrap_err()
        .contains("checkpoint"));
}

#[test]
fn rejects_guard_with_wrong_successor() {
    let mut input = inputs();
    input.guard_pins[0].on_success = 200;
    assert!(generate(&image(), &input).unwrap_err().contains("guard"));
}

#[test]
fn rejects_unsupported_schema() {
    let mut input = inputs();
    input.schema_version = 2;
    assert!(generate(&image(), &input)
        .unwrap_err()
        .contains("schema version"));
}

#[test]
fn rejects_non_cut_checkpoint_set() {
    let mut input = inputs();
    input.edges[0].checkpoints.pop();
    assert!(generate(&image(), &input)
        .unwrap_err()
        .contains("do not cut"));
}

#[test]
fn rejects_invalid_field_name() {
    let mut input = inputs();
    input.readable_fields[0].name = "x\naxiom injected : False".into();
    assert!(generate(&image(), &input)
        .unwrap_err()
        .contains("readable field"));
}

#[test]
fn rejects_unknown_json_fields() {
    let mut json = serde_json::to_value(
        serde_json::from_str::<serde_json::Value>(include_str!(
            "../../../examples/lean/PToken/success-proof-inputs.json"
        ))
        .unwrap(),
    )
    .unwrap();
    json["typo"] = true.into();
    assert!(serde_json::from_value::<BaselineInputs>(json).is_err());
}

struct TempDir(std::path::PathBuf);
impl TempDir {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "qed-success-proofs-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn cli(manifest: &Path, output: &Path, check: bool) -> std::process::Output {
    let mut command = std::process::Command::new(env!("CARGO_BIN_EXE_qed-success-proofs"));
    command
        .arg("../tests/fixtures/p_token.so")
        .arg(manifest)
        .arg(output);
    if check {
        command.arg("--check");
    }
    command.output().unwrap()
}

#[test]
fn cli_regenerates_checks_and_rejects_drift_without_writing() {
    let tmp = TempDir::new();
    let manifest = Path::new("../../examples/lean/PToken/success-proof-inputs.json");
    let result = cli(manifest, &tmp.0, false);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let paths = tmp.0.join("SuccessPaths.lean");
    assert_eq!(
        std::fs::read_to_string(&paths).unwrap(),
        include_str!("../../../examples/lean/PToken/SuccessPaths.lean")
    );
    assert!(cli(manifest, &tmp.0, true).status.success());
    std::fs::write(&paths, "drift\n").unwrap();
    let result = cli(manifest, &tmp.0, true);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("drift"));
    assert_eq!(std::fs::read_to_string(&paths).unwrap(), "drift\n");
}

#[test]
fn cli_bad_artifact_does_not_create_output() {
    let tmp = TempDir::new();
    let output = tmp.0.join("absent");
    let manifest = tmp.0.join("bad.json");
    let mut json: serde_json::Value = serde_json::from_str(include_str!(
        "../../../examples/lean/PToken/success-proof-inputs.json"
    ))
    .unwrap();
    json["artifact_sha256"] = "0".repeat(64).into();
    std::fs::write(&manifest, serde_json::to_string(&json).unwrap()).unwrap();
    let result = cli(&manifest, &output, false);
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("artifact SHA-256"));
    assert!(!output.exists());
}

#[test]
fn lean_embedding_and_function_registry_match_the_bound_elf() {
    let image = image();
    let lean = include_str!("../../../examples/lean/Generated/PTokenText.lean");
    let hex = lean
        .split_once("def PTokenText : ByteArray := Decode.bytesOfHex \"")
        .unwrap()
        .1
        .split_once('"')
        .unwrap()
        .0;
    let hex: String = hex.chars().filter(|c| !c.is_whitespace()).collect();
    let bytes: Vec<u8> = hex
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect();
    assert_eq!(hex.len() % 2, 0);
    assert_eq!(bytes, image.text_bytes);

    let registry = lean
        .split_once("def PTokenFnRegistry : List (Nat × Nat) := [")
        .unwrap()
        .1
        .split_once(']')
        .unwrap()
        .0;
    let numbers: Vec<usize> = registry
        .split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .map(|s| s.parse().unwrap())
        .collect();
    assert_eq!(numbers.len() % 2, 0);
    let expected: Vec<_> = numbers
        .chunks_exact(2)
        .map(|pair| (pair[0] as u32, pair[1]))
        .collect();
    let mut actual: Vec<_> = image
        .executable
        .get_function_registry()
        .iter()
        .map(|(key, (_, slot))| (key, slot))
        .collect();
    actual.sort_unstable();
    assert_eq!(actual, expected);
}
