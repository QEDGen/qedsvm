use object::{Object, ObjectSection};
use qed_analysis::concept_map::ConceptMap;
use serde_json::Value;

const DEPLOYED: &[u8] = include_bytes!("../../tests/fixtures/debug_concepts.so");
const DEBUG: &[u8] = include_bytes!("../../tests/fixtures/debug_concepts.debug");

fn map() -> Value {
    let map = ConceptMap::from_elf_bytes(DEPLOYED, DEBUG).expect("matched build");
    serde_json::from_str(&map.to_json().unwrap()).unwrap()
}

#[test]
fn actual_sbf_build_recovers_inline_chains_layouts_and_discriminants() {
    let map = map();
    assert_eq!(map["schema_version"], 1);
    assert_eq!(map["trust"], "untrusted_debug_labels");
    assert_eq!(map["pc_convention"], "logical_lddw_once");
    let functions = map["functions"].as_array().unwrap();
    for name in ["entrypoint", "transfer", "authorize"] {
        assert!(
            functions
                .iter()
                .any(|f| f["name"].as_str().unwrap_or("").contains(name)),
            "missing {name}"
        );
    }
    let structures = map["structures"].as_array().unwrap();
    let account = structures
        .iter()
        .find(|s| s["name"] == "Account")
        .expect("Account layout");
    assert_eq!(account["byte_size"], 48);
    let members = account["members"].as_array().unwrap();
    for (name, offset) in [("authority", 0), ("amount", 32), ("state", 40)] {
        assert!(members
            .iter()
            .any(|m| m["name"] == name && m["byte_offset"] == offset));
    }
    let enums = map["enumerations"].as_array().unwrap();
    let error = enums.iter().find(|e| e["name"] == "Error").unwrap();
    assert!(error["variants"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v["name"] == "Frozen" && v["value"] == "42"));
    let signed = enums.iter().find(|e| e["name"] == "SignedError").unwrap();
    assert!(signed["variants"]
        .as_array()
        .unwrap()
        .iter()
        .any(|v| v["name"] == "Negative" && v["value"] == "-3"));
    let lines = map["lines"].as_array().unwrap();
    assert!(lines.iter().any(|l| l["location"]["file"]
        .as_str()
        .unwrap_or("")
        .ends_with("src/lib.rs")
        && l["location"]["line"].as_u64().unwrap_or(0) > 0));
    let entry = functions
        .iter()
        .find(|f| f["name"] == "entrypoint")
        .unwrap();
    let transfer = functions
        .iter()
        .find(|f| f["name"].as_str().unwrap_or("").ends_with("::transfer"))
        .unwrap();
    let authorize = functions
        .iter()
        .find(|f| f["name"].as_str().unwrap_or("").ends_with("::authorize"))
        .unwrap();
    assert_eq!(transfer["parent"], entry["id"]);
    assert_eq!(authorize["parent"], transfer["id"]);
    assert_eq!(transfer["call_site"]["line"], 40);
    assert_eq!(authorize["call_site"]["line"], 27);
    let chain = serde_json::json!([entry["id"], transfer["id"], authorize["id"]]);
    assert!(
        lines.iter().any(|l| l["location"]["line"] == 22
            && l["range"] == serde_json::json!({"start":2,"end":4})
            && l["inline_chains"].as_array().unwrap().contains(&chain)),
        "authorize source line and ancestry"
    );
    assert!(
        map["artifact"]["logical_instruction_count"]
            .as_u64()
            .unwrap()
            < map["artifact"]["text_byte_size"].as_u64().unwrap() / 8,
        "fixture must exercise lddw"
    );
}

#[test]
fn refuses_same_size_text_mismatch_before_labels() {
    let file = object::File::parse(DEPLOYED).unwrap();
    let (offset, _) = file.section_by_name(".text").unwrap().file_range().unwrap();
    let mut changed = DEPLOYED.to_vec();
    changed[offset as usize + 4] ^= 1;
    let err = ConceptMap::from_elf_bytes(&changed, DEBUG).expect_err("mismatch refused");
    assert!(err.contains(".text mismatch"), "{err}");
}

#[test]
fn stripped_artifact_reports_partial_coverage_and_identity_is_deterministic() {
    let partial = ConceptMap::from_elf_bytes(DEPLOYED, DEPLOYED).unwrap();
    let partial: Value = serde_json::from_str(&partial.to_json().unwrap()).unwrap();
    assert_eq!(partial["coverage"]["debug_info"], false);
    assert_eq!(partial["functions"], serde_json::json!([]));
    assert!(partial["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d["code"] == "missing_debug_info"));
    let first = ConceptMap::from_elf_bytes(DEPLOYED, DEBUG)
        .unwrap()
        .to_json()
        .unwrap();
    let second = ConceptMap::from_elf_bytes(DEPLOYED, DEBUG)
        .unwrap()
        .to_json()
        .unwrap();
    assert_eq!(first, second);
    let map: Value = serde_json::from_str(&first).unwrap();
    assert_ne!(
        map["artifact"]["deployed_sha256"],
        map["artifact"]["debug_sha256"]
    );
    assert_eq!(
        map["artifact"]["text_sha256"],
        "d633362afbcf805a0f7d2191b12d1b5278cbafdf0c518c338ab8a8e7115bbe43"
    );
}

#[test]
fn rejects_malformed_dwarf_without_emitting_partial_labels() {
    let file = object::File::parse(DEBUG).unwrap();
    let (offset, _) = file
        .section_by_name(".debug_info")
        .unwrap()
        .file_range()
        .unwrap();
    let mut malformed = DEBUG.to_vec();
    malformed[offset as usize..offset as usize + 4].copy_from_slice(&[0xff; 4]);
    assert!(ConceptMap::from_elf_bytes(DEPLOYED, &malformed)
        .err()
        .unwrap()
        .contains("DWARF"));
}

#[test]
fn function_ranges_use_logical_boundaries_and_end_of_text() {
    let map = map();
    let functions = map["functions"].as_array().unwrap();
    let entry = functions
        .iter()
        .find(|f| f["name"] == "entrypoint")
        .unwrap();
    // Independent objdump pin: entrypoint spans slots [0,20), with lddw
    // at slots 0 and 14; signed_error spans slots [20,22).
    assert_eq!(
        entry["ranges"],
        serde_json::json!([{ "start": 0, "end": 18 }])
    );
    let helper = functions
        .iter()
        .find(|f| f["name"] == "signed_error")
        .unwrap();
    assert_eq!(
        helper["ranges"],
        serde_json::json!([{ "start": 18, "end": 20 }])
    );
    assert_eq!(map["artifact"]["logical_instruction_count"], 20);
}

#[test]
fn actual_debug_one_build_is_explicitly_partial_for_types() {
    let deployed = include_bytes!("../../tests/fixtures/debug_concepts_limited.so");
    let debug = include_bytes!("../../tests/fixtures/debug_concepts_limited.debug");
    let map = ConceptMap::from_elf_bytes(deployed, debug).unwrap();
    let map: Value = serde_json::from_str(&map.to_json().unwrap()).unwrap();
    assert_eq!(map["coverage"]["debug_info"], true);
    assert_eq!(map["coverage"]["debug_line"], true);
    assert_eq!(map["coverage"]["type_entries"], false);
    assert!(!map["lines"].as_array().unwrap().is_empty());
    assert!(map["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .any(|d| d["code"] == "missing_type_entries"));
}

#[test]
fn cli_emits_consumable_json_and_no_labels_on_failure() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/fixtures");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_qed-concept-map"))
        .arg(root.join("debug_concepts.so"))
        .arg(root.join("debug_concepts.debug"))
        .output()
        .unwrap();
    assert!(output.status.success(), "{:?}", output);
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        json["artifact"]["deployed_sha256"],
        "59e62b350b40eb31f69fe5508f85e822c1ea1c66ace914828e97ca97071dbd08"
    );
    assert_eq!(
        json["artifact"]["debug_sha256"],
        "3bcbe33a849d7aa1d824c069053bf9744cf5db4d25171803e84dc412e68c3840"
    );
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_qed-concept-map"))
        .arg(root.join("debug_concepts.so"))
        .arg(root.join("counter_with_helper.debug"))
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8(output.stderr)
        .unwrap()
        .contains(".text mismatch"));
}

#[test]
fn malformed_inline_abstract_origin_is_an_error_not_a_missing_label() {
    let file = object::File::parse(DEBUG).unwrap();
    let (offset, _) = file
        .section_by_name(".debug_info")
        .unwrap()
        .file_range()
        .unwrap();
    // Pinned full-debug fixture: DIE 0x175 is authorize's inline instance;
    // its first attribute is DW_FORM_ref4 abstract_origin -> DIE 0x5b.
    let start = offset as usize + 0x176;
    assert_eq!(&DEBUG[start..start + 4], &[0x5b, 0, 0, 0]);
    let mut malformed = DEBUG.to_vec();
    malformed[start..start + 4].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(ConceptMap::from_elf_bytes(DEPLOYED, &malformed)
        .expect_err("invalid local DIE reference must fail extraction")
        .contains("DWARF"));
}

#[test]
fn actual_v3_debug_addresses_remain_in_the_high_text_region() {
    let deployed = include_bytes!("../../tests/fixtures/debug_concepts_v3.so");
    let debug = include_bytes!("../../tests/fixtures/debug_concepts_v3.debug");
    let map = ConceptMap::from_elf_bytes(deployed, debug).unwrap();
    assert_eq!(map.artifact.sbpf_version, 3);
    assert_eq!(map.artifact.debug_text_address, 0x1_0000_0000);
    assert!(map
        .functions
        .iter()
        .any(|f| f.name.as_deref() == Some("entrypoint") && f.ranges[0].start == 0));
    assert!(map
        .functions
        .iter()
        .any(|f| f.name.as_deref().unwrap_or("").ends_with("::authorize")));
    assert!(map
        .lines
        .iter()
        .any(|line| line.inline_chains.iter().any(|c| c.len() == 3)));
    assert!(
        !map.diagnostics
            .iter()
            .any(|d| d.code.starts_with("unmapped_")),
        "{:?}",
        map.diagnostics
    );
}
