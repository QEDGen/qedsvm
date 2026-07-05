//! Codama account-data-struct → byte layout (issue #41, Phase 2).
//! IDL-derived field offsets/kinds feed `account_agg` instantiation in refinement codegen.
//! Relocated from qedlift-only to shared substrate so qedrecover can consume field names too.
//! Pure parsing — trusted-input front-end (`docs/TCB.md` §5).

use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum FieldKind {
    Pubkey,       // 32-byte ↦Pubkey (four u64 limbs)
    U64,          // 8-byte ↦U64
    Byte,         // 1-byte ↦ₘ  (u8 / bool / single-byte enum tag)
    Bytes(usize), // opaque region of N bytes (options, arrays, wide scalars)
}

#[derive(Debug, Clone)]
pub struct AccountField {
    pub name:   String,
    pub offset: usize,
    pub kind:   FieldKind,
}

#[derive(Debug, Clone)]
pub struct AccountLayout {
    pub name:   String,
    pub fields: Vec<AccountField>,
    pub size:   usize,
}

/// Byte width of a Codama `numberTypeNode` format string.
pub fn codama_number_size(fmt: &str) -> Option<usize> {
    match fmt {
        "u8" | "i8"     => Some(1),
        "u16" | "i16"   => Some(2),
        "u32" | "i32"   => Some(4),
        "u64" | "i64"   => Some(8),
        "u128" | "i128" => Some(16),
        _ => None,
    }
}

/// Byte size of a Codama type node. Resolves `definedTypeLinkNode`s via `defined`. Returns `None` for variable-size or unsupported nodes.
fn codama_type_size(
    ty: &serde_json::Value,
    defined: &HashMap<String, serde_json::Value>,
) -> Option<usize> {
    match ty.get("kind")?.as_str()? {
        "publicKeyTypeNode" => Some(32),
        "numberTypeNode"    => codama_number_size(ty.get("format")?.as_str()?),
        // Solana COption: a fixed prefix (u32 here) + the item bytes.
        "optionTypeNode" => {
            let prefix = ty.get("prefix")
                .and_then(|p| codama_type_size(p, defined)).unwrap_or(4);
            Some(prefix + codama_type_size(ty.get("item")?, defined)?)
        }
        "booleanTypeNode" => ty.get("size")
            .and_then(|s| codama_type_size(s, defined)).or(Some(1)),
        "enumTypeNode" => ty.get("size")
            .and_then(|s| codama_type_size(s, defined)).or(Some(1)),
        "arrayTypeNode" => {
            let item = codama_type_size(ty.get("item")?, defined)?;
            // `fixedCountNode { value: N }` — older Codama uses `count` key.
            let count = ty.get("count")?;
            let n = count.get("value").or_else(|| count.get("count"))?.as_u64()? as usize;
            Some(item * n)
        }
        "fixedSizeTypeNode" => ty.get("size")?.as_u64().map(|n| n as usize),
        "definedTypeLinkNode" => {
            let name = ty.get("name")?.as_str()?;
            codama_type_size(defined.get(name)?.get("type")?, defined)
        }
        _ => None,
    }
}

/// Map a Codama type node to its codec `FieldKind`.
fn codama_field_kind(
    ty: &serde_json::Value,
    defined: &HashMap<String, serde_json::Value>,
) -> Option<FieldKind> {
    let size = codama_type_size(ty, defined)?;
    let resolved = if ty.get("kind").and_then(|k| k.as_str()) == Some("definedTypeLinkNode") {
        let name = ty.get("name")?.as_str()?;
        defined.get(name)?.get("type")?
    } else {
        ty
    };
    Some(match resolved.get("kind").and_then(|k| k.as_str()) {
        Some("publicKeyTypeNode")              => FieldKind::Pubkey,
        Some("numberTypeNode") if size == 8    => FieldKind::U64,
        Some("numberTypeNode") if size == 1    => FieldKind::Byte,
        Some("booleanTypeNode") if size == 1   => FieldKind::Byte,
        Some("enumTypeNode") if size == 1      => FieldKind::Byte,
        _                                      => FieldKind::Bytes(size),
    })
}

/// Parse a Codama account-data struct into a byte layout. Accepts a full Codama root or bare `program` object.
pub fn parse_account_layout(
    root: &serde_json::Value,
    name: &str,
) -> Result<AccountLayout, Box<dyn std::error::Error>> {
    let prog = root.get("program").unwrap_or(root);
    let defined: HashMap<String, serde_json::Value> = prog
        .get("definedTypes").and_then(|v| v.as_array())
        .map(|arr| arr.iter()
            .filter_map(|t| Some((t.get("name")?.as_str()?.to_string(), t.clone())))
            .collect())
        .unwrap_or_default();
    let accts = prog.get("accounts").and_then(|v| v.as_array())
        .ok_or("codama: /program/accounts missing")?;
    let acct = accts.iter()
        .find(|a| a.get("name").and_then(|n| n.as_str()) == Some(name))
        .ok_or_else(|| format!("codama: account {:?} not found", name))?;
    let fields_json = acct.pointer("/data/fields").and_then(|v| v.as_array())
        .ok_or_else(|| format!("codama: account {:?} has no data.fields", name))?;

    let mut offset = 0usize;
    let mut fields = Vec::new();
    for f in fields_json {
        let fname = f.get("name").and_then(|n| n.as_str()).unwrap_or("?").to_string();
        let ty = f.get("type").ok_or("codama: field has no type")?;
        let size = codama_type_size(ty, &defined)
            .ok_or_else(|| format!("codama: field {:?}: unsupported type node", fname))?;
        let kind = codama_field_kind(ty, &defined)
            .ok_or_else(|| format!("codama: field {:?}: unclassifiable", fname))?;
        fields.push(AccountField { name: fname, offset, kind });
        offset += size;
    }
    Ok(AccountLayout { name: name.to_string(), fields, size: offset })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn idl() -> serde_json::Value {
        let text = std::fs::read_to_string("../tests/fixtures/spl_token.codama.json")
            .expect("read spl_token.codama.json");
        serde_json::from_str(&text).expect("parse IDL")
    }

    #[test]
    fn token_account_layout() {
        let l = parse_account_layout(&idl(), "token").unwrap();
        assert_eq!(l.size, 165, "SPL token account is 165 bytes");
        let by = |n: &str| l.fields.iter().find(|f| f.name == n).unwrap();
        assert_eq!((by("mint").offset,   by("mint").kind.clone()),   (0,  FieldKind::Pubkey));
        assert_eq!((by("owner").offset,  by("owner").kind.clone()),  (32, FieldKind::Pubkey));
        assert_eq!((by("amount").offset, by("amount").kind.clone()), (64, FieldKind::U64));
        // delegate (option<pubkey>) starts the opaque rest region at 72.
        assert_eq!(by("delegate").offset, 72);
        assert_eq!((by("state").offset, by("state").kind.clone()), (108, FieldKind::Byte));
    }

    #[test]
    fn mint_account_layout() {
        let l = parse_account_layout(&idl(), "mint").unwrap();
        assert_eq!(l.size, 82, "SPL mint account is 82 bytes");
        let supply = l.fields.iter().find(|f| f.name == "supply").unwrap();
        assert_eq!((supply.offset, supply.kind.clone()), (36, FieldKind::U64));
    }
}
