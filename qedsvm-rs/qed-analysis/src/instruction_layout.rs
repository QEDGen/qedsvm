//! Conservative fixed-width Codama instruction argument layout.
//! Discriminators are serialized arguments too; do not add them a second time.

use serde_json::Value;

/// Resolve a named little-endian u64 argument to its instruction-data offset.
/// Unknown/variable-size preceding types and ambiguous names fail closed.
pub fn u64_argument_offset(root: &Value, handler: &str, argument: &str) -> Result<usize, String> {
    let program = root.get("program").unwrap_or(root);
    let instructions = program
        .get("instructions")
        .and_then(Value::as_array)
        .ok_or("IDL has no instructions")?;
    let matching: Vec<_> = instructions
        .iter()
        .filter(|i| i.get("name").and_then(Value::as_str) == Some(handler))
        .collect();
    if matching.len() != 1 {
        return Err(format!("expected one IDL instruction named {handler:?}"));
    }
    let args = matching[0]
        .get("arguments")
        .and_then(Value::as_array)
        .ok_or("IDL instruction has no arguments")?;
    let matches = args
        .iter()
        .filter(|a| a.get("name").and_then(Value::as_str) == Some(argument))
        .count();
    if matches != 1 {
        return Err(format!(
            "expected one argument named {argument:?} in {handler:?}"
        ));
    }
    let mut offset = 0usize;
    for arg in args {
        let ty = arg.get("type").ok_or("instruction argument has no type")?;
        if arg.get("name").and_then(Value::as_str) == Some(argument) {
            if ty.get("kind").and_then(Value::as_str) != Some("numberTypeNode")
                || ty.get("format").and_then(Value::as_str) != Some("u64")
                || ty.get("endian").and_then(Value::as_str) != Some("le")
            {
                return Err("parameter must be a direct little-endian u64 argument".into());
            }
            return Ok(offset);
        }
        offset = offset
            .checked_add(fixed_width(ty)?)
            .ok_or("argument offset overflow")?;
    }
    Err("argument not found".into())
}

fn fixed_width(ty: &Value) -> Result<usize, String> {
    let number = |v: &Value| {
        v.as_u64()
            .and_then(|n| usize::try_from(n).ok())
            .ok_or_else(|| "invalid fixed width".to_string())
    };
    match ty.get("kind").and_then(Value::as_str) {
        Some("numberTypeNode") => super::layout::codama_number_size(
            ty.get("format").and_then(Value::as_str).unwrap_or(""),
        )
        .ok_or_else(|| "unsupported number type".into()),
        Some("publicKeyTypeNode") => Ok(32),
        Some("arrayTypeNode")
            if ty.pointer("/count/kind").and_then(Value::as_str) == Some("fixedCountNode") =>
        {
            let n = number(ty.pointer("/count/value").ok_or("missing fixed count")?)?;
            fixed_width(ty.get("item").ok_or("missing array item")?)?
                .checked_mul(n)
                .ok_or_else(|| "array width overflow".into())
        }
        Some("fixedSizeTypeNode") => number(ty.get("size").ok_or("missing fixed size")?),
        _ => Err("variable-size or unsupported argument precedes parameter".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn counts_serialized_discriminator_once() {
        let idl = json!({"instructions":[{"name":"deposit", "arguments":[
            {"name":"discriminator", "type":{"kind":"numberTypeNode", "format":"u8"}},
            {"name":"amount", "type":{"kind":"numberTypeNode", "format":"u64", "endian":"le"}}
        ], "discriminators":[{"kind":"fieldDiscriminatorNode", "name":"discriminator"}]}]});
        assert_eq!(u64_argument_offset(&idl, "deposit", "amount"), Ok(1));
        assert!(u64_argument_offset(&idl, "deposit", "missing").is_err());
        assert!(u64_argument_offset(&idl, "wrong_handler", "amount").is_err());
    }

    #[test]
    fn rejects_ambiguous_or_non_u64_arguments_and_variable_prefixes() {
        let argument = json!({"name":"amount", "type":{"kind":"numberTypeNode", "format":"u64", "endian":"le"}});
        for args in [
            json!([argument, argument]),
            json!([{"name":"amount", "type":{"kind":"numberTypeNode", "format":"u64", "endian":"be"}}]),
            json!([{"name":"amount", "type":{"kind":"numberTypeNode", "format":"i64", "endian":"le"}}]),
            json!([{"name":"prefix", "type":{"kind":"optionTypeNode", "item":{"kind":"numberTypeNode", "format":"u64"}}}, argument]),
        ] {
            let idl = json!({"instructions":[{"name":"deposit", "arguments":args}]});
            assert!(u64_argument_offset(&idl, "deposit", "amount").is_err());
        }
    }

    #[test]
    fn fixed_array_prefix_and_overflow_are_checked() {
        let mut idl = json!({"program":{"instructions":[{"name":"deposit", "arguments":[
            {"name":"prefix", "type":{"kind":"arrayTypeNode", "count":{"kind":"fixedCountNode", "value":3}, "item":{"kind":"numberTypeNode", "format":"u16"}}},
            {"name":"amount", "type":{"kind":"numberTypeNode", "format":"u64", "endian":"le"}}
        ]}]}});
        assert_eq!(u64_argument_offset(&idl, "deposit", "amount"), Ok(6));
        idl["program"]["instructions"][0]["arguments"][0]["type"]["count"]["value"] =
            json!(u64::MAX);
        assert!(u64_argument_offset(&idl, "deposit", "amount").is_err());
        let duplicate = idl["program"]["instructions"][0].clone();
        idl["program"]["instructions"]
            .as_array_mut()
            .unwrap()
            .push(duplicate);
        assert!(u64_argument_offset(&idl, "deposit", "amount").is_err());
    }
}
