//! `disasm-to-lean` — convert `llvm-objdump -d` output to Lean `Insn` syntax for the qedsvm spec layer.
//!
//! Gotchas: branch targets use byte-slot arithmetic — a `lddw` between branch and target skews the PC;
//! fix manually. `call IMM` emits `.call_local`; syscall `call` (src=0) needs a manual rewrite to
//! `.call <Syscall>`. Unsupported or malformed instructions fail the command;
//! pass `--allow-partial` to emit diagnostic comments during exploratory work.

use std::io::{self, Read, Write};

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut path: Option<String> = None;
    let mut range: Option<(u64, u64)> = None;
    let mut allow_partial = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--allow-partial" => {
                allow_partial = true;
                i += 1;
            }
            "--range" => {
                let r = args.get(i + 1).expect("--range requires an argument");
                range = Some(parse_range(r));
                i += 2;
            }
            other => {
                if path.is_none() {
                    path = Some(other.to_string());
                }
                i += 1;
            }
        }
    }

    let mut input = String::new();
    if let Some(p) = path {
        input = std::fs::read_to_string(p)?;
    } else {
        io::stdin().read_to_string(&mut input)?;
    }

    let mut lines_out: Vec<String> = Vec::new();
    let mut pc: u64 = 0;
    for line in input.lines() {
        let parsed = match parse_disasm_line(line) {
            Some(p) => p,
            None => continue,
        };
        let (byte_off, mnem, operands) = parsed;
        if let Some((lo, hi)) = range {
            if byte_off < lo || byte_off > hi {
                continue;
            }
        }
        let lean = match encode_insn(pc, &mnem, &operands) {
            Ok(lean) => lean,
            Err(message) if allow_partial => format!("/* ERROR: {message} */"),
            Err(message) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "{byte_off:#x}: {message}; rerun with --allow-partial to emit a comment"
                    ),
                ));
            }
        };
        lines_out.push(format!(
            "  (CodeReq.singleton {} ({}))  -- {:#x}: {} {}",
            pc, lean, byte_off, mnem, operands
        ));
        pc += if mnem == "lddw" { 2 } else { 1 };
    }

    let stdout = io::stdout();
    let mut out = stdout.lock();

    if lines_out.is_empty() {
        writeln!(out, "/- no instructions matched -/")?;
        return Ok(());
    }

    // Left-folded singleton.union chain: shape expected by Macros.lean / PTokenValidationPrelude.lean.
    writeln!(
        out,
        "/- {} instructions, paste under `def myCr : CodeReq := ...` -/",
        lines_out.len()
    )?;
    let n = lines_out.len();
    if n == 1 {
        writeln!(out, "{}", lines_out[0])?;
        return Ok(());
    }
    // n-1 leading `(` then each subsequent line prefixed with `).union`.
    let opens = "(".repeat(n - 1);
    writeln!(out, "{}{}", opens, lines_out[0].trim_start())?;
    for line in &lines_out[1..] {
        writeln!(out, "  ).union {}", line.trim_start())?;
    }

    Ok(())
}

fn parse_range(s: &str) -> (u64, u64) {
    let mid = s.find('-').expect("--range expects START-END");
    let lo = parse_hex_u64(&s[..mid]);
    let hi = parse_hex_u64(&s[mid + 1..]);
    (lo, hi)
}

fn parse_hex_u64(s: &str) -> u64 {
    let s = s.trim().trim_start_matches("0x");
    u64::from_str_radix(s, 16).expect("expected hex number")
}

fn parse_disasm_line(line: &str) -> Option<(u64, String, String)> {
    let trimmed = line.trim_start();
    let colon = trimmed.find(':')?;
    let byte_off = u64::from_str_radix(trimmed[..colon].trim(), 16).ok()?;
    let rest = &trimmed[colon + 1..];
    // llvm-objdump: tab separates hex-bytes column from asm column.
    let tab = rest.find('\t')?;
    let asm = rest[tab..].trim();
    if asm.is_empty() {
        return None;
    }
    let space = asm.find(char::is_whitespace).unwrap_or(asm.len());
    let mnem = asm[..space].to_string();
    let operands = asm[space..].trim().to_string();
    if mnem.is_empty() {
        return None;
    }
    Some((byte_off, mnem, operands))
}

fn strip_label_annotation(s: &str) -> &str {
    // llvm-objdump appends "<.text+0x...>" or "<entrypoint+0x...>" after jump/call targets.
    match s.find('<') {
        Some(idx) => s[..idx].trim(),
        None => s.trim(),
    }
}

fn encode_insn(pc: u64, mnem: &str, operands: &str) -> Result<String, String> {
    let ops: Vec<&str> = operands.split(',').map(str::trim).collect();
    let expected = match mnem {
        "exit" => 0,
        "neg64" | "neg32" | "ja" | "call" | "callx" => 1,
        "jeq" | "jne" | "jgt" | "jge" | "jlt" | "jle" | "jsgt" | "jsge" | "jslt" | "jsle"
        | "jset" => 3,
        "mov64" | "add64" | "sub64" | "mul64" | "div64" | "mod64" | "or64" | "and64" | "xor64"
        | "lsh64" | "rsh64" | "arsh64" | "mov32" | "add32" | "sub32" | "mul32" | "div32"
        | "mod32" | "or32" | "and32" | "xor32" | "lsh32" | "rsh32" | "arsh32" | "ldxb" | "ldxh"
        | "ldxw" | "ldxdw" | "stxb" | "stxh" | "stxw" | "stxdw" | "lddw" => 2,
        _ => {
            return Err(format!(
                "unsupported opcode `{mnem}` with operands `{operands}`"
            ))
        }
    };
    let actual = if operands.trim().is_empty() {
        0
    } else {
        ops.len()
    };
    if actual != expected {
        return Err(format!(
            "opcode `{mnem}` expects {expected} operand(s), got {actual}"
        ));
    }

    let encoded = match mnem {
        "mov64" | "add64" | "sub64" | "mul64" | "div64" | "mod64" | "or64" | "and64" | "xor64"
        | "lsh64" | "rsh64" | "arsh64" => {
            format!(".{} {} {}", mnem, parse_reg(ops[0]), parse_src(ops[1]))
        }
        "neg64" => format!(".neg64 {}", parse_reg(ops[0])),
        "mov32" | "add32" | "sub32" | "mul32" | "div32" | "mod32" | "or32" | "and32" | "xor32"
        | "lsh32" | "rsh32" | "arsh32" => {
            format!(".{} {} {}", mnem, parse_reg(ops[0]), parse_src(ops[1]))
        }
        "neg32" => format!(".neg32 {}", parse_reg(ops[0])),
        "ldxb" => encode_ldx("byte", &ops),
        "ldxh" => encode_ldx("half", &ops),
        "ldxw" => encode_ldx("word", &ops),
        "ldxdw" => encode_ldx("dword", &ops),
        "stxb" => encode_stx("byte", &ops),
        "stxh" => encode_stx("half", &ops),
        "stxw" => encode_stx("word", &ops),
        "stxdw" => encode_stx("dword", &ops),
        // `target` = absolute PC = current_pc + 1 + relative_offset.
        "jeq" | "jne" | "jgt" | "jge" | "jlt" | "jle" | "jsgt" | "jsge" | "jslt" | "jsle"
        | "jset" => encode_jcc(mnem, pc, &ops),
        "ja" => {
            let off_str = strip_label_annotation(ops[0]).trim_start_matches('+');
            let off = parse_int(off_str);
            let target = (pc as i64) + 1 + off;
            format!(".ja {}", paren_signed(target))
        }
        // lddw is 16 bytes but counts as 1 logical PC slot in the spec layer's Insn model.
        "lddw" => format!(".lddw {} {}", parse_reg(ops[0]), parse_int(ops[1])),
        "call" => format!(".call_local {}", parse_int(strip_label_annotation(ops[0]))),
        "callx" => format!(".callx {}", parse_reg(ops[0])),
        "exit" => ".exit".to_string(),
        _ => unreachable!("supported opcode set checked above"),
    };
    if encoded.contains("/*") {
        Err(format!("malformed `{mnem} {operands}`"))
    } else {
        Ok(encoded)
    }
}

fn parse_reg(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('r') {
        format!(".{}", s)
    } else {
        format!("/* not a reg: {:?} */", s)
    }
}

fn parse_int(s: &str) -> i64 {
    let s = s.trim();
    let (neg, body) = if let Some(stripped) = s.strip_prefix('-') {
        (true, stripped.trim())
    } else if let Some(stripped) = s.strip_prefix('+') {
        (false, stripped.trim())
    } else {
        (false, s)
    };
    let n = if let Some(hex) = body.strip_prefix("0x") {
        i64::from_str_radix(hex, 16).unwrap_or(0)
    } else {
        body.parse::<i64>().unwrap_or(0)
    };
    if neg {
        -n
    } else {
        n
    }
}

fn parse_src(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('r') {
        format!("(.reg {})", parse_reg(s))
    } else {
        format!("(.imm {})", parse_int(s))
    }
}

fn parse_mem_operand(s: &str) -> (String, i64) {
    let s = s
        .trim()
        .trim_start_matches('[')
        .trim_end_matches(']')
        .trim();
    // Reg names contain only digits, so the first `+`/`-` always delimits the offset.
    let split = s.bytes().position(|b| b == b'+' || b == b'-');
    match split {
        Some(idx) => {
            let reg = parse_reg(s[..idx].trim());
            let off_str = s[idx..].trim();
            let off = parse_int(off_str); // sign included
            (reg, off)
        }
        None => (parse_reg(s), 0),
    }
}

fn encode_ldx(width: &str, ops: &[&str]) -> String {
    let dst = parse_reg(ops[0]);
    let (src, off) = parse_mem_operand(ops[1]);
    format!(".ldx .{} {} {} {}", width, dst, src, paren_signed(off))
}

fn encode_stx(width: &str, ops: &[&str]) -> String {
    let (dst, off) = parse_mem_operand(ops[0]);
    let src = parse_reg(ops[1]);
    format!(".stx .{} {} {} {}", width, dst, paren_signed(off), src)
}

/// Wrap negative literals in parens so Lean parses them as a single
/// argument rather than `Neg.neg` applied to the next token.
fn paren_signed(n: i64) -> String {
    if n < 0 {
        format!("({})", n)
    } else {
        format!("{}", n)
    }
}

fn encode_jcc(mnem: &str, pc: u64, ops: &[&str]) -> String {
    let dst = parse_reg(ops[0]);
    let src = parse_src(ops[1]);
    let off_str = strip_label_annotation(ops[2]).trim_start_matches('+');
    let off = parse_int(off_str);
    let target = (pc as i64) + 1 + off;
    format!(".{} {} {} {}", mnem, dst, src, paren_signed(target))
}

#[cfg(test)]
mod tests {
    use super::encode_insn;

    #[test]
    fn unsupported_opcode_fails_closed() {
        assert!(encode_insn(0, "atomic", "r0, r1").is_err());
    }

    #[test]
    fn malformed_operands_fail_closed() {
        assert!(encode_insn(0, "add64", "r0").is_err());
        assert!(encode_insn(0, "add64", "not_a_register, 1").is_err());
    }

    #[test]
    fn supported_opcode_is_unchanged() {
        assert_eq!(
            encode_insn(0, "add64", "r0, 1").unwrap(),
            ".add64 .r0 (.imm 1)"
        );
    }
}
