//! `disasm-to-lean` — convert `llvm-objdump -d` output to Lean `Insn`
//! syntax for the qedsvm spec layer.
//!
//! Eliminates hand-transcription when lifting a slice of compiled sBPF
//! into a Hoare-triple proof. Output is the `CodeReq` singleton-union
//! chain matching the shape `Macros.lean` and `PTokenValidationPrelude.lean`
//! use directly — paste under a `def myCr : CodeReq := ...` to get the
//! code requirement for the slice.
//!
//! Usage:
//! ```
//! cargo run --bin disasm-to-lean -- path/to/disasm.txt
//! cargo run --bin disasm-to-lean < disasm.txt
//! cargo run --bin disasm-to-lean -- disasm.txt --range 0xba0-0xbd8
//! ```
//!
//! Range filter (`--range start-end`): only emit instructions whose byte
//! offset falls inside `[start, end]` (inclusive). Both bounds are hex,
//! with or without `0x` prefix. Useful when lifting a small slice out of
//! a large disassembly.
//!
//! PC numbering: emitted PCs start at 0 for the first matched instruction
//! and increment by 1 per logical instruction. `lddw` is 16 bytes but
//! counts as 1 logical PC slot per the spec layer's `Insn` model.
//!
//! Known limitations (this is a transcription helper, not a full decoder):
//! - Branch targets are computed as `current_pc + 1 + relative_offset`.
//!   This is the *byte-slot* arithmetic and is correct iff the source
//!   and target PCs aren't separated by a `lddw` (which adds a PC-skew).
//!   For programs with lddw between branch and target, post-process the
//!   target value manually.
//! - `call IMM` is emitted as `.call_local IMM` (sBPF's PC-relative call
//!   form). Syscall `call` (src=0 in the encoding) needs manual rewrite
//!   to `.call <Syscall>`.
//! - Unsupported opcodes are emitted as `/* TODO: <mnem> <ops> */`.

use std::io::{self, Read, Write};

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut path: Option<String> = None;
    let mut range: Option<(u64, u64)> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
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
        let lean = encode_insn(pc, &mnem, &operands);
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

    // Emit a left-folded singleton.union chain, matching the shape used
    // throughout Macros.lean and PTokenValidationPrelude.lean.
    writeln!(out, "/- {} instructions, paste under `def myCr : CodeReq := ...` -/", lines_out.len())?;
    let n = lines_out.len();
    if n == 1 {
        writeln!(out, "{}", lines_out[0])?;
        return Ok(());
    }
    // For n ≥ 2: ((((s0).union s1).union s2)...).union sN-1
    // Opens: n-1 leading `(`; each line after the first prefixed with `).union` and indented.
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
    // llvm-objdump separates the hex-bytes column from the disassembly
    // column with a tab. Anything before the tab is bytes; after is asm.
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
    // llvm-objdump appends "<.text+0x...>" or "<entrypoint+0x...>" after
    // jump targets and call destinations. Drop everything from the first
    // '<' onward.
    match s.find('<') {
        Some(idx) => s[..idx].trim(),
        None => s.trim(),
    }
}

fn encode_insn(pc: u64, mnem: &str, operands: &str) -> String {
    let ops: Vec<&str> = operands.split(',').map(str::trim).collect();
    match mnem {
        // ALU 64-bit (imm + reg variants share the same shape).
        "mov64" | "add64" | "sub64" | "mul64" | "div64" | "mod64"
        | "or64" | "and64" | "xor64" | "lsh64" | "rsh64" | "arsh64" => {
            format!(".{} {} {}", mnem, parse_reg(ops[0]), parse_src(ops[1]))
        }
        "neg64" => format!(".neg64 {}", parse_reg(ops[0])),
        // ALU 32-bit.
        "mov32" | "add32" | "sub32" | "mul32" | "div32" | "mod32"
        | "or32" | "and32" | "xor32" | "lsh32" | "rsh32" | "arsh32" => {
            format!(".{} {} {}", mnem, parse_reg(ops[0]), parse_src(ops[1]))
        }
        "neg32" => format!(".neg32 {}", parse_reg(ops[0])),
        // Memory loads (reg-indexed).
        "ldxb" => encode_ldx("byte", &ops),
        "ldxh" => encode_ldx("half", &ops),
        "ldxw" => encode_ldx("word", &ops),
        "ldxdw" => encode_ldx("dword", &ops),
        // Memory stores (reg source).
        "stxb" => encode_stx("byte", &ops),
        "stxh" => encode_stx("half", &ops),
        "stxw" => encode_stx("word", &ops),
        "stxdw" => encode_stx("dword", &ops),
        // Conditional jumps. `target` is absolute PC = current pc + 1 + relative.
        "jeq" | "jne" | "jgt" | "jge" | "jlt" | "jle"
        | "jsgt" | "jsge" | "jslt" | "jsle" | "jset" => encode_jcc(mnem, pc, &ops),
        // Unconditional jump.
        "ja" => {
            let off_str = strip_label_annotation(ops[0]).trim_start_matches('+');
            let off = parse_int(off_str);
            let target = (pc as i64) + 1 + off;
            format!(".ja {}", paren_signed(target))
        }
        // 64-bit immediate load (16-byte instruction; counts as 2 PC slots).
        "lddw" => format!(".lddw {} {}", parse_reg(ops[0]), parse_int(ops[1])),
        // PC-relative function call. Syscall variant needs manual rewrite.
        "call" => format!(".call_local {}", parse_int(strip_label_annotation(ops[0]))),
        // Indirect call.
        "callx" => format!(".callx {}", parse_reg(ops[0])),
        "exit" => ".exit".to_string(),
        _ => format!("/* TODO: {} {} */", mnem, operands),
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
    if neg { -n } else { n }
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
    // "[rN + off]" or "[rN - off]" or "[rN]" (off = 0).
    let s = s.trim().trim_start_matches('[').trim_end_matches(']').trim();
    // Find the first `+` or `-` that isn't part of `r10` etc. Since reg
    // names contain only digits, the first such char delimits the offset.
    let split = s.bytes().position(|b| b == b'+' || b == b'-');
    match split {
        Some(idx) => {
            let reg = parse_reg(s[..idx].trim());
            // Include the sign in the offset string.
            let off_str = s[idx..].trim();
            let off = parse_int(off_str);
            (reg, off)
        }
        None => (parse_reg(s), 0),
    }
}

fn encode_ldx(width: &str, ops: &[&str]) -> String {
    // ldxX dst, [src + off]
    let dst = parse_reg(ops[0]);
    let (src, off) = parse_mem_operand(ops[1]);
    format!(".ldx .{} {} {} {}", width, dst, src, paren_signed(off))
}

fn encode_stx(width: &str, ops: &[&str]) -> String {
    // stxX [dst + off], src
    let (dst, off) = parse_mem_operand(ops[0]);
    let src = parse_reg(ops[1]);
    format!(".stx .{} {} {} {}", width, dst, paren_signed(off), src)
}

/// Wrap negative literals in parens so Lean parses them as a single
/// argument rather than `Neg.neg` applied to the next token.
fn paren_signed(n: i64) -> String {
    if n < 0 { format!("({})", n) } else { format!("{}", n) }
}

fn encode_jcc(mnem: &str, pc: u64, ops: &[&str]) -> String {
    // jcc dst, src, +rel
    let dst = parse_reg(ops[0]);
    let src = parse_src(ops[1]);
    let off_str = strip_label_annotation(ops[2]).trim_start_matches('+');
    let off = parse_int(off_str);
    let target = (pc as i64) + 1 + off;
    format!(".{} {} {} {}", mnem, dst, src, paren_signed(target))
}
