//! `qedsvm-cli` — drive the Lean reference SVM from the shell.

use std::process::ExitCode;

use qedsvm::{run_buffer, run_buffer_with_registry, ExitOutcome};

const USAGE: &str = "\
qedsvm-cli — execute a Solana ELF under the qedsvm Lean reference VM.

USAGE:
  qedsvm-cli --elf <path> --input <path> [OPTIONS]

REQUIRED:
  --elf <path>       Path to the program ELF (sBPF, version 1).
  --input <path>     Path to the serialized input region (account
                     buffers + instruction data, as `serialize_parameters`
                     would produce). Empty file is valid.

OPTIONS:
  --cu-budget <n>    Compute-unit budget (default: 200000).
  --registry <path>  CPI program registry blob (see
                     `qedsvm::encode_registry`). Without this,
                     `sol_invoke_signed` callees aren't resolvable.
  --hex-bytes <n>    Hex-truncate modified-input / return-data dumps
                     to this many bytes (default: 64).
  -h, --help         Show this help.
";

fn main() -> ExitCode {
    match real_main() {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}

fn real_main() -> Result<ExitCode, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "-h" || a == "--help") || args.is_empty() {
        print!("{USAGE}");
        return Ok(ExitCode::SUCCESS);
    }

    let mut elf_path: Option<String> = None;
    let mut input_path: Option<String> = None;
    let mut registry_path: Option<String> = None;
    let mut cu_budget: u64 = 200_000;
    let mut hex_bytes: usize = 64;

    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        match a.as_str() {
            "--elf"        => { elf_path      = Some(next_arg(&args, &mut i, "--elf")?); }
            "--input"      => { input_path    = Some(next_arg(&args, &mut i, "--input")?); }
            "--registry"   => { registry_path = Some(next_arg(&args, &mut i, "--registry")?); }
            "--cu-budget"  => {
                let v = next_arg(&args, &mut i, "--cu-budget")?;
                cu_budget = v.parse::<u64>()
                    .map_err(|e| format!("--cu-budget: {e}"))?;
            }
            "--hex-bytes" => {
                let v = next_arg(&args, &mut i, "--hex-bytes")?;
                hex_bytes = v.parse::<usize>()
                    .map_err(|e| format!("--hex-bytes: {e}"))?;
            }
            _ => return Err(format!("unexpected argument: {a}")),
        }
        i += 1;
    }

    let elf_path = elf_path.ok_or("missing required --elf")?;
    let input_path = input_path.ok_or("missing required --input")?;

    let elf = std::fs::read(&elf_path)
        .map_err(|e| format!("read --elf {elf_path}: {e}"))?;
    let input = std::fs::read(&input_path)
        .map_err(|e| format!("read --input {input_path}: {e}"))?;

    let result = if let Some(reg_path) = registry_path {
        let registry = std::fs::read(&reg_path)
            .map_err(|e| format!("read --registry {reg_path}: {e}"))?;
        run_buffer_with_registry(&elf, &input, &registry, cu_budget)
    } else {
        run_buffer(&elf, &input, cu_budget)
    }
    .map_err(|e| format!("Lean VM: {e}"))?;

    let outcome_str = match &result.outcome {
        ExitOutcome::OutOfBudget => "out-of-budget".to_string(),
        ExitOutcome::Halted(r0) => format!("halted r0={r0:#x} ({r0})"),
        ExitOutcome::Faulted(code) => format!("faulted (vmError, sentinel {code:#x})"),
    };
    println!("outcome:                {outcome_str}");
    println!("compute_units_consumed: {}", result.compute_units_consumed);
    println!("log_lines:              {}", result.logs.len());
    for (idx, line) in result.logs.iter().enumerate() {
        let s = String::from_utf8_lossy(line);
        println!("  [{idx:>3}] {s}");
    }
    println!("return_data:            {} bytes", result.return_data.len());
    if !result.return_data.is_empty() {
        println!("  hex: {}", hex_trunc(&result.return_data, hex_bytes));
    }
    println!("modified_input:         {} bytes", result.modified_input.len());
    if !result.modified_input.is_empty() {
        println!("  hex: {}", hex_trunc(&result.modified_input, hex_bytes));
    }

    let code = match &result.outcome {
        ExitOutcome::Halted(0) => ExitCode::SUCCESS,
        _ => ExitCode::FAILURE,
    };
    Ok(code)
}

fn next_arg(args: &[String], i: &mut usize, flag: &str) -> Result<String, String> {
    *i += 1;
    args.get(*i).cloned().ok_or_else(|| format!("{flag} requires a value"))
}

fn hex_trunc(bytes: &[u8], cap: usize) -> String {
    let (slice, more) = if bytes.len() > cap {
        (&bytes[..cap], bytes.len() - cap)
    } else {
        (bytes, 0)
    };
    let mut s = String::with_capacity(slice.len() * 2 + 16);
    for b in slice {
        s.push_str(&format!("{b:02x}"));
    }
    if more > 0 {
        s.push_str(&format!(" …(+{more})"));
    }
    s
}
