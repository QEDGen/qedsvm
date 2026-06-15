//! qedsvm vs mollusk: byte+CU conformance demo.
//! Fixtures: incrementer.so (u64+1 write-back) + p_token.so Transfer 250 (76 CU).
//! Run: cargo run --release --features diff-mollusk --manifest-path qedsvm-rs/Cargo.toml --example conformance_demo
//! Exit 0 if byte+CU identical, 1 otherwise.

#![cfg(feature = "diff-mollusk")]

use std::time::Instant;

use qedsvm::Svm;
use mollusk_svm::Mollusk;
use solana_account::{Account, AccountSharedData, ReadableAccount};
use solana_instruction::{AccountMeta, Instruction};
use solana_pubkey::Pubkey;

const INCREMENTER_SO: &[u8] = include_bytes!("../tests/fixtures/incrementer.so");
const P_TOKEN_SO:     &[u8] = include_bytes!("../tests/fixtures/p_token.so");

fn pid(seed: u64) -> Pubkey {
    let mut b = [0u8; 32];
    b[..8].copy_from_slice(&seed.to_le_bytes());
    Pubkey::from(b)
}

fn build_token_account(mint: &Pubkey, owner: &Pubkey, amount: u64) -> Vec<u8> {
    let mut d = vec![0u8; 165];
    d[0..32].copy_from_slice(mint.as_ref());
    d[32..64].copy_from_slice(owner.as_ref());
    d[64..72].copy_from_slice(&amount.to_le_bytes());
    d[108] = 1; // AccountState::Initialized
    d
}

/// Result of running one fixture through both engines.
struct Comparison {
    name: &'static str,
    fs_status: String, m_status: String,
    fs_cu: u64,        m_cu: u64,
    fs_return: Vec<u8>, m_return: Vec<u8>,
    fs_accounts: Vec<Vec<u8>>, m_accounts: Vec<Vec<u8>>,
    fs_wall_ms: f64,   m_wall_ms: f64,
}

impl Comparison {
    fn identical(&self) -> bool {
        self.fs_status == self.m_status
            && self.fs_cu == self.m_cu
            && self.fs_return == self.m_return
            && self.fs_accounts == self.m_accounts
    }
}

fn fmt_status<T: std::fmt::Debug>(r: T) -> String {
    let s = format!("{:?}", r);
    if s.starts_with("Success") { "Success".into() } else { s }
}

fn run_fixture(
    name: &'static str,
    so: &[u8],
    program_id: Pubkey,
    ix: Instruction,
    fs_accounts: Vec<(Pubkey, AccountSharedData)>,
    m_accounts:  Vec<(Pubkey, mollusk_account::Account)>,
) -> Comparison {
    // ---- qedsvm ----
    let mut fs = Svm::default().with_cu_budget(1_400_000);
    fs.add_program(&program_id, so);
    let t0 = Instant::now();
    let fs_r = fs.process_instruction(&ix, &fs_accounts).expect("qedsvm runs");
    let fs_wall_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // ---- mollusk ----
    let mut m = Mollusk::default();
    m.add_program_with_loader_and_elf(
        &program_id, &solana_sdk_ids::bpf_loader_upgradeable::id(), so,
    );
    let t0 = Instant::now();
    let m_r = m.process_instruction(&ix, &m_accounts);
    let m_wall_ms = t0.elapsed().as_secs_f64() * 1000.0;

    Comparison {
        name,
        fs_status: fmt_status(&fs_r.program_result),
        m_status:  fmt_status(&m_r.program_result),
        fs_cu: fs_r.compute_units_consumed,
        m_cu:  m_r.compute_units_consumed,
        fs_return: fs_r.return_data,
        m_return:  m_r.return_data,
        fs_accounts: fs_r.resulting_accounts.iter()
            .map(|(_, a)| a.data().to_vec()).collect(),
        m_accounts: m_r.resulting_accounts.iter()
            .map(|(_, a)| a.data.clone()).collect(),
        fs_wall_ms, m_wall_ms,
    }
}

fn print_comparison(c: &Comparison) {
    let acct_digest = |v: &[Vec<u8>]| -> String {
        let mut s = String::new();
        for (i, d) in v.iter().enumerate() {
            if !s.is_empty() { s.push_str("  "); }
            s.push_str(&format!("[{i}] {}B {:02x}{:02x}…{:02x}{:02x}",
                d.len(),
                d.first().copied().unwrap_or(0),
                d.get(1).copied().unwrap_or(0),
                d.iter().rev().nth(1).copied().unwrap_or(0),
                d.last().copied().unwrap_or(0),
            ));
        }
        if s.is_empty() { "(none)".into() } else { s }
    };

    println!("\n── {} ──", c.name);
    println!("  qedsvm:   {:<10}  CU={:<6}  ret={:>3}B  wall={:>6.1}ms  accts: {}",
        c.fs_status, c.fs_cu, c.fs_return.len(), c.fs_wall_ms,
        acct_digest(&c.fs_accounts));
    println!("  mollusk:  {:<10}  CU={:<6}  ret={:>3}B  wall={:>6.1}ms  accts: {}",
        c.m_status, c.m_cu, c.m_return.len(), c.m_wall_ms,
        acct_digest(&c.m_accounts));

    if c.identical() {
        println!("  ✅ byte+CU identical");
    } else {
        println!("  ❌ DIVERGED");
        if c.fs_status != c.m_status { println!("     status: {} vs {}", c.fs_status, c.m_status); }
        if c.fs_cu     != c.m_cu     { println!("     CU:     {} vs {}", c.fs_cu, c.m_cu); }
        if c.fs_return != c.m_return { println!("     return_data differs"); }
        if c.fs_accounts != c.m_accounts { println!("     account data differs"); }
    }
}

fn incrementer() -> Comparison {
    let program_id = pid(5);
    let acct_key = pid(6);
    let lamports = 1_000_000u64;
    let data = vec![0u8; 16];

    let fs_pre = AccountSharedData::from(Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let m_pre = mollusk_account::Account {
        lamports, data: data.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };

    let ix = Instruction {
        program_id, data: vec![],
        accounts: vec![AccountMeta::new(acct_key, false)],
    };

    run_fixture(
        "incrementer (u64+1 write-back)",
        INCREMENTER_SO, program_id, ix,
        vec![(acct_key, fs_pre)],
        vec![(acct_key, m_pre)],
    )
}

fn p_token_transfer() -> Comparison {
    let program_id = pid(40);
    let mint       = pid(41);
    let authority  = pid(42);
    let source_key = pid(43);
    let dest_key   = pid(44);

    const AMOUNT: u64 = 250;
    const SOURCE_INITIAL: u64 = 1_000;
    const DEST_INITIAL:   u64 = 0;
    const LAMPORTS: u64 = 2_039_280; // standard rent-exempt for 165B

    let source = build_token_account(&mint, &authority, SOURCE_INITIAL);
    let dest   = build_token_account(&mint, &authority, DEST_INITIAL);

    let fs_src = AccountSharedData::from(Account {
        lamports: LAMPORTS, data: source.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let fs_dst = AccountSharedData::from(Account {
        lamports: LAMPORTS, data: dest.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    });
    let fs_auth = AccountSharedData::from(Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    });

    let m_src = mollusk_account::Account {
        lamports: LAMPORTS, data: source.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };
    let m_dst = mollusk_account::Account {
        lamports: LAMPORTS, data: dest.clone(), owner: program_id,
        executable: false, rent_epoch: 0,
    };
    let m_auth = mollusk_account::Account {
        lamports: 1_000_000, data: vec![], owner: Pubkey::default(),
        executable: false, rent_epoch: 0,
    };

    let mut ix_data = Vec::with_capacity(9);
    ix_data.push(3); // Transfer discriminant
    ix_data.extend_from_slice(&AMOUNT.to_le_bytes());

    let ix = Instruction {
        program_id,
        data: ix_data,
        accounts: vec![
            AccountMeta::new(source_key, false),
            AccountMeta::new(dest_key, false),
            AccountMeta::new_readonly(authority, true),
        ],
    };

    run_fixture(
        "p-token Transfer (pinocchio, 250 of token)",
        P_TOKEN_SO, program_id, ix,
        vec![(source_key, fs_src), (dest_key, fs_dst), (authority, fs_auth)],
        vec![(source_key, m_src),  (dest_key, m_dst),  (authority, m_auth)],
    )
}

fn main() {
    std::env::set_var("RUST_LOG", "off"); // silence mollusk's register-tracing DEBUG logs

    println!("qedsvm vs mollusk: byte+CU conformance demo");
    println!("===========================================");
    println!("Two compiled .so fixtures, two engines, same observable output.");

    let results = [incrementer(), p_token_transfer()];
    for c in &results { print_comparison(c); }

    let ok = results.iter().filter(|c| c.identical()).count();
    let total = results.len();
    println!("\n============================================");
    if ok == total {
        println!("✅ {ok}/{total} fixtures byte+CU identical to mollusk.");
        std::process::exit(0);
    } else {
        println!("❌ {ok}/{total} fixtures identical — {} diverged.", total - ok);
        std::process::exit(1);
    }
}
