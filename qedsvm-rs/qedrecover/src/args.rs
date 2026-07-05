//! CLI argument parsing for qedrecover.

use std::path::PathBuf;

pub(crate) struct Args {
    pub(crate) so: PathBuf,
    pub(crate) overlay: PathBuf,
    pub(crate) output: Option<PathBuf>,
    /// `.pcs` trace (one decimal logical PC per line, `#` comments ignored). Tags
    /// happy-path blocks in emitted metadata; rejected if overlay claims > 1 instruction.
    pub(crate) trace: Option<PathBuf>,
    /// Emit the qedmeta `.toml` sidecar (issue #37) consumed by qedlift. Independent of `--output`.
    pub(crate) qedmeta_out: Option<PathBuf>,
}

pub(crate) fn parse_args() -> Result<Args, String> {
    let mut so: Option<PathBuf> = None;
    let mut overlay: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut trace: Option<PathBuf> = None;
    let mut qedmeta_out: Option<PathBuf> = None;
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--so" => so = Some(it.next().ok_or("--so needs a path")?.into()),
            "--overlay" => overlay = Some(it.next().ok_or("--overlay needs a path")?.into()),
            "--output" => output = Some(it.next().ok_or("--output needs a path")?.into()),
            "--trace" => trace = Some(it.next().ok_or("--trace needs a path")?.into()),
            "--qedmeta-out" => {
                qedmeta_out = Some(it.next().ok_or("--qedmeta-out needs a path")?.into())
            }
            other => return Err(format!("unknown arg: {}", other)),
        }
    }
    Ok(Args {
        so: so.ok_or("missing --so")?,
        overlay: overlay.ok_or("missing --overlay")?,
        output,
        trace,
        qedmeta_out,
    })
}
