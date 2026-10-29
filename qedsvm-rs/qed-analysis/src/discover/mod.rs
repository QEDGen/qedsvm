//! Binary-derived success-proof bindings (solana-skills#450). Every result here is an
//! untrusted proposal: Lean re-checks it against the decoded program before any theorem
//! depends on it.

pub mod authority;
pub mod bindings;
pub mod dispatch;
pub mod fields;
pub mod noreturn;
