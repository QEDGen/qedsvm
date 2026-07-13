use super::super::*;

/// Pins the p-token Transfer ERROR-PATH lift (pattern library Layer 3,
/// ENFORCES direction): from an insufficient-balance pre (the violated
/// check surfaces as the taken-`jlt` branch hypothesis), the real bytecode
/// runs dispatch → checks → error handler → TokenError logging → the
/// ProgramError encoder → the shared exit, with the account cells
/// untouched and r0 = the error code. The happy-path arm REQUIRES the
/// check; this lift proves the program ENFORCES it.
#[test]
fn p_token_transfer_insufficient_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_insufficient.pcs",
        "PTokenTransferInsufficient",
        None,
        "../../examples/lean/Generated/PTokenTransferInsufficientLifted.lean",
        None,
    );
}

/// Pins the p-token Transfer FROZEN-SOURCE error-path lift (pattern
/// library Layer 3, ENFORCES direction for the frozen check): the taken
/// `jeq state, 2` diverts to the same error handler with
/// TokenError::AccountFrozen (17) in r7 → r0 at the shared exit.
#[test]
fn p_token_transfer_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_frozen.pcs",
        "PTokenTransferFrozen",
        None,
        "../../examples/lean/Generated/PTokenTransferFrozenLifted.lean",
        None,
    );
}

/// Pins the p-token Transfer FROZEN-DEST error-path lift: the sibling of
/// the frozen-source lift, one `jeq` later (pc 4012, `jeq r5, 2`), same
/// error handler, TokenError::AccountFrozen (17) at the shared exit.
#[test]
fn p_token_transfer_dest_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_dest_frozen.pcs",
        "PTokenTransferDestFrozen",
        None,
        "../../examples/lean/Generated/PTokenTransferDestFrozenLifted.lean",
        None,
    );
}

/// Pins the p-token Transfer MINT-MISMATCH error-path lift: the mint
/// compare's first dword limb (`jne` at pc 4019, src mint limb0 vs dest
/// mint limb0) diverts through pc 4724 to the error handler,
/// TokenError::MintMismatch (3) at the shared exit. The first
/// pubkey-INEQUALITY lift; the trace exercises limb 0 (the fixture mints
/// differ in their first 8 bytes).
#[test]
fn p_token_transfer_mint_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_mint_mismatch.pcs",
        "PTokenTransferMintMismatch",
        None,
        "../../examples/lean/Generated/PTokenTransferMintMismatchLifted.lean",
        None,
    );
}

/// Pins the batch-2 p-token Transfer ERROR-PATH lifts (pattern library
/// Layer 3, ENFORCES direction) — all violating traces of the same
/// Transfer dispatch window, each diverting at a different check:
/// uninitialized src/dest (jeq state,0 at 4005/4008 → the 5080
/// UninitializedAccount path), invalid state byte src/dest (jgt state,2
/// at 4004/4007 → 4725 with the ProgramError::InvalidAccountData
/// encoding r6=3), short instruction data (jlt ix_len,9 at 3998 → the
/// 312 hub, TokenError::InvalidInstruction 12), and the mint-compare
/// limbs 1-3 (the jne at 4022/4025/4028 → 4724, MintMismatch 3 —
/// completing pubkey inequality alongside the limb-0 lift).
#[test]
fn p_token_transfer_src_uninit_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_src_uninit.pcs",
        "PTokenTransferSrcUninit",
        None,
        "../../examples/lean/Generated/PTokenTransferSrcUninitLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_dest_uninit_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_dest_uninit.pcs",
        "PTokenTransferDestUninit",
        None,
        "../../examples/lean/Generated/PTokenTransferDestUninitLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_src_bad_state_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_src_bad_state.pcs",
        "PTokenTransferSrcBadState",
        None,
        "../../examples/lean/Generated/PTokenTransferSrcBadStateLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_dest_bad_state_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_dest_bad_state.pcs",
        "PTokenTransferDestBadState",
        None,
        "../../examples/lean/Generated/PTokenTransferDestBadStateLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_short_ix_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_short_ix.pcs",
        "PTokenTransferShortIx",
        None,
        "../../examples/lean/Generated/PTokenTransferShortIxLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_mint_mismatch_limb1_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_mint_mismatch_limb1.pcs",
        "PTokenTransferMintMismatchLimb1",
        None,
        "../../examples/lean/Generated/PTokenTransferMintMismatchLimb1Lifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_mint_mismatch_limb2_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_mint_mismatch_limb2.pcs",
        "PTokenTransferMintMismatchLimb2",
        None,
        "../../examples/lean/Generated/PTokenTransferMintMismatchLimb2Lifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_mint_mismatch_limb3_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_mint_mismatch_limb3.pcs",
        "PTokenTransferMintMismatchLimb3",
        None,
        "../../examples/lean/Generated/PTokenTransferMintMismatchLimb3Lifted.lean",
        None,
    );
}

/// Pins the batch-3 p-token Transfer ERROR-PATH lifts: the authority
/// tri-case (owner-but-not-signer and delegate-but-not-signer →
/// ProgramError::MissingRequiredSignature 8<<32; neither owner nor
/// delegate → TokenError::OwnerMismatch 4) plus the delegated-amount
/// allowance check (delegate signs but allowance < amount →
/// TokenError::InsufficientFunds 1, a distinct check from the
/// source-balance one). Together these close the deferred "signer guard"
/// item honestly: each leg's violation is a separate EnforcedError, so
/// the delegate alternative is modeled instead of over-promised away.
#[test]
fn p_token_transfer_owner_not_signer_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_owner_not_signer.pcs",
        "PTokenTransferOwnerNotSigner",
        None,
        "../../examples/lean/Generated/PTokenTransferOwnerNotSignerLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_delegate_not_signer_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_delegate_not_signer.pcs",
        "PTokenTransferDelegateNotSigner",
        None,
        "../../examples/lean/Generated/PTokenTransferDelegateNotSignerLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_owner_mismatch.pcs",
        "PTokenTransferOwnerMismatch",
        None,
        "../../examples/lean/Generated/PTokenTransferOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_delegate_insufficient_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_delegate_insufficient.pcs",
        "PTokenTransferDelegateInsufficient",
        None,
        "../../examples/lean/Generated/PTokenTransferDelegateInsufficientLifted.lean",
        None,
    );
}

/// Pins the fan-out p-token ERROR-PATH lifts (pattern library Layer 3,
/// ENFORCES direction) across the MintTo / Burn / TransferChecked /
/// CloseAccount arms. Headline: MintTo supply-overflow IS enforced
/// (TokenError::Overflow 14) — the invariant the absent Transfer
/// dest-overflow check leans on, so both sides of the supply invariant
/// are in the catalog. Others: MintTo fixed-supply (5), MintTo
/// authority-mismatch (4), MintTo mint-mismatch (3), MintTo dest-frozen
/// (17), Burn insufficient (1), Burn frozen (17), TransferChecked
/// decimals-mismatch (18) + explicit-mint mismatch (3), CloseAccount
/// nonzero balance (11).
#[test]
fn p_token_mint_to_supply_overflow_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_mint_to_supply_overflow.pcs",
        "PTokenMintToSupplyOverflow",
        None,
        "../../examples/lean/Generated/PTokenMintToSupplyOverflowLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_fixed_supply_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_mint_to_fixed_supply.pcs",
        "PTokenMintToFixedSupply",
        None,
        "../../examples/lean/Generated/PTokenMintToFixedSupplyLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_authority_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_mint_to_authority_mismatch.pcs",
        "PTokenMintToAuthorityMismatch",
        None,
        "../../examples/lean/Generated/PTokenMintToAuthorityMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_mint_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_mint_to_mint_mismatch.pcs",
        "PTokenMintToMintMismatch",
        None,
        "../../examples/lean/Generated/PTokenMintToMintMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_mint_to_dest_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_mint_to_dest_frozen.pcs",
        "PTokenMintToDestFrozen",
        None,
        "../../examples/lean/Generated/PTokenMintToDestFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_burn_insufficient_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_burn_insufficient.pcs",
        "PTokenBurnInsufficient",
        None,
        "../../examples/lean/Generated/PTokenBurnInsufficientLifted.lean",
        None,
    );
}

#[test]
fn p_token_burn_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_burn_frozen.pcs",
        "PTokenBurnFrozen",
        None,
        "../../examples/lean/Generated/PTokenBurnFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_checked_decimals_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_checked_decimals_mismatch.pcs",
        "PTokenTransferCheckedDecimalsMismatch",
        None,
        "../../examples/lean/Generated/PTokenTransferCheckedDecimalsMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_transfer_checked_mint_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_checked_mint_mismatch.pcs",
        "PTokenTransferCheckedMintMismatch",
        None,
        "../../examples/lean/Generated/PTokenTransferCheckedMintMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_close_account_nonzero_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_close_account_nonzero.pcs",
        "PTokenCloseAccountNonzero",
        None,
        "../../examples/lean/Generated/PTokenCloseAccountNonzeroLifted.lean",
        None,
    );
}

/// Pins the batch-5 p-token ERROR-PATH lifts across the Approve /
/// Revoke / SetAuthority / FreezeAccount / ThawAccount arms: approve
/// frozen (17) + owner-mismatch (4), revoke frozen (17) +
/// owner-mismatch (4), set-authority owner-mismatch (4) + unsupported
/// authority type (15), freeze on a no-freeze-authority mint (16) +
/// freeze-authority mismatch (4) + already-frozen (13), thaw
/// not-frozen (13).
#[test]
fn p_token_approve_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_approve_frozen.pcs",
        "PTokenApproveFrozen",
        None,
        "../../examples/lean/Generated/PTokenApproveFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_approve_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_approve_owner_mismatch.pcs",
        "PTokenApproveOwnerMismatch",
        None,
        "../../examples/lean/Generated/PTokenApproveOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_revoke_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_revoke_frozen.pcs",
        "PTokenRevokeFrozen",
        None,
        "../../examples/lean/Generated/PTokenRevokeFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_revoke_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_revoke_owner_mismatch.pcs",
        "PTokenRevokeOwnerMismatch",
        None,
        "../../examples/lean/Generated/PTokenRevokeOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_set_authority_owner_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_set_authority_owner_mismatch.pcs",
        "PTokenSetAuthorityOwnerMismatch",
        None,
        "../../examples/lean/Generated/PTokenSetAuthorityOwnerMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_set_authority_bad_type_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_set_authority_bad_type.pcs",
        "PTokenSetAuthorityBadType",
        None,
        "../../examples/lean/Generated/PTokenSetAuthorityBadTypeLifted.lean",
        None,
    );
}

#[test]
fn p_token_freeze_cannot_freeze_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_freeze_cannot_freeze.pcs",
        "PTokenFreezeCannotFreeze",
        None,
        "../../examples/lean/Generated/PTokenFreezeCannotFreezeLifted.lean",
        None,
    );
}

#[test]
fn p_token_freeze_authority_mismatch_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_freeze_authority_mismatch.pcs",
        "PTokenFreezeAuthorityMismatch",
        None,
        "../../examples/lean/Generated/PTokenFreezeAuthorityMismatchLifted.lean",
        None,
    );
}

#[test]
fn p_token_freeze_already_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_freeze_already_frozen.pcs",
        "PTokenFreezeAlreadyFrozen",
        None,
        "../../examples/lean/Generated/PTokenFreezeAlreadyFrozenLifted.lean",
        None,
    );
}

#[test]
fn p_token_thaw_not_frozen_lift_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_thaw_not_frozen.pcs",
        "PTokenThawNotFrozen",
        None,
        "../../examples/lean/Generated/PTokenThawNotFrozenLifted.lean",
        None,
    );
}
/// Re-emit one p_token arm and diff lift + refinement against on-disk artifacts. Every arm is pinned: H8 vacuity shipped unnoticed without these pins.
fn pin_p_token_arm(
    pcs: &str,
    module: &str,
    arm: Option<&str>,
    lift_path: &str,
    refine_path: Option<&str>,
) {
    let so = std::path::Path::new("../tests/fixtures/p_token.so");
    let ctx = load_binary(so).expect("load p_token.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse p_token.so");
    let trace = load_trace(std::path::Path::new(pcs)).expect("load trace");
    // All p_token arms share the binary → shared-text dedup: the arm imports
    // `Generated.PTokenText` instead of re-embedding the ~100KB `.text`.
    let result = lift_one_with_layouts(
        so,
        &ctx,
        &analysis,
        LiftRequest {
            module_override: Some(module.to_string()),
            trace: Some(&trace),
            arm_name: arm,
            shared_text: Some("PToken"),
            ..LiftRequest::default()
        },
    )
    .expect("lift p_token arm");

    // QEDLIFT_BLESS=1 re-blesses artifacts after an intentional emitter change.
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(lift_path, &result.lean).expect("write lift");
        if let (Some(rp), Some((_, rlean))) = (refine_path, result.refinement.as_ref()) {
            std::fs::write(rp, rlean).expect("write refinement");
        }
    }
    let on_disk = std::fs::read_to_string(lift_path).expect("read lift");
    assert_eq!(
        result.lean, on_disk,
        "{lift_path} is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
    if let Some(rp) = refine_path {
        let (_, rlean) = result.refinement.expect("refinement emitted");
        let r_on_disk = std::fs::read_to_string(rp).expect("read refinement");
        assert_eq!(
            rlean, r_on_disk,
            "{rp} is out of sync with the qedlift refinement codegen \
             (mechanically emitted, do not hand-edit)"
        );
    }

    // The shared `.text` module is generated output too: every arm pin also
    // pins `Generated/PTokenText.lean` (identical for all arms of the binary).
    let (smod, slean) = result.shared_text.expect("shared text module emitted");
    assert_eq!(smod, "PTokenText");
    let spath = "../../examples/lean/Generated/PTokenText.lean";
    if std::env::var("QEDLIFT_BLESS").is_ok() {
        std::fs::write(spath, &slean).expect("write shared text module");
    }
    let s_on_disk = std::fs::read_to_string(spath).expect("read shared text module");
    assert_eq!(
        slean, s_on_disk,
        "{spath} is out of sync with the qedlift shared-text emitter \
         (mechanically emitted, do not hand-edit)"
    );
}

#[test]
fn p_token_transfer_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer.pcs",
        "PTokenTransfer",
        Some("Transfer"),
        "../../examples/lean/Generated/PTokenTransferTracedLifted.lean",
        Some("../../examples/lean/PToken/TransferRefinement.lean"),
    );
}

#[test]
fn p_token_transfer_checked_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_transfer_checked.pcs",
        "PTokenTransferChecked",
        Some("TransferChecked"),
        "../../examples/lean/Generated/PTokenTransferCheckedTracedLifted.lean",
        Some("../../examples/lean/PToken/TransferCheckedRefinement.lean"),
    );
}

/// Regenerated 2026-06-12 after H8: Phase A canonical aliasing (r10 spills) + Phase B byte demotion (`ldxdw_bytes_spec`).
#[test]
fn p_token_mint_to_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_mint_to.pcs",
        "PTokenMintTo",
        Some("MintTo"),
        "../../examples/lean/Generated/PTokenMintToTracedLifted.lean",
        Some("../../examples/lean/PToken/MintToRefinement.lean"),
    );
}

/// Regenerated 2026-06-12 after H8 Phase C-1: pre-split memset specs (`↦U64` cells; blob never overlaps).
#[test]
fn p_token_close_account_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_close_account.pcs",
        "PTokenCloseAccount",
        None,
        "../../examples/lean/Generated/PTokenCloseAccountTracedLifted.lean",
        None,
    );
}

/// Full H8 gauntlet: `sol_get_sysvar` (cells17), stw tail-zeroing (byte demotion), rent dword read. Trace re-captured under H7-faithful VM.
#[test]
fn p_token_initialize_mint2_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_initialize_mint2.pcs",
        "PTokenInitializeMint2",
        None,
        "../../examples/lean/Generated/PTokenInitializeMint2TracedLifted.lean",
        None,
    );
}

#[test]
fn p_token_burn_is_mechanically_emitted() {
    pin_p_token_arm(
        "../tests/fixtures/p_token_burn.pcs",
        "PTokenBurn",
        Some("Burn"),
        "../../examples/lean/Generated/PTokenBurnTracedLifted.lean",
        Some("../../examples/lean/PToken/BurnRefinement.lean"),
    );
}
