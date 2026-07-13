use super::super::*;

/// Guards the heap-corollary codegen: `heapBumpPtr`/`heapBlockU64` fold + conditional `HeapSL` import.
#[test]
fn heap_alloc_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/heap_alloc.so");
    let ctx = load_binary(so).expect("load heap_alloc.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse heap_alloc.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("HeapAlloc".to_string()),
        None,
        None,
        None,
        None,
    )
    .expect("lift heap_alloc.so");

    let on_disk = std::fs::read_to_string("../../examples/lean/Generated/HeapAllocLifted.lean")
        .expect("read HeapAllocLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "HeapAllocLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}
/// Pins ldxh/stxh and ST_H_IMM (`sth_spec`) on real cargo-build-sbf bytecode.
#[test]
fn halfword_store_lift_is_mechanically_emitted() {
    let so = std::path::Path::new("../tests/fixtures/halfword_store.so");
    let ctx = load_binary(so).expect("load halfword_store.so");
    let analysis = Analysis::from_executable(&ctx.executable).expect("analyse halfword_store.so");
    let result = lift_one(
        so,
        &ctx,
        &analysis,
        None,
        Some("HalfwordStore".to_string()),
        None,
        None,
        None,
        None,
    )
    .expect("lift halfword_store.so");

    let on_disk = std::fs::read_to_string("../../examples/lean/Generated/HalfwordStoreLifted.lean")
        .expect("read HalfwordStoreLifted.lean");
    assert_eq!(
        result.lean, on_disk,
        "HalfwordStoreLifted.lean is out of sync with the qedlift emitter \
         (mechanically emitted, do not hand-edit)"
    );
}
