"""Batch format shared by harness/fdvm_main.c and QedCase.lean.

batch  := u64 MAGIC, u64 count, case*
case   := u64 len_words, header[24], text[text_cnt], rodata (8-pad), input (8-pad),
          calldests[calldests_cnt]                       (all little-endian u64)
header := version, entry_pc, cu_budget, heap_max, text_cnt, rodata_sz, input_sz,
          calldests_cnt, r2_initial, text_off, features, reg_mask, reg[12]
features bit 0 direct_mapping, 1 syscall_parameter_address_restrictions,
         bit 2 virtual_address_space_adjustments (fd_vm_init flags).
reg_mask bit i: override r_i with reg[i] after init (as fd's test_vm_instr does).
"""
import struct

MAGIC = 0x0032544142564446  # "FDVBAT2\0"
FEAT_DIRECT_MAPPING, FEAT_SYSCALL_PARAM, FEAT_VAS_ADJ = 1, 2, 4

def _pad8(b): return b + b"\0" * (-len(b) % 8)

def insn(op, dst=0, src=0, off=0, imm=0):
    return struct.pack("<BBhI", op, (src << 4) | dst, off, imm & 0xffffffff)

def pack_case(text, *, version=0, entry_pc=0, budget=200_000, heap_max=32 * 1024,
              rodata=None, input_=b"", calldests=(), r2=0, text_off=0,
              features=0, regs=None):
    assert len(text) % 8 == 0, "text must be whole 8-byte slots"
    rodata = text if rodata is None else rodata
    if version >= 3:
        calldests = ()
    regs = regs or {}
    mask = sum(1 << i for i in regs)
    reg = [regs.get(i, 0) & 0xffffffffffffffff for i in range(12)]
    hdr = struct.pack("<24Q", version, entry_pc, budget, heap_max, len(text) // 8,
                      len(rodata), len(input_), len(calldests), r2, text_off, features,
                      mask, *reg)
    body = hdr + text + _pad8(rodata) + _pad8(input_) + b"".join(
        struct.pack("<Q", c) for c in calldests)
    return struct.pack("<Q", len(body) // 8) + body

def pack_batch(cases):
    return struct.pack("<QQ", MAGIC, len(cases)) + b"".join(cases)
