"""Build the small sectionless V3 conformance fixture (solana-sbpf 0.14.4)."""

from pathlib import Path
import struct


TEXT = bytearray.fromhex(
    "b700000001000000"  # mov64 r0, 1
    "1600010001000000"  # jeq32 r0, 1, +1
    "b700000063000000"  # skipped mov64 r0, 99
    "8510000001000000"  # relative call +1, src=1
    "9500000000000000"  # return target: exit
    "8500000000000000"  # static syscall, src=0
    "b700000000000000"  # mov64 r0, 0
    "9500000000000000"  # callee return
)
struct.pack_into("<I", TEXT, 44, 0x5C2A3178)  # sol_log_64_ Murmur3 hash

def write_elf(name: str, text: bytes) -> None:
    elf = bytearray(120 + len(text))
    elf[:16] = bytes.fromhex("7f454c46020101000000000000000000")
    struct.pack_into(
        "<HHIQQQIHHHHHH", elf, 16,
        3, 247, 1, 0x100000000, 64, 0, 3, 64, 56, 1, 0, 0, 0,
    )
    struct.pack_into(
        "<IIQQQQQQ", elf, 64,
        1, 1, 120, 0x100000000, 0x100000000, len(text), len(text), 8,
    )
    elf[120:] = text
    Path(__file__).with_name(name).write_bytes(elf)


write_elf("sbpfv3_static_path.so", TEXT)

ACCOUNT_TEXT = bytearray.fromhex(
    "b700000001000000"  # mov64 r0, 1
    "1600010001000000"  # jeq32 r0, 1, +1
    "b700000063000000"  # skipped mov64 r0, 99
    "8510000001000000"  # relative call +1
    "9500000000000000"  # return target: exit
    "7112600000000000"  # ldxb r2, [r1+96], account 0 data[0]
    "0702000001000000"  # add64 r2, 1
    "7321600000000000"  # stxb [r1+96], r2
    "8500000000000000"  # static sol_log_64_ syscall
    "b700000000000000"  # success return value
    "9500000000000000"  # callee return
)
struct.pack_into("<I", ACCOUNT_TEXT, 8 * 8 + 4, 0x5C2A3178)
write_elf("sbpfv3_account_path.so", ACCOUNT_TEXT)
