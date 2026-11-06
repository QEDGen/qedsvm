//! One parametric probe for the runtime's account-change rules (#144). It edits
//! the serialized input directly, so the only thing under test is what the
//! runtime does with the edited buffer after the program exits 0.
//!
//! Instruction data is a list of 16-byte ops, `[op, account, 0 x6, arg: u64]`,
//! where `account` is the instruction-account position and a duplicate position
//! resolves to its first occurrence:
//!
//!   0  lamports = arg
//!   1  lamports += arg (wrapping, so a negative delta is two's complement)
//!   2  data_len field = arg
//!   3  data[arg as u32] = (arg >> 32) as u8
//!   4  owner = [arg as u8; 32]
//!   5  executable byte = arg
//!   6  is_signer byte = arg
//!   7  is_writable byte = arg
//!   8  first key byte = arg
//!   9  rent_epoch field = arg
//!   10 owner = this program's id
//!   11 data[..arg] = 0
//!   12 invoke the program at `account`, which must be the last position, passing
//!      every other account and the next `arg` bytes of ops as its instruction data;
//!      those ops run in the callee, and a nonzero return ends this program with it

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::sol_invoke_signed_c;

const MAX_ACCOUNTS: usize = 8;
const NON_DUP: u8 = 0xff;
const HEADER: usize = 88;
const REALLOC_ROOM: usize = 10240;

#[repr(C)]
#[derive(Clone, Copy)]
struct Meta {
    key: u64,
    is_writable: u8,
    is_signer: u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Info {
    key: u64,
    lamports: u64,
    data_len: u64,
    data: u64,
    owner: u64,
    rent_epoch: u64,
    is_signer: u8,
    is_writable: u8,
    executable: u8,
}

#[repr(C)]
struct Ix {
    program_id: u64,
    metas: u64,
    metas_len: u64,
    data: u64,
    data_len: u64,
}

unsafe fn rd(input: *const u8, off: usize) -> u64 {
    core::ptr::read_unaligned(input.add(off) as *const u64)
}

unsafe fn wr(input: *mut u8, off: usize, v: u64) {
    core::ptr::write_unaligned(input.add(off) as *mut u64, v)
}

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let n = rd(input, 0) as usize;
        if n > MAX_ACCOUNTS {
            return 1;
        }
        // Offsets are fixed before any op runs: an op may rewrite data_len.
        let mut base = [0usize; MAX_ACCOUNTS];
        let mut rent = [0usize; MAX_ACCOUNTS];
        let mut off = 8usize;
        let mut i = 0;
        while i < n {
            let marker = *input.add(off);
            if marker == NON_DUP {
                base[i] = off;
                let len = rd(input, off + 80) as usize;
                off += HEADER + len + REALLOC_ROOM;
                off = (off + 7) & !7;
                rent[i] = off;
                off += 8;
            } else {
                base[i] = base[marker as usize];
                rent[i] = rent[marker as usize];
                off += 8;
            }
            i += 1;
        }
        let ix_len = rd(input, off) as usize;
        let ops = off + 8;
        let pid = ops + ix_len;
        let mut at = 0usize;
        while at + 16 <= ix_len {
            let op = *input.add(ops + at);
            let a = *input.add(ops + at + 1) as usize;
            let arg = rd(input, ops + at + 8);
            let b = base[a];
            match op {
                0 => wr(input, b + 72, arg),
                1 => wr(input, b + 72, rd(input, b + 72).wrapping_add(arg)),
                2 => wr(input, b + 80, arg),
                3 => core::ptr::write_volatile(
                    input.add(b + HEADER + (arg as u32) as usize),
                    (arg >> 32) as u8,
                ),
                4 => {
                    let mut j = 0;
                    while j < 32 {
                        core::ptr::write_volatile(input.add(b + 40 + j), arg as u8);
                        j += 1;
                    }
                }
                5 => *input.add(b + 3) = arg as u8,
                6 => *input.add(b + 1) = arg as u8,
                7 => *input.add(b + 2) = arg as u8,
                8 => *input.add(b + 8) = arg as u8,
                9 => wr(input, rent[a], arg),
                10 => {
                    let mut j = 0;
                    while j < 32 {
                        core::ptr::write_volatile(input.add(b + 40 + j), *input.add(pid + j));
                        j += 1;
                    }
                }
                11 => {
                    let mut j = 0;
                    while j < arg as usize {
                        core::ptr::write_volatile(input.add(b + HEADER + j), 0);
                        j += 1;
                    }
                }
                12 => {
                    let meta0 = Meta { key: 0, is_writable: 0, is_signer: 0 };
                    let mut metas = [meta0; MAX_ACCOUNTS];
                    let info0 = Info {
                        key: 0,
                        lamports: 0,
                        data_len: 0,
                        data: 0,
                        owner: 0,
                        rent_epoch: 0,
                        is_signer: 0,
                        is_writable: 0,
                        executable: 0,
                    };
                    let mut infos = [info0; MAX_ACCOUNTS];
                    let count = n - 1;
                    let start = input as u64;
                    let mut j = 0;
                    while j < count {
                        let h = base[j];
                        metas[j] = Meta {
                            key: start + h as u64 + 8,
                            is_writable: *input.add(h + 2),
                            is_signer: *input.add(h + 1),
                        };
                        infos[j] = Info {
                            key: start + h as u64 + 8,
                            lamports: start + h as u64 + 72,
                            data_len: rd(input, h + 80),
                            data: start + (h + HEADER) as u64,
                            owner: start + h as u64 + 40,
                            rent_epoch: rd(input, rent[j]),
                            is_signer: *input.add(h + 1),
                            is_writable: *input.add(h + 2),
                            executable: *input.add(h + 3),
                        };
                        j += 1;
                    }
                    let ix = Ix {
                        program_id: start + b as u64 + 8,
                        metas: metas.as_ptr() as u64,
                        metas_len: count as u64,
                        data: start + (ops + at + 16) as u64,
                        data_len: arg,
                    };
                    let r = sol_invoke_signed_c(
                        &ix as *const Ix as *const u8,
                        infos.as_ptr() as *const u8,
                        count as u64,
                        core::ptr::null(),
                        0,
                    );
                    if r != 0 {
                        return r;
                    }
                    at += arg as usize;
                }
                _ => return 2,
            }
            at += 16;
        }
    }
    0
}
