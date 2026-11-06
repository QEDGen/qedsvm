//! Returns a window of the program's own serialized input, so a differential
//! test can compare the input ABI byte by byte (#145). It only reads.
//!
//! Instruction data of at least 16 bytes is `[start: u64, len: u64, ..]`, a window
//! of at most 1024 bytes from the start of the input. Longer data whose last byte
//! is 0xC9 first invokes the program at the last account position, passing every
//! other account and all but that last byte, and leaves the callee's return data
//! in place.
//!
//! Shorter instruction data selects the trailer: the instruction-data length, the
//! instruction data and the program id.

#![no_std]
#![allow(unexpected_cfgs)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

use solana_define_syscall::definitions::{sol_invoke_signed_c, sol_set_return_data};

const MAX_ACCOUNTS: usize = 8;
const MAX_WINDOW: usize = 1024;
const NON_DUP: u8 = 0xff;
const HEADER: usize = 88;
const REALLOC_ROOM: usize = 10240;
const CPI: u8 = 0xC9;

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

#[no_mangle]
pub extern "C" fn entrypoint(input: *mut u8) -> u64 {
    unsafe {
        let n = rd(input, 0) as usize;
        let mut base = [0usize; MAX_ACCOUNTS];
        let mut off = 8usize;
        let mut i = 0;
        while i < n {
            let marker = *input.add(off);
            if marker == NON_DUP {
                if i < MAX_ACCOUNTS {
                    base[i] = off;
                }
                let len = rd(input, off + 80) as usize;
                off += HEADER + len + REALLOC_ROOM;
                off = (off + 7) & !7;
                off += 8;
            } else {
                if i < MAX_ACCOUNTS {
                    base[i] = base[marker as usize];
                }
                off += 8;
            }
            i += 1;
        }
        let ix_len = rd(input, off) as usize;
        let ix = off + 8;
        let (start, len) = if ix_len >= 16 {
            (rd(input, ix) as usize, rd(input, ix + 8) as usize)
        } else {
            (off, 8 + ix_len + 32)
        };
        if ix_len > 16 && *input.add(ix + ix_len - 1) == CPI {
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
            let at = input as u64;
            let mut j = 0;
            while j < count {
                let h = base[j];
                metas[j] = Meta {
                    key: at + h as u64 + 8,
                    is_writable: *input.add(h + 2),
                    is_signer: *input.add(h + 1),
                };
                infos[j] = Info {
                    key: at + h as u64 + 8,
                    lamports: at + h as u64 + 72,
                    data_len: rd(input, h + 80),
                    data: at + (h + HEADER) as u64,
                    owner: at + h as u64 + 40,
                    // Not what the caller's buffer holds: the runtime must not forward it.
                    rent_epoch: 0x0102_0304_0506_0708,
                    is_signer: *input.add(h + 1),
                    is_writable: *input.add(h + 2),
                    executable: *input.add(h + 3),
                };
                j += 1;
            }
            let call = Ix {
                program_id: at + base[n - 1] as u64 + 8,
                metas: metas.as_ptr() as u64,
                metas_len: count as u64,
                data: at + ix as u64,
                data_len: (ix_len - 1) as u64,
            };
            return sol_invoke_signed_c(
                &call as *const Ix as *const u8,
                infos.as_ptr() as *const u8,
                count as u64,
                core::ptr::null(),
                0,
            );
        }
        let len = if len > MAX_WINDOW { MAX_WINDOW } else { len };
        let mut out = [0u8; MAX_WINDOW];
        let mut j = 0;
        while j < len {
            out[j] = core::ptr::read_volatile(input.add(start + j));
            j += 1;
        }
        sol_set_return_data(out.as_ptr(), len as u64);
    }
    0
}
