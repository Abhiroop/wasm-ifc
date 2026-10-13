//! The password checker of `../password/password.c`, in Rust, for `wasm32-wasip1`.
//!
//! It reads a password from a file in `/secrets`, compares a hash of it with a dictionary of
//! weak passwords, shows the verdict on its standard output, and appends a record of the run
//! to a log in `/log` that is shared with the developer. The password must not reach the log.
//!
//! As in the C program, the secret input and output go to the host directly, and the code
//! that handles the password does not branch on it. The standard library opens the files,
//! which happens under a public pc, and writes the log.
//!
//! The features `leak_control` and `leak_memory` select the variants that leak.

use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::fd::AsRawFd;

#[repr(C)]
struct Buffer {
    start: *const u8,
    length: usize,
}

#[link(wasm_import_module = "wasi_snapshot_preview1")]
extern "C" {
    fn fd_read(fd: i32, buffers: *const Buffer, count: usize, read: *mut usize) -> i32;
    fn fd_write(fd: i32, buffers: *const Buffer, count: usize, written: *mut usize) -> i32;
}

/// djb2 hashes of the dictionary's weak passwords: "123456", "password", "qwerty", "letmein".
const WEAK: [u32; 4] = [0x7dd1705a, 0x17f6dc38, 0x1818ae71, 0x715ae1b3];
const CAPACITY: usize = 64;
/// "ok\n" at 0, "weak\n" at 5.
static VERDICTS: [u8; 10] = *b"ok\n\0\0weak\n";

/// The djb2 hash of the first `length` bytes, computed over the whole buffer.
fn djb2(text: &[u8; CAPACITY], length: u32) -> u32 {
    let mut h: u32 = 5381;
    for (i, byte) in text.iter().enumerate() {
        let keep = ((i as u32) < length) as u32;
        let keep = keep.wrapping_neg();
        let next = h.wrapping_mul(33).wrapping_add(*byte as u32);
        h = (next & keep) | (h & !keep);
    }
    h
}

fn main() {
    let input = match File::open("/secrets/password") {
        Ok(file) => file,
        Err(_) => std::process::exit(1),
    };
    let mut password = [0u8; CAPACITY];
    // Ask the host directly, so that "did the read fail" (the status, public) and "how many
    // bytes" (the count, secret like the file) stay two values.
    let buffer = Buffer { start: password.as_mut_ptr(), length: CAPACITY };
    let mut count: usize = 0;
    let status = unsafe { fd_read(input.as_raw_fd(), &buffer, 1, &mut count) };
    drop(input);
    if status != 0 {
        std::process::exit(1);
    }

    // Drop one trailing newline.
    let mut length = count as u32;
    let last = password[(length.wrapping_sub(1) as usize) % CAPACITY] as u32;
    length = length.wrapping_sub(((length > 0) as u32) & ((last == b'\n' as u32) as u32));

    let hash = djb2(&password, length);
    let mut matched: u32 = 0;
    for weak in WEAK {
        matched |= (hash == weak) as u32;
    }

    // The verdict, chosen by an offset and not by a branch.
    let verdict = Buffer {
        start: VERDICTS.as_ptr().wrapping_add(5 * matched as usize),
        length: 3 + 2 * matched as usize,
    };
    let mut written: usize = 0;
    let _ = unsafe { fd_write(1, &verdict, 1, &mut written) };

    let mut log = match OpenOptions::new().append(true).create(true).open("/log/runs.log") {
        Ok(file) => file,
        Err(_) => std::process::exit(1),
    };
    let mut record = format!("checked {}", WEAK.len());
    if cfg!(feature = "leak_control") {
        if matched != 0 {
            record.push_str(" weak");
        }
    } else if cfg!(feature = "leak_memory") {
        record.push_str(&format!(" {hash}"));
    }
    record.push('\n');
    let _ = log.write_all(record.as_bytes());
}
