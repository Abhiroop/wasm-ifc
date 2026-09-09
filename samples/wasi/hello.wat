;; Hello, world through WASI: the string lives in a data segment, an iovec pointing at it is
;; written at address 0, fd_write sends it to stdout (fd 1), and proc_exit ends the program.
(module
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (memory (export "memory") 1)
  (data (i32.const 8) "Hello, world!\n")
  (func (export "_start")
    (i32.store (i32.const 0) (i32.const 8))   ;; iov.base
    (i32.store (i32.const 4) (i32.const 14))  ;; iov.len
    (drop (call $fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 20)))
    (call $proc_exit (i32.const 0))))
