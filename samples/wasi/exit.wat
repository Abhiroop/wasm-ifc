;; The exit code of proc_exit becomes the process exit code.
(module
  (import "wasi_snapshot_preview1" "proc_exit" (func $proc_exit (param i32)))
  (memory 1)
  (func (export "_start") (call $proc_exit (i32.const 7))))
