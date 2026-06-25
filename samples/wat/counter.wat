(module
  (global $c (mut i32) (i32.const 100))
  (global $base i32 (i32.const 1000))   ;; immutable
  (func $bump (export "bump") (param $by i32) (result i32)
    (global.get $c)
    (local.get $by)
    (i32.add)
    (global.set $c)
    (global.get $c)
    (global.get $base)
    (i32.add)))
