(module
  (func $popcnt (export "popcnt") (param $x i32) (result i32)
    (local.get $x) (i32.popcnt))
  (func $combine (export "combine") (param $lo i32) (param $hi i32) (result i32)
    (local.get $lo) (i32.const 255) (i32.and)
    (local.get $hi) (i32.const 8) (i32.shl)
    (i32.or)))
