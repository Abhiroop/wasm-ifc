(module
  ;; conversion: dynamic interpreter handles it, typed layer rejects (out of scope)
  (func $widen (export "widen") (param $x i32) (result i64)
    (local.get $x) (i64.extend_i32_s)))
