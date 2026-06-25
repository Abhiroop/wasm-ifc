(module
  (func $abs (export "abs") (param $x i32) (result i32)
    (local.get $x)
    (i32.const 0)
    (i32.lt_s)
    (if (result i32)
      (then (i32.const 0) (local.get $x) (i32.sub))
      (else (local.get $x)))))
