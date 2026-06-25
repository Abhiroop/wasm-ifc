(module
  (func $fac (export "fac") (param $n i32) (result i32)
    (local.get $n)
    (i32.const 1)
    (i32.le_s)
    (if (result i32)
      (then (i32.const 1))
      (else
        (local.get $n)
        (local.get $n)
        (i32.const 1)
        (i32.sub)
        (call $fac)
        (i32.mul)))))
