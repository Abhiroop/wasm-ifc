(module
  ;; number of Collatz steps to reach 1 — uses i32.and for the parity test
  (func $collatz (export "collatz") (param $n i32) (result i32)
    (local $steps i32)
    (block $done (loop $l
      (br_if $done (i32.le_u (local.get $n) (i32.const 1)))
      (if (i32.eqz (i32.and (local.get $n) (i32.const 1)))
        (then (local.set $n (i32.div_u (local.get $n) (i32.const 2))))
        (else (local.set $n (i32.add (i32.mul (i32.const 3) (local.get $n)) (i32.const 1)))))
      (local.set $steps (i32.add (local.get $steps) (i32.const 1)))
      (br $l)))
    (local.get $steps)))
