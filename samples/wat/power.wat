(module
  ;; iterative exponentiation: base^exp
  (func $power (export "power") (param $base i32) (param $exp i32) (result i32)
    (local $result i32)
    (local.set $result (i32.const 1))
    (block $done (loop $l
      (br_if $done (i32.eqz (local.get $exp)))
      (local.set $result (i32.mul (local.get $result) (local.get $base)))
      (local.set $exp (i32.sub (local.get $exp) (i32.const 1)))
      (br $l)))
    (local.get $result)))
