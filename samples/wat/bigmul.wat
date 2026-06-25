(module
  (func $bigmul (export "bigmul") (param $a i64) (param $b i64) (result i64)
    (local.get $a) (local.get $b) (i64.mul)))
