(module
  (func $divs (export "divs") (param $a i32) (param $b i32) (result i32)
    (local.get $a) (local.get $b) (i32.div_s))
  (func $divu (export "divu") (param $a i32) (param $b i32) (result i32)
    (local.get $a) (local.get $b) (i32.div_u)))
