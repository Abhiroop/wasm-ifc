(module
  ;; square via a helper, exercising Call and argument passing
  (func $mul (param $a i32) (param $b i32) (result i32)
    (local.get $a)
    (local.get $b)
    (i32.mul))
  (func $square (export "square") (param $x i32) (result i32)
    (local.get $x)
    (local.get $x)
    (call $mul)))
