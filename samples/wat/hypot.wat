(module
  ;; f64 arithmetic: sqrt(x*x + y*y)
  (func $hypot (export "hypot") (param $x f64) (param $y f64) (result f64)
    (local.get $x) (local.get $x) (f64.mul)
    (local.get $y) (local.get $y) (f64.mul)
    (f64.add) (f64.sqrt)))
