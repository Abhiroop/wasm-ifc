(module
  (func $r (export "r") (param $n i32) (result i32)
    (local.get $n)
    (i32.const 1)
    (i32.add)
    (return)
    (i32.const 999)))  ;; dead
