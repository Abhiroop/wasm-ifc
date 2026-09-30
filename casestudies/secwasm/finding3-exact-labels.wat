(module
  ;; Finding 3: a public argument to a secret parameter; a public constant carried by a secret branch
  (func $g (param i32) (result i32) local.get 0)
  (func (export "f") (param $y i32) (result i32)
    i32.const 5 call $g drop
    block (result i32)
      i32.const 0 local.get $y br_if 0 drop i32.const 1
    end))
