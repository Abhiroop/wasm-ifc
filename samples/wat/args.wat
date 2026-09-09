(module
  ;; Argument order through an internal call: a - b must see a first and b second.
  (func $sub (param i32 i32) (result i32) local.get 0 local.get 1 i32.sub)
  (func (export "callsub") (param i32 i32) (result i32) local.get 0 local.get 1 call $sub)
  ;; Parameters of different types, and a callee returning two results.
  (func $second (param i32 i64) (result i64) local.get 1)
  (func (export "mixed") (param i32 i64) (result i64) local.get 0 local.get 1 call $second)
  (func $two (result i32 i32) i32.const 1 i32.const 2)
  (func (export "multi") (result i32) call $two i32.sub))
