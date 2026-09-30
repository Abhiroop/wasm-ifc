(module
  ;; Finding 4: unreachable in a block with a result
  (func (export "f") (param $x i32) (result i32)
    local.get $x
    if (result i32) block (result i32) unreachable end else i32.const 7 end))
