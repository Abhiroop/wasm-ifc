(module (memory 1) (global (mut i32) (i32.const 0)) (global (mut i32) (i32.const 0))
  ;; Example 5: memory.grow in a branch on a secret
  (func (export "f")
    memory.size global.set 0
    i32.const 0 i32.load
    if (result i32) i32.const 1 memory.grow else i32.const 0 end
    drop
    memory.size global.set 1))
