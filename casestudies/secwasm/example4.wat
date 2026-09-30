(module (memory 1) (global (mut i32) (i32.const 0)) (global (mut i32) (i32.const 0))
  ;; Example 4: memory.grow by a secret amount
  (func (export "f")
    memory.size global.set 0
    i32.const 0 i32.load memory.grow drop
    memory.size global.set 1))
