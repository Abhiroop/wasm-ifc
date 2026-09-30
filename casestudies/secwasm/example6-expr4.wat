(module (memory 1) (global (mut i32) (i32.const 0))
  ;; Example 6: a public write at expr 4, after $B2 but inside $B1, which br_if 1 may skip
  (func (export "f")
    block $B0 block $B1 block $B2
      i32.const 0 i32.load br_if 1
      i32.const 4 i32.load br_if 0
    end
    i32.const 1 global.set 0
    end end))
