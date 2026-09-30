(module (global (mut i32) (i32.const 0))
  ;; Example 8: copy the truth value of a secret into a public global by skipping to the end
  (func (export "f") (param $y i32)
    block (result i32)
      block (result i32)
        i32.const 0
        local.get $y
        br_if 1
      end
      drop
      i32.const 1
    end
    global.set 0))
