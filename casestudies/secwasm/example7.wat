(module (memory 1) (global (mut i32) (i32.const 0))
  ;; Example 7: if (x) return 0 else return 1, x secret; the result is secret
  (func (export "f")
    i32.const 0 i32.load
    block (param i32) (result i32)
      block (param i32)
        i32.eqz br_if 0
        i32.const 1 br 1
      end
      i32.const 0
    end
    global.set 0))
