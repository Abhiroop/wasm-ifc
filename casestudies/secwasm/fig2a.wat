(module
  ;; Figure 2a: branching out of nested blocks, no secrets
  (func (export "f") (result i32)
    i32.const 0
    block (param i32) (result i32)
      block (param i32)
        i32.eqz
        br_if 0
        i32.const 1
        br 1
      end
      i32.const 0
    end))
