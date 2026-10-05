(module
  ;; Section 4.2: a br_table that leaves a value below the one it carries, which the printed
  ;; T-Br-Table cannot type because it keeps the values below the carried ones
  (func (export "f") (param $x i32) (result i32)
    block (result i32)
      i32.const 9
      i32.const 7
      local.get $x
      br_table 0
    end))
