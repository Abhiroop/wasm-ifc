(module
  ;; Finding 6: a br_table with repeated targets, which |gamma| >= m excludes
  (func (export "f") (param $x i32) (result i32)
    block block
      local.get $x br_table 0 1 0
    end end
    i32.const 3))
