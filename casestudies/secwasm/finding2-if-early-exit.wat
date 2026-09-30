(module (global (mut i32) (i32.const 0))
  ;; Finding 2: an early exit in one arm of an if, which the printed T-If cannot type
  (func (export "f") (param $c i32) (param $y i32)
    block
      local.get $c
      if
        local.get $y br_if 1
      else
        nop
      end
      nop
    end))
