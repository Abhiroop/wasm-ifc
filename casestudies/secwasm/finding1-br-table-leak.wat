(module (global (mut i32) (i32.const 0))
  ;; Finding 1: the printed T-Br-Table lifts by the number of immediates, not the target's depth
  (func (export "f") (param $secret i32)
    block $b3 block $b2 block $b1 block $b0
      local.get $secret br_table 0 3
    end end end
    i32.const 1 global.set 0
    end))
