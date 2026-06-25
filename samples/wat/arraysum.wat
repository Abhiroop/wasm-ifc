(module
  (memory 1)
  ;; write 0..n-1 into memory, then sum them back: result = n*(n-1)/2
  (func $arraysum (export "arraysum") (param $n i32) (result i32)
    (local $i i32) (local $sum i32)
    (block $w (loop $wl
      (local.get $i) (local.get $n) (i32.ge_s) (br_if $w)
      (local.get $i) (i32.const 4) (i32.mul) (local.get $i) (i32.store)
      (local.get $i) (i32.const 1) (i32.add) (local.set $i)
      (br $wl)))
    (i32.const 0) (local.set $i)
    (block $s (loop $sl
      (local.get $i) (local.get $n) (i32.ge_s) (br_if $s)
      (local.get $sum) (local.get $i) (i32.const 4) (i32.mul) (i32.load) (i32.add) (local.set $sum)
      (local.get $i) (i32.const 1) (i32.add) (local.set $i)
      (br $sl)))
    (local.get $sum)))
