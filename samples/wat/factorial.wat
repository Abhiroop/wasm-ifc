(module
  ;; iterative factorial: acc starts at 1, multiply down from n
  (func $fac (export "fac") (param $n i32) (result i32)
    (local $acc i32)
    (i32.const 1)
    (local.set $acc)
    (block $done
      (loop $continue
        ;; if n <= 1, leave the loop
        (local.get $n)
        (i32.const 1)
        (i32.le_s)
        (br_if $done)
        ;; acc = acc * n
        (local.get $acc)
        (local.get $n)
        (i32.mul)
        (local.set $acc)
        ;; n = n - 1
        (local.get $n)
        (i32.const 1)
        (i32.sub)
        (local.set $n)
        (br $continue)))
    (local.get $acc)))
