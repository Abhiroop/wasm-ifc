(module
  ;; Euclid's algorithm — loop + br_if + i32.rem_u
  (func $gcd (export "gcd") (param $a i32) (param $b i32) (result i32)
    (block $done
      (loop $loop
        (local.get $b) (i32.eqz) (br_if $done)
        (local.get $b)
        (local.get $a) (local.get $b) (i32.rem_u)
        (local.set $b)
        (local.set $a)
        (br $loop)))
    (local.get $a)))
