(module
  ;; mutually recursive — call across two functions, forward reference
  (func $isEven (export "isEven") (param $n i32) (result i32)
    (local.get $n) (i32.eqz)
    (if (result i32) (then (i32.const 1))
      (else (local.get $n) (i32.const 1) (i32.sub) (call $isOdd))))
  (func $isOdd (export "isOdd") (param $n i32) (result i32)
    (local.get $n) (i32.eqz)
    (if (result i32) (then (i32.const 0))
      (else (local.get $n) (i32.const 1) (i32.sub) (call $isEven)))))
