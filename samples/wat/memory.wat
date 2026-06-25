(module
  (memory 1)
  ;; store x at address 0, then load it back doubled via add
  (func $roundtrip (export "roundtrip") (param $x i32) (result i32)
    (i32.const 0)
    (local.get $x)
    (i32.store)
    (i32.const 0)
    (i32.load)
    (i32.const 0)
    (i32.load)
    (i32.add)))
