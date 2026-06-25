(module
  (memory 1)   ;; one 64 KiB page
  (func $oob (export "oob") (param $addr i32) (result i32)
    (i32.load (local.get $addr))))
