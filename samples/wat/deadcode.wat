(module
  (func $dead (export "dead") (result i32)
    (block (result i32)
      (i32.const 5)
      (br 0)
      (i32.add))))   ;; dead: i32.add on an empty (polymorphic) stack
