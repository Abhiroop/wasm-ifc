(module
  ;; br 1 jumps out of two nested blocks, carrying the i32 result.
  (func $nested (export "nested") (result i32)
    (block $outer (result i32)
      (block $inner (result i32)
        (i32.const 4)
        (br 1)        ;; jump out of $outer, keeping 4 as its result
        (i32.const 99) ;; dead code
      )
      (i32.const 7)
      (i32.add))))    ;; skipped: $outer already has its result
