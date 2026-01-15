(module
  (func $example (result i32)

    (block (result i32)
      ;; Produce initial value inside the block
      i32.const 10

      ;; Exit the block immediately
      br 0

      ;; Never executed
      i32.const 5
      i32.add
      end
    )

    ;; Stack now contains the block result: [10]

    i32.const 3
    i32.add
  )
)
