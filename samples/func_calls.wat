(module
  ;; Function to add two i32 numbers
  (func $add (param $a i32) (param $b i32) (result i32)
    local.get $a
    local.get $b
    i32.add)

  ;; Function to double a number using $add
  (func $double (param $x i32) (result i32)
    local.get $x
    local.get $x
    call $add      ;; calls function $add
  )

  ;; Main exported function
  (func (export "main") (result i32)
    i32.const 21    ;; push integer 21 onto the stack
    call $double    ;; call the $double function
  )
)
