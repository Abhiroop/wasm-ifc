(module (memory 1) (data (i32.const 0) "\61\61\61\61\62\62\62\62")
  ;; Example 1: a load declared public reads a byte of the secret region: trap
  (func (export "f") (result i32) i32.const 1 i32.load))
