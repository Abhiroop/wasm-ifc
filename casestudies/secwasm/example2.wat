(module (memory 1) (data (i32.const 0) "\61\61\61\61\62\62\62\62")
  ;; Example 2: the same load declared secret succeeds, and its value is secret
  (global (mut i32) (i32.const 0))
  (func (export "f") i32.const 1 i32.load global.set 0))
