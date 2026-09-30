(module (memory 1) (data (i32.const 0) "\61\61\61\61\62\62\62\62")
  ;; Example 3: a store declared secret relabels the bytes it writes; a public load of them then traps
  (func (export "f") (result i32)
    i32.const 2 i32.const 99 i32.store
    i32.const 0 i32.load))
