(module
  (func $block-params (result i32)
    ;; VAL: context has locals: [], labels: []
    ;; VAL: type so far is [] -> []
    ;; EXEC: stack is []
    (i32.const 100)
    ;; VAL: type so far is [] -> [i32]
    ;; EXEC: stack is [value(100)]
    (i32.const 200)
    ;; VAL: type so far is [] -> [i32, i32]
    ;; EXEC: stack is [value(100), value(200)]
    (block (param i32) (result i32) ;; type: [i32] -> [i32]
      ;; VAL: block of type [i32] -> [i32], remember label by output [i32]
      ;; VAL: context has locals: [], labels: [[i32]]
      ;; VAL: type so far is [i32] -> [i32]
      ;; EXEC: arity is 1 (from type output)
      ;; EXEC: pop top value, push label, push value back
      ;; EXEC: stack is [value(100), label(arity=1), value(200)]
      (i32.const 50)
      ;; VAL: type of last instruction is [...] -> [..., i32]
      ;; VAL: type so far is [i32] -> [i32, i32]
      ;; EXEC: stack is [value(100), label(arity=1), value(200), value(50)]
      (i32.sub)
      ;; VAL: type of last instruction is [..., i32, i32] -> [..., i32]
      ;; VAL: type so far is [i32] -> [i32]
      ;; VAL: block's body has type [i32] -> [i32], expected [i32] -> [i32] -- OK
      ;; EXEC: stack is [value(100), label(arity=1), value(150)]
      ;; EXEC: label is eliminated (pop all stack until label, pop label, re-push)
    )
    ;; VAL: type of last instruction is [..., i32] -> [..., i32]
    ;; VAL: type so far is [] -> [i32, i32]
    ;; EXEC: stack is [value(100), value(150)]
    (i32.add)
    ;; VAL: type of last instruction is [..., i32, i32] -> [..., i32]
    ;; VAL: type so far is [] -> [i32]
    ;; EXEC: stack is [value(250)]
    ;; VAL: function's body has type [] -> [i32], expected [] -> [i32] -- OK
    ;; EXEC: call frame is eliminated (TODO)
  )
)