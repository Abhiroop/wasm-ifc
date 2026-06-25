(module
  (func $block-simple (result i32)
    ;; VAL: context has locals: [], labels: []
    ;; VAL: type so far is [] -> []
    ;; EXEC: stack is []
    (block (result i32) ;; type: [] -> [i32]
      ;; VAL: block of type [] -> [i32], remember label by output [i32]
      ;; VAL: context has locals: [], labels: [[i32]]
      ;; VAL: type so far is [] -> []
      ;; EXEC: arity is 1 (from type output)
      ;; EXEC: push label; stack is [label(arity=1)]
      (i32.const 10)
      ;; VAL: type of last instruction is [...] -> [..., i32]
      ;; VAL: type so far is [] -> [i32]
      (i32.const 20)
      ;; VAL: type of last instruction is [...] -> [..., i32]
      ;; VAL: type so far is [] -> [i32, i32]
      ;; EXEC: stack is [label(arity=1), value(10), value(20)]
      (i32.add)
      ;; VAL: type of last instruction is [..., i32, i32] -> [..., i32]
      ;; VAL: type so far is [] -> [i32]
      ;; EXEC: stack is [label(arity=1), value(30)]
      ;; VAL: block's body has type [] -> [i32], expected [] -> [i32] -- OK
      ;; EXEC: label is eliminated (pop all stack until label, pop label, re-push)
    )
    ;; VAL: context has locals: [], labels: []
    ;; VAL: type of last instruction is [...] -> [..., i32]
    ;; VAL: type so far is [] -> [i32]
    ;; EXEC: stack is [value(30)]
    ;; VAL: function's body has type [] -> [i32], expected [] -> [i32] -- OK
    ;; EXEC: call frame is eliminated (TODO)
  )
)