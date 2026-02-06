(module
  (func $block-simple (result i32)
    (block (result i32)
    ;; VAL: context has locals: [], labels: [label(arity=1)]
    ;; VAL: type so far is [] -> []
    ;; EXEC: stack is []
      (block (result i32 i32) ;; type: [] -> [i32]
        ;; VAL: block of type [] -> [i32, i32], remember label by output [i32, i32]
        ;; VAL: context has locals: [], labels: [[i32], [i32, i32]]
        ;; VAL: type so far is [] -> []
        ;; EXEC: arity is 2 (from type output)
        ;; EXEC: push label; stack is [label(arity=2)]
        (i32.const 10)
        ;; VAL: type of last instruction is [...] -> [..., i32]
        ;; VAL: type so far is [] -> [i32]
        (i32.const 20)
        (i32.const 10)
        ;; VAL: type of last instruction is [...] -> [..., i32, i32]
        ;; VAL: type so far is [] -> [i32, i32, i32]
        ;; EXEC: stack is [label(arity=2), value(10), value(20), value(10)]
        (i32.add)
        ;; VAL: type of last instruction is [..., i32, i32, i32] -> [..., i32, i32]
        ;; VAL: type so far is [] -> [i32, i32]
        ;; EXEC: stack is [label(arity=2), value(10), value(30)]
        (br 1)
        ;; VAL: in context, label 0 is [i32, i32], label 1 is [i32]
        ;; VAL: type needed here is [] -> [i32]
        ;; VAL: type of last instruction is synthesized [...] + [i32] -> [...] = [..., i32] -> [..., i32]
        ;; VAL: type so far is [] -> [i32]
        ;; VAL: block's body has type [] -> [i32], expected [] -> [i32] -- OK
        ;; EXEC: label 1 has arity 1
        ;; EXEC: pop all stack until label 1, pop labels, re-push 1, discard rest; stack is [value(30)]
        ;; EXEC: control flow jumps forward out of block

      )
    ;; technically unreachable
    )
    ;; VAL: context has locals: [], labels: []
    ;; VAL: should be [i32]
    ;; EXEC: stack should be [value(30)]
    ;; HOWEVER THERE IS COMPILATION ERROR STATING THAT THER IS ONE MORE I32 ON THE STACK

  )
)

;; THOUGHTS: WASM validation and execution fork here
;; VALIDATION: it simply checks whether exactly what is expected is on the stack at the end of each block. 
    ;; INNER BLOCK: expects [i32, i32] at the end, when going through it linearly it is also [i32, i32], so OK
    ;; BRANCH VALIDATION: simply checks whether at the point of br 1 the stack can provide [i32] on top (but apparently see next example pops off values according to label of inner block) -- it can, so OK
    ;; OUTER BLOCK: expects [i32] at the end, when going through it, linearly it is [i32, i32], so ERROR

;; EXECUTION: would actually work differently here and this would be fine!!!
    ;; INNER BLOCK: executes fine, stack at the end is [i32] because of branch
    ;; BRANCH EXECUTION: pops until label 1, which has arity 1, so pops two values (i32, i32), re-pushes one (i32), stack is now [i32]
    ;; OUTER BLOCK: at the end stack is [i32], as expected, so OK


;; (module
;;   (func $block-simple (result i32 i32)
;;     (block (result i32 i32)
;;     ;; VAL: context has locals: [], labels: [label(arity=2)]
;;     ;; VAL: type so far is [] -> []
;;     ;; EXEC: stack is []
;;       (block (result i32) ;; type: [] -> [i32]
;;         ;; VAL: block of type [] -> [i32], remember label by output [i32]
;;         ;; VAL: context has locals: [], labels: [[i32, i32], [i32]]
;;         ;; VAL: type so far is [] -> []
;;         ;; EXEC: arity is 1 (from type output)
;;         ;; EXEC: push label; stack is [label(arity=1)]
;;         (i32.const 10)
;;         ;; VAL: type of last instruction is [...] -> [..., i32]
;;         ;; VAL: type so far is [] -> [i32]
;;         (i32.const 20)
;;         (i32.const 10)
;;         ;; VAL: type of last instruction is [...] -> [..., i32, i32]
;;         ;; VAL: type so far is [] -> [i32, i32, i32]
;;         ;; EXEC: stack is [label(arity=1), value(10), value(20), value(10)]
;;         (i32.add)
;;         ;; VAL: type of last instruction is [..., i32, i32, i32] -> [..., i32, i32]
;;         ;; VAL: type so far is [] -> [i32, i32]
;;         ;; EXEC: stack is [label(arity=1), value(10), value(30)]
;;         (br 1)
;;         ;; VAL: in context, label 0 is [i32], label 1 is [i32, i32]
;;         ;; VAL: type needed here is [] -> [i32, i32] => or so one would think => but might actually be [] -> [i32] 
;;         ;; VAL: type of last instruction is synthesized [...] + [i32] -> [...] = [..., i32] -> [..., i32]
;;         ;; VAL: type so far is [] -> [i32, i32] => but it might actually be [] -> [i32]
;;         ;; EXEC: label 1 has arity 2
;;         ;; EXEC: pop all stack until label 1, pop labels, re-push 1, discard rest; stack is [value(30)]
;;         ;; EXEC: control flow jumps forward out of block

;;       )
;;     ;; technically unreachable
;;     )
;;     ;; VAL: context has locals: [], labels: []
;;     ;; VAL: should be [i32]
;;     ;; EXEC: stack should be [value(30)]
;;     ;; HOWEVER THERE IS COMPILATION ERROR STATING THAT THER IS ONE MORE I32 ON THE STACK

;;   )
;; )

;; THOUGHTS: WASM validation and execution fork here, here it seems as if br just simple removes the values on top of the stack according to the inner block's label
;; VALIDATION: it simply checks whether exactly what is expected is on the stack at the end of each block. 
    ;; INNER BLOCK: expects [i32] at the end, when going through it linearly it is also [i32] because of br (REMOVES WHATEVER IS IN TOP LABEL APPARENTLY IN VALIDATION, MAKES NO SENSE?), so OK
    ;; BRANCH VALIDATION: simply checks whether at the point of br 1 the stack can provide [i32] on top -- it can, so OK
    ;; OUTER BLOCK: expects [i32, i32] at the end, when going through it, linearly it is [i32] BECAUSE OF BRANCH IN INNER BLOCK??, so ERROR

;; EXECUTION: would actually work differently here and this would be fine!!!
    ;; INNER BLOCK: executes fine, stack at the end is [i32] because of branch
    ;; BRANCH EXECUTION: pops until label 1, which has arity 1, so pops two values (i32, i32), re-pushes one (i32), stack is now [i32]
    ;; OUTER BLOCK: at the end stack is [i32], as expected, so OK