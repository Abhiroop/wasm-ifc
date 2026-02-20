;; (module
;;   (func $block-simple (result i32 i64)
;;     (block (result i32 i64)
;;       (i32.const 10)
;;       (block (result i32)
;;         (i32.const 20)
;;         (i64.const 30)
;;         (br 1)
;;       )
;;     )
;;   )
;; )
;; Why this compile with a weird error and not like expected?
;; Error is that it fails with expected [i32, i64] but got [i32, i32]
;; however assuming it does as in execution it would get [i32, i64] with [20,30]
;; If we assume it simply does what top label wants it would also be
;;  [i32,i64] since i64 is on top of stack but values would be [10,30]
;; third option is that it just casts the value without saying anything because inner block returns i32
;;    so in this case it would be [i32, i32] with values [10,30]


;; (module
;;   (func $block-simple (result i32 i64)
;;     (block (result i32 i64)
;;       (i32.const 10)
;;       (block (result i64)
;;         (i32.const 20)
;;         (i64.const 30)
;;         (br 1)
;;       )
;;     )
;;   )
;; )

;; This compiles because the type however you do it the type is correct



;; (module
;;   (func $block-simple (result i32)
;;     (block (result i32)
;;       (block (result i32)
;;         (i32.const 20)
;;         (i32.const 10)
;;         (br 0)
;;         (i32.add)
;;         (i32.add)
;;         (i32.add)
;;         (i32.add)
;;         (i32.add)
;;         (i32.add)
;;         (i32.add)
;;       )
;;     )
;;   )
;; )
;; This compiles.......


;; (module
;;   (func $block-simple (result i32 i32)
;;     (block (result i32 i32)
;;       (block (result i32)
;;         (i32.const 20)
;;         (i32.const 10)
;;         (br 1)
;;       ) ;; does the end of the block just remove the top value on the stack?
;;     )
;;   )
;; )


;; This does not compile
;; because when the end of the block is reached validation checks whether the ret type of the block is on top and

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (module
;;   (func $block-simple (result i32 i32)
;;     (block (result i32 i32)
;;       (block (result i32)
;;         (i32.const 20)
;;         (i32.const 10)
;;         (br 1) ;; here it is the same whether I put br0 or br1 as long as I have the const 30
;;       ) ;; does the end of the block just remove the top value on the stack?
;;       (i32.const 30)
;;     )
;;   )
;; )

;; This compiles as well so in validation somehow the i32.const is considered


;; (module
;;   (func $block-simple (result i32 i32)
;;     (block (result i32 i32)
;;       (i32.const 20)
;;       (block (result i32)
;;         (i32.const 10)
;;         (br 1) ;; here it is the same whether I put br0 or br1 as long as I have the const 30
;;       ) ;; does the end of the block just remove the top value on the stack?
;;     )
;;   )
;; )

;; (module
;;   (func $block-simple (result i32 i32)
;;     (block (result i32 i32)
;;       (i32.const 20)
;;       (block (result i32)
;;         (i32.const 10)
;;         (br 1)
;;       )
;;     )
;;   )
;; )

(module
  (func $block-simple (result i32 i32)
    (block (result i32 i32)               ;; depth 2
      (i32.const 20)      
      (block (result i32)
          i32.const 6                 ;; depth 1
          (block (result i32)             ;; depth 0 (innermost)
                i32.const 4
                br 1                      ;; jump out of two enclosing blocks
                ;; unreachable
          )
          i32.add
          ;; skipped
      )
      ;; execution continues here after end of block with depth 1
      )
  )
)
