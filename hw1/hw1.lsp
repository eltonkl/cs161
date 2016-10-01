; TREE-CONTAINS N TREE
; Determines whether the given ordered tree TREE contains the number N
; Returns T if N is contained in TREE, or NIL otherwise
; Base case: if TREE is a number, return whether N == TREE
; Otherwise check if TREE's m is <, ==, or > than N and recursively call
;   TREE-CONTAINS on the subtree or check equality between m and N
(defun TREE-CONTAINS (N TREE)
    (cond ((numberp TREE) (= N TREE))
          (t (cond ((< N (second TREE)) (TREE-CONTAINS N (first TREE)))
                   ((= N (second TREE)) t)
                   (t (TREE-CONTAINS N (third TREE)))))))

; TREE-MAX TREE
; Returns the maximum number of the ordered tree TREE
; Base case: if TREE is a number, return TREE
; Otherwise return TREE-MAX on the right subtree, which we know only
;   contains numbers greater than m
(defun TREE-MAX (TREE)
    (cond ((numberp TREE) TREE)
          (t (TREE-MAX (third TREE)))))

; TREE-ORDER TREE
; Returns, in list form, the in-order traversal of the numbers in the
;   ordered tree TREE
; Base case: if TREE is a number, return (list TREE)
; Otherwise return a list consisting of the in-order traversal of the
;   left sub-tree prepended to a list consisting of the middle
;   prepended to the in-order traversal of the right sub-tree
(defun TREE-ORDER (TREE)
    (cond ((numberp TREE) (list TREE))
          (t (append (TREE-ORDER (first TREE))
                     (TREE-ORDER (second TREE))
                     (TREE-ORDER (third TREE))))))

; SUB-LIST L START LEN
; Returns the sub-list of L starting at position START with length LEN
; Base case: if LEN is 0, return NIL
; Base case: if START is 0, return a list consisting of the head of L
;   prepended to a recursive call to SUB-LIST with the tail of L and
;   a new LEN of the current LEN - 1
; Otherwise return a recursive call to SUB-LIST with the tail of L
;   and a starting position 1 less than the current START
(defun SUB-LIST (L START LEN)
   (cond ((= LEN 0) NIL)
         ((= START 0) (cons (car L) (SUB-LIST (cdr L) 0 (- LEN 1))))
         (t (SUB-LIST (cdr L) (- START 1) LEN))))

