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

; SPLIT-LIST L
; Takes a list L, and returns a list of two lists L1 and L2, in that
; order, such that L is the result of appending L1 and L2, and
; length of L2 minus length of L1 is 0 or 1
; There are two cases: even length L and odd length L
; If length is even then we can call SUB-LIST on the length divided by 2
; Otherwise we need to subtract 1 from the length and then divide by 2
; and then use that value to call SUB-LIST
(defun SPLIT-LIST (L)
    (cond
        ((evenp (length L))
         (let ((x (/ (length L) 2)))
              (list (SUB-LIST L 0 x) (SUB-LIST L x x))))
        ((oddp (length L))
         (let ((x (/ (- (length L) 1) 2)))
              (list (SUB-LIST L 0 x) (SUB-LIST L x (+ x 1)))))))

; BTREE-HEIGHT TREE
; Returns the height of the binary tree TREE
; Base case: TREE is an atom - height is 0
; Otherwsie, add 1 to the greater of the BTREE-HEIGHTs of the
; children of the TREE
(defun BTREE-HEIGHT (TREE)
    (cond
        ((atom TREE) 0)
        (t (let ((x (BTREE-HEIGHT (first TREE)))
                 (y (BTREE-HEIGHT (second TREE))))
                (cond ((> x y) (+ 1 x))
                      (t (+ 1 y)))))))

; LIST2BTREE LEAVES
; Takes a non-empty list of atoms LEAVES, and returns a binary
; tree such that the tree leaves are the elements of LEAVES
; and for any internal node in the tree, the number of leaves
; in its right branch minus the number of leaves in its left
; branch is 0 or 1
; Base cases: LEAVES is length 1: return the only number in LEAVES
; LEAVES is length 2: return a list of the first two numbers
; Otherwise: split the list using SPLIT-LIST and combine the
; results of recursive calls to LIST2BTREE on the two halves
(defun LIST2BTREE (LEAVES)
    (cond 
        ((= (length LEAVES) 1) (first LEAVES))
        ((= (length LEAVES) 2) (list (first leaves) (second LEAVES)))
        (t (let
             ((lists (SPLIT-LIST LEAVES)))
             (list (LIST2BTREE (first lists)) (LIST2BTREE (second lists)))))))

; BTREE2LIST TREE
; The inverse of LIST2BTREE: takes a binary tree TREE, and returns a list
; of atoms
; Base case: TREE is an atom: return a list consisting of the atom
; Tree is a list of length 1: recursively call BTREE2LIST on the head of the list
; Otherwise: append the result of a recursive call to BTREE2LIST of the head of
; the list to a recursive call to BTREE2LIST on the tail of the list
(defun BTREE2LIST (TREE)
    (cond ((atom TREE) (list TREE))
          ((= (length TREE) 1) (BTREE2LIST (car TREE)))
          (t (append (BTREE2LIST (car TREE)) (BTREE2LIST (cdr TREE))))))

; IS-SAME E1 E2
; Given two Lisp expressions E1 and E2, whose atoms are all numbers,
; return T if the expressions are identical and NIL otherwise
; Base cases:
;       Both nil: true
;       Both numbers: E1 == E2
; Otherwise:
;       Both lists: logical and the result of IS-SAME recursively on
;                   the heads of E1 and E2 and the result of IS-SAME
;                   on the tails of E1 and E2
; If E1 and E2 are not both the same type, return false
(defun IS-SAME (E1 E2)
    (cond ((and (null E1) (null E2)) t)
          ((and (numberp E1) (numberp E2)) (= E1 E2))
          ((and (listp E1) (listp E2))
           (and (IS-SAME (car E1) (car E2)) (IS-SAME (cdr E1) (cdr E2))))
          (t nil)))
