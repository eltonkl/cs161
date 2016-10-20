;
; CS161 HW3: Sokoban
;
; *********************
;    READ THIS FIRST
; *********************
;
; All functions that you need to modify are marked with 'EXERCISE' in their
; header comments. This file also contains many helper functions. You may call
; any of them in your functions.
;
; Do not modify a-star.lsp.
;
; *Warning*: The provided A* code only supports the maximum cost of 4999 for any
; node. That is f(n)=g(n)+h(n) < 5000. So, be careful when you write your
; heuristic functions.  Do not make them return anything too large.
;
; For Allegro Common Lisp users: The free version of Allegro puts a limit on
; memory. So, it may crash on some hard sokoban problems and there is no easy
; fix (unless you buy Allegro). Of course, other versions of Lisp may also crash
; if the problem is too hard, but the amount of memory available will be
; relatively more relaxed. Improving the quality of the heuristic will mitigate
; this problem, as it will allow A* to solve hard problems with fewer node
; expansions. In either case, this limitation should not significantly affect
; your grade.
; 
; Remember that most functions are not graded on efficiency (only correctness).
; Efficiency can only influence your heuristic performance in the competition
; (which will affect your score).
;  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; General utility functions
; They are not necessary for this homework.
; Use/modify them for your own convenience.
;

;
; For reloading modified code.
; I found this easier than typing (load "filename") every time.
;
(defun reload ()
  (load "hw3.lsp")
  )

;
; For loading a-star.lsp.
;
(defun load-a-star ()
  (load "a-star.lsp"))

;
; Reloads hw3.lsp and a-star.lsp
;
(defun reload-all ()
  (reload)
  (load-a-star)
  )

;
; A shortcut function.
; goal-test and next-states stay the same throughout the assignment.
; So, you can just call (sokoban <init-state> #'<heuristic-name>).
; 
(defun sokoban (s h)
  (a* s #'goal-test #'next-states h)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; end general utility functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; We now begin actual Sokoban code
;

; Define some global variables
(setq blank 0)
(setq wall 1)
(setq box 2)
(setq keeper 3)
(setq star 4)
(setq boxstar 5)
(setq keeperstar 6)

; Some helper functions for checking the content of a square
(defun isBlank (v)
  (= v blank)
  )

(defun isWall (v)
  (= v wall)
  )

(defun isBox (v)
  (= v box)
  )

(defun isKeeper (v)
  (= v keeper)
  )

(defun isStar (v)
  (= v star)
  )

(defun isBoxStar (v)
  (= v boxstar)
  )

(defun isKeeperStar (v)
  (= v keeperstar)
  )

;
; Helper function of getKeeperPosition
;
(defun getKeeperColumn (r col)
  (cond ((null r) nil)
	(t (if (or (isKeeper (car r)) (isKeeperStar (car r)))
	       col
	     (getKeeperColumn (cdr r) (+ col 1))
	     );end if
	   );end t
	);end cond
  )

;
; getKeeperPosition (s firstRow)
; Returns a list indicating the position of the keeper (c r).
; 
; Assumes that the keeper is in row >= firstRow.
; The top row is the zeroth row.
; The first (right) column is the zeroth column.
;
(defun getKeeperPosition (s row)
  (cond ((null s) nil)
	(t (let ((x (getKeeperColumn (car s) 0)))
	     (if x
		 ;keeper is in this row
		 (list x row)
		 ;otherwise move on
		 (getKeeperPosition (cdr s) (+ row 1))
		 );end if
	       );end let
	 );end t
	);end cond
  );end defun

;
; cleanUpList (l)
; returns l with any NIL element removed.
; For example, if l is '(1 2 NIL 3 NIL), returns '(1 2 3).
;
(defun cleanUpList (L)
  (cond ((null L) nil)
	(t (let ((cur (car L))
		 (res (cleanUpList (cdr L)))
		 )
	     (if cur
		 (cons cur res)
		  res
		 )
	     );end let
	   );end t
	);end cond
  );end

; no-boxes row
; Helper function for goal-test
; Returns t if the row contains no boxes and nil otherwise
(defun no-boxes (row)
	(cond
        ((null row) t)
        ((isBox (first row)) nil)
        (t (no-boxes (rest row)))
    )
)

; goal-test s
; return true (t)
; if and only if s is a goal state of a Sokoban game.
; (no box is on a non-goal square)

(defun goal-test (s)
    (cond
        ((null s) t)
        ((no-boxes (first s)) (goal-test (rest s)))
        (t nil)
    )
)

; get-square s r c
; Helper function for try-move
; Given state s, row number r, column number c, returns the integer
; content of square (r, c) for the state s.
(defun get-square (s r c)
    (let
        (
            (num-r (length s))
            (num-c (length (first s)))
        )
        (cond
            ((or (= r num-r) (> r num-r) (= c num-c) (> c num-c) (< r 0) (< c 0)) wall) ; ARE WE ALLOWED TO USE >= or <=???
            ; ^^^ Bounds checks
            (t (car (nthcdr c (car (nthcdr r s)))))
        )
    )
)

; set-square s r c v
; Helper function for try-move
; Given state s, row number r, column number c, and square content v
; Returns the new state obtained by setting the square (r, c) to value v
(defun set-square (s r c v)
    (let*
        (
            (frontrows (butlast s (- (length s) r))) ; Rows in front of the desired row
            (currow (car (nthcdr r s))) ; Desired row
            (backrows (cdr (nthcdr r s))) ; Row behind the desired row
            (frontcols (butlast currow (- (length currow) c))) ; Cols behind the desired col
            (backcols (cdr (nthcdr c currow))) ; Cols in front of the desired col
            (newcols (append frontcols (list v) backcols)) ; Create new col
            (newrows (append frontrows (list newcols) backrows)) ; Create new rows
        )
        newrows
    )
)

; 0 is up
; 1 is right
; 2 is down
; 3 is left
; We aren't allowed to use globals, so I'll just have to mark direction-int correspondence in a comment

; try-move s d
; Helper function for next-states
; For a given state s and a given direction d (where d is an int corresponding) to the table above,
; returns the valid state s if the keeper can move in the given direction (while moving the relevant box or updating states appropriately)
; or returns nil otherwise.
(defun try-move (s d)
    (let*
        (
            (keeper-pos (getKeeperPosition s 0))
            (keeper-r (cadr keeper-pos))
            (keeper-c (car keeper-pos))
            (delta-r (cond ((= d 0) -1) ((= d 1) 0) ((= d 2) 1) ((= d 3) 0))) ; row delta for the given direction
            (delta-c (cond ((= d 0) 0) ((= d 1) 1) ((= d 2) 0) ((= d 3) -1))) ; col delta for the given direction
            (new-keeper-r (+ keeper-r delta-r))
            (new-keeper-c (+ keeper-c delta-c))
            (old-square-cur-val (get-square s keeper-r keeper-c)) ; Keeper's old position's current value
            (new-square-cur-val (get-square s new-keeper-r new-keeper-c)) ; Keeper's new position's current value
            (old-square-new-val (cond ((isKeeper old-square-cur-val) blank) (t star))) ; If the keeper wasn't on a star, it becomes blank, but if the keeper was on a star, it becomes star
            (new-square-new-val (cond ((or (isStar new-square-cur-val) (isBoxStar new-square-cur-val)) keeperstar) (t keeper))) ; If the keeper moves onto a star, the new position value becomes keeperstar. Otherwise, the value becomes keeper
        )
        (cond
            ((isWall new-square-cur-val) nil) ; If the keeper would move onto a wall, return nil
            (t
                (let*
                    (
                        (keeper-moved-from-old-s (set-square s keeper-r keeper-c old-square-new-val)) ; State after the keeper moves off the current square (keeper is not on the new square yet)
                        (keeper-moved-onto-new-s (set-square keeper-moved-from-old-s new-keeper-r new-keeper-c new-square-new-val)) ; State after keeper moves onto new square))
                    )
                    (cond
                        ( ; Keeper is moving onto what is currently a box
                            (or (isBox new-square-cur-val) (isBoxStar new-square-cur-val))
                            (let*
                                (
                                    (new-box-r (+ new-keeper-r delta-r)) ; Box is being pushed - what's the new r
                                    (new-box-c (+ new-keeper-c delta-c)) ; New c
                                    (new-box-cur-val (get-square s new-box-r new-box-c))
                                )
                                (cond
                                    (
                                        (or (isBlank new-box-cur-val) (isStar new-box-cur-val)) ; Where the box is being moved to is a valid position for the box to be moved to
                                        (let*
                                            (
                                                (new-box-new-val (cond ((isBlank new-box-cur-val) box) (t boxstar))) ; If the new position of the box is blank, then it becomes box; otherwise if it was star, it becomes boxstar
                                                (box-moved-onto-new-s (set-square keeper-moved-onto-new-s new-box-r new-box-c new-box-new-val)) ; New state after box is moved
                                            )
                                            box-moved-onto-new-s
                                        )
                                    )
                                    (t nil) ; Box being moved onto something that's not empty or a star
                                )
                            )
                        )
                        ((or (isBlank new-square-cur-val) (isStar new-square-cur-val)) keeper-moved-onto-new-s) ; If the keeper is moving onto a blank spot or a star, return the state after the keeper moves onto the new square
                        (t nil) ; Invalid move, return nil
                    )
                )
            )
        )
    )
)

; next-states s
; Returns the list of sucessor states of s.
; This is the top-level next-states (successor) function.
(defun next-states (s)
    (let* ((pos (getKeeperPosition s 0))
	    (r (car pos))
	    (c (cadr pos))
	    ;x and y are now the coordinate of the keeper in s.
	    (result (list (try-move s 0) (try-move s 1) (try-move s 2) (try-move s 3)))
	)
    (cleanUpList result);end
    );end let
);

; h0 s
; Computes the trivial admissible heuristic.
(defun h0 (s)
    0 ; Whew, that was hard
)

; count-boxes row
; Helper function for h1
; Returns the number of boxes in the row.
(defun count-boxes (row)
    (count box row)
)

; h1 s
; Computes the number of misplaced boxes in s.
; h1 is an admissible function - at the minimum, it counts the number of moves that have to be made to finish the game; thus, no overestimating will occur.
(defun h1 (s)
    (cond
        ((null s) 0)
        (t (+ (count-boxes (first s)) (h1 (rest s))))
    )
)

; Objective: make A* solve problems as fast as possible.
; The Lisp 'time' function can be used to measure the
; running time of a function call.

; Helper for col-manhats
; manhat r1 c1 r2 c2
; Computes manhattan distance of given coordinate pairs (r1, c1) and (r2, c2)
(defun manhat (r1 c1 r2 c2)
    (let
        (
            (diff-r (cond ((> r1 r2) (- r1 r2)) (t (- r2 r1))))
            (diff-c (cond ((> c1 c2) (- c1 c2)) (t (- c2 c1))))
        )
        (+ diff-r diff-c)
    )
)

; Helper for total-manhats
; col-manhats row row-num col-num accum keeper-r keeper-c
; Given a row and its number (row-num) and the head of the row's column number (col-num)
; and an accumulator accum (in hopes of tail call optimization)
; and the precomputed keeper coordinates (keeper-r, keeper-c)
; Returns the sum of the manhattan distances between each box and the keeper for the given row
(defun col-manhats (row row-num col-num accum keeper-r keeper-c)
    (cond
        ((null row) accum)
        (t 
            (let*
                (
                    (cur-manhat (cond ((isBox (car row)) (manhat row-num col-num keeper-r keeper-c)) (t 0)))
                    (new-accum (+ accum cur-manhat))
                )
                (col-manhats (cdr row) row-num (+ 1 col-num) new-accum keeper-r keeper-c)
            )
        )
    )
)

; Helper for h3
; total-manhats s row-num accum keeper-r keeper-c
; Given a state s and the head of the state (the current row)'s row number (row-num)
; and an accumulator and keeper coordinates, returns the sum of the manhattan distances between each box
; and the keeper for the whole map

(defun total-manhats (s row-num accum keeper-r keeper-c)
    (cond
        ((null s) accum)
        (t
            (let*
                (
                    (cur-col-manhats (col-manhats (car s) row-num 0 0 keeper-r keeper-c))
                    (new-accum (+ accum cur-col-manhats))
                )
                (total-manhats (cdr s) (+ 1 row-num) new-accum keeper-r keeper-c)
            )
        )
    )
)

; h3: admissible heuristic #1 to be used in conjunction with another heuristic
; h3 s
; see total-manhats for the actual description of this heuristic
(defun h3 (s)
    (let*
        (
            (keeper (getKeeperPosition s 0))
            (keeper-r (cadr keeper))
            (keeper-c (car keeper))
        )
        (total-manhats s 0 0 keeper-r keeper-c)
    )
)

; get-square-fast, helper for corner
; get-square-f s num-r num-c r c
; Use precomputed num-r num-c instead of calculating it every time we call get-square
(defun get-square-f (s num-r num-c r c)
    (cond
        ((or (= r num-r) (> r num-r) (= c num-c) (> c num-c) (< r 0) (< c 0)) wall) ; ARE WE ALLOWED TO USE >= or <=???
        ; ^^^ Bounds checks
        (t (car (nthcdr c (car (nthcdr r s)))))
    )
)

; box-in-corner-score: helper for box-corner-col-score, which is indirectly a helper for h4
; box-in-corner-score orig-s orig-r orig-c r c
; If (r, c) is trapped in a corner, return 100, otherwise 0
; Making h(n) a minimum of 100 makes the state this (r, c) is contained in very unlikely to be explored
; If there is a box in a corner, we want to not explore this state anymore, so adding a large number makes that the case
; Can't use a really big number because our maximum for f(n) for the given a-star is 4999
(defun box-in-corner-score (orig-s orig-r orig-c r c)
    (let*
        (
            (up (- r 1))
            (down (+ r 1))
            (left (- c 1))
            (right (+ c 1))
            (up-n (cond ((isWall (get-square-f orig-s orig-r orig-c up c)) 1) (t 0)))
            (down-n (cond ((isWall (get-square-f orig-s orig-r orig-c down c)) 1) (t 0)))
            (left-n (cond ((isWall (get-square-f orig-s orig-r orig-c r left)) 1) (t 0)))
            (right-n (cond ((isWall (get-square-f orig-s orig-r orig-c r right)) 1) (t 0)))
            (v-wall-count (+ up-n down-n))
            (h-wall-count (+ left-n right-n))
        )
        (cond
            ((and (> v-wall-count 0) (> h-wall-count 0)) 100)
            (t 0)
        )
    )
)

; Helper function for total-box-corner-score
; box-corner-col-score totals all calls of corner on box coords for the given row
; Uses the same precompute and accumulate strategy as the helpers for h3
(defun box-corner-col-score (orig-s orig-r orig-c row row-num col-num accum)
    (cond
        ((null row) accum)
        (t 
            (let*
                (
                    (cur-corner (cond ((isBox (car row)) (box-in-corner-score orig-s orig-r orig-c row-num col-num)) (t 0)))
                    (new-accum (+ accum cur-corner))
                )
                (box-corner-col-score orig-s orig-r orig-c (cdr row) row-num (+ 1 col-num) new-accum)
            )
        )
    )
)

; Helper function for h4
; total-box-corner-score orig-s orig-r orig-c s row-num accum
; Same idea: total score of all boxes in corners for the given state s
(defun total-box-corner-score (orig-s orig-r orig-c s row-num accum)
    (cond
        ((null s) accum)
        (t
            (let*
                (
                    (cur-box-corner-col-score (box-corner-col-score orig-s orig-r orig-c (car s) row-num 0 0))
                    (new-accum (+ accum cur-box-corner-col-score))
                )
                (total-box-corner-score orig-s orig-r orig-c (cdr s) (+ 1 row-num) new-accum)
            )
        )
    )
)

; h4: admissible heuristic
; Basically, if we have a box in a corner, we want this state to not be expanded, so add a large number
(defun h4 (s)
    (total-box-corner-score s (length s) (length (first s)) s 0 0)
)

; h2: Combination of h3 and h4 (this is pretty fast!)
; Admissible heuristic: the total of manhattan distances of boxes to the keeper
; and if there is a box in a corner, try to get the A* to skip this state
(defun h2 (s)
    (+ (h3 s) (h4 s))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
 | Some predefined problems.  Each problem can be visualized by calling
 | (printstate <problem>).  Problems are ordered roughly by their difficulties.
 | For most problems, we also privide 2 additional number per problem: 1) # of
 | nodes expanded by A* using our next-states and h0 heuristic.  2) the depth of
 | the optimal solution.  These numbers are located at the comments of the
 | problems. For example, the first problem below was solved by 80 nodes
 | expansion of A* and its optimal solution depth is 7.
 |
 | Your implementation may not result in the same number of nodes expanded, but
 | it should probably give something in the same ballpark. As for the solution
 | depth, any admissible heuristic must make A* return an optimal solution. So,
 | the depths of the optimal solutions provided could be used for checking
 | whether your heuristic is admissible.
 |
 | Warning: some problems toward the end are quite hard and could be impossible
 | to solve without a good heuristic!
 |
 |#

;(80,7)
(setq p1 '((1 1 1 1 1 1)
	   (1 0 3 0 0 1)
	   (1 0 2 0 0 1)
	   (1 1 0 1 1 1)
	   (1 0 0 0 0 1)
	   (1 0 0 0 4 1)
	   (1 1 1 1 1 1)))

;(110,10)
(setq p2 '((1 1 1 1 1 1 1)
	   (1 0 0 0 0 0 1) 
	   (1 0 0 0 0 0 1) 
	   (1 0 0 2 1 4 1) 
	   (1 3 0 0 1 0 1)
	   (1 1 1 1 1 1 1)))

;(211,12)
(setq p3 '((1 1 1 1 1 1 1 1 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 0 0 0 2 0 3 4 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 0 0 0 1 0 0 0 1)
	   (1 1 1 1 1 1 1 1 1)))

;(300,13)
(setq p4 '((1 1 1 1 1 1 1)
	   (0 0 0 0 0 1 4)
	   (0 0 0 0 0 0 0)
	   (0 0 1 1 1 0 0)
	   (0 0 1 0 0 0 0)
	   (0 2 1 0 0 0 0)
	   (0 3 1 0 0 0 0)))

;(551,10)
(setq p5 '((1 1 1 1 1 1)
	   (1 1 0 0 1 1)
	   (1 0 0 0 0 1)
	   (1 4 2 2 4 1)
	   (1 0 0 0 0 1)
	   (1 1 3 1 1 1)
	   (1 1 1 1 1 1)))

;(722,12)
(setq p6 '((1 1 1 1 1 1 1 1)
	   (1 0 0 0 0 0 4 1)
	   (1 0 0 0 2 2 3 1)
	   (1 0 0 1 0 0 4 1)
	   (1 1 1 1 1 1 1 1)))

;(1738,50)
(setq p7 '((1 1 1 1 1 1 1 1 1 1)
	   (0 0 1 1 1 1 0 0 0 3)
	   (0 0 0 0 0 1 0 0 0 0)
	   (0 0 0 0 0 1 0 0 1 0)
	   (0 0 1 0 0 1 0 0 1 0)
	   (0 2 1 0 0 0 0 0 1 0)
	   (0 0 1 0 0 0 0 0 1 4)))

;(1763,22)
(setq p8 '((1 1 1 1 1 1)
	   (1 4 0 0 4 1)
	   (1 0 2 2 0 1)
	   (1 2 0 1 0 1)
	   (1 3 0 0 4 1)
	   (1 1 1 1 1 1)))

;(1806,41)
(setq p9 '((1 1 1 1 1 1 1 1 1) 
	   (1 1 1 0 0 1 1 1 1) 
	   (1 0 0 0 0 0 2 0 1) 
	   (1 0 1 0 0 1 2 0 1) 
	   (1 0 4 0 4 1 3 0 1) 
	   (1 1 1 1 1 1 1 1 1)))

;(10082,51)
(setq p10 '((1 1 1 1 1 0 0)
	    (1 0 0 0 1 1 0)
	    (1 3 2 0 0 1 1)
	    (1 1 0 2 0 0 1)
	    (0 1 1 0 2 0 1)
	    (0 0 1 1 0 0 1)
	    (0 0 0 1 1 4 1)
	    (0 0 0 0 1 4 1)
	    (0 0 0 0 1 4 1)
	    (0 0 0 0 1 1 1)))

;(16517,48)
(setq p11 '((1 1 1 1 1 1 1)
	    (1 4 0 0 0 4 1)
	    (1 0 2 2 1 0 1)
	    (1 0 2 0 1 3 1)
	    (1 1 2 0 1 0 1)
	    (1 4 0 0 4 0 1)
	    (1 1 1 1 1 1 1)))

;(22035,38)
(setq p12 '((0 0 0 0 1 1 1 1 1 0 0 0)
	    (1 1 1 1 1 0 0 0 1 1 1 1)
	    (1 0 0 0 2 0 0 0 0 0 0 1)
	    (1 3 0 0 0 0 0 0 0 0 0 1)
	    (1 0 0 0 2 1 1 1 0 0 0 1)
	    (1 0 0 0 0 1 0 1 4 0 4 1)
	    (1 1 1 1 1 1 0 1 1 1 1 1)))

;(26905,28)
(setq p13 '((1 1 1 1 1 1 1 1 1 1)
	    (1 4 0 0 0 0 0 2 0 1)
	    (1 0 2 0 0 0 0 0 4 1)
	    (1 0 3 0 0 0 0 0 2 1)
	    (1 0 0 0 0 0 0 0 0 1)
	    (1 0 0 0 0 0 0 0 4 1)
	    (1 1 1 1 1 1 1 1 1 1)))

;(41715,53)
(setq p14 '((0 0 1 0 0 0 0)
	    (0 2 1 4 0 0 0)
	    (0 2 0 4 0 0 0)
	    (3 2 1 1 1 0 0)
	    (0 0 1 4 0 0 0)))

;(48695,44)
(setq p15 '((1 1 1 1 1 1 1)
	    (1 0 0 0 0 0 1)
	    (1 0 0 2 2 0 1)
	    (1 0 2 0 2 3 1)
	    (1 4 4 1 1 1 1)
	    (1 4 4 1 0 0 0)
	    (1 1 1 1 0 0 0)
	    ))

;(91344,111)
(setq p16 '((1 1 1 1 1 0 0 0)
	    (1 0 0 0 1 0 0 0)
	    (1 2 1 0 1 1 1 1)
	    (1 4 0 0 0 0 0 1)
	    (1 0 0 5 0 5 0 1)
	    (1 0 5 0 1 0 1 1)
	    (1 1 1 0 3 0 1 0)
	    (0 0 1 1 1 1 1 0)))

;(3301278,76)
(setq p17 '((1 1 1 1 1 1 1 1 1 1)
	    (1 3 0 0 1 0 0 0 4 1)
	    (1 0 2 0 2 0 0 4 4 1)
	    (1 0 2 2 2 1 1 4 4 1)
	    (1 0 0 0 0 1 1 4 4 1)
	    (1 1 1 1 1 1 0 0 0 0)))

;(??,25)
(setq p18 '((0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1)
	    (0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0)
	    (0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0)
	    (0 0 0 0 0 0 0 0 3 0 0 0 0 0 0 0)
	    (0 0 0 0 0 0 1 0 0 1 0 0 0 0 0 0)
	    (0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0)
	    (1 1 1 1 1 0 0 0 0 0 0 1 1 1 1 1)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 0 0 0 0 4 1 0 0 0 0)
	    (0 0 0 0 1 0 2 0 0 0 0 1 0 0 0 0)
	    (0 0 0 0 1 0 2 0 0 0 4 1 0 0 0 0)
	    ))
;(??,21)
(setq p19 '((0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (1 1 1 1 0 0 0 0 1 1 1 1)
	    (0 0 0 0 1 0 0 1 0 0 0 0)
	    (0 0 0 0 0 0 3 0 0 0 2 0)
	    (0 0 0 0 1 0 0 1 0 0 0 4)
	    (1 1 1 1 0 0 0 0 1 1 1 1)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 0 0 0 1 0 0 0)
	    (0 0 0 1 0 2 0 4 1 0 0 0)))

;(??,??)
(setq p20 '((0 0 0 1 1 1 1 0 0)
	    (1 1 1 1 0 0 1 1 0)
	    (1 0 0 0 2 0 0 1 0)
	    (1 0 0 5 5 5 0 1 0)
	    (1 0 0 4 0 4 0 1 1)
	    (1 1 0 5 0 5 0 0 1)
	    (0 1 1 5 5 5 0 0 1)
	    (0 0 1 0 2 0 1 1 1)
	    (0 0 1 0 3 0 1 0 0)
	    (0 0 1 1 1 1 1 0 0)))

;(??,??)
(setq p21 '((0 0 1 1 1 1 1 1 1 0)
	    (1 1 1 0 0 1 1 1 1 0)
	    (1 0 0 2 0 0 0 1 1 0)
	    (1 3 2 0 2 0 0 0 1 0)
	    (1 1 0 2 0 2 0 0 1 0)
	    (0 1 1 0 2 0 2 0 1 0)
	    (0 0 1 1 0 2 0 0 1 0)
	    (0 0 0 1 1 1 1 0 1 0)
	    (0 0 0 0 1 4 1 0 0 1)
	    (0 0 0 0 1 4 4 4 0 1)
	    (0 0 0 0 1 0 1 4 0 1)
	    (0 0 0 0 1 4 4 4 0 1)
	    (0 0 0 0 1 1 1 1 1 1)))

;(??,??)
(setq p22 '((0 0 0 0 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 0 0 1 0 0 0 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 0 0 1 2 0 0 1 0 0 0 0 0 0 0 0 0 0)
	    (0 0 1 1 1 0 0 2 1 1 0 0 0 0 0 0 0 0 0)
	    (0 0 1 0 0 2 0 2 0 1 0 0 0 0 0 0 0 0 0)
	    (1 1 1 0 1 0 1 1 0 1 0 0 0 1 1 1 1 1 1)
	    (1 0 0 0 1 0 1 1 0 1 1 1 1 1 0 0 4 4 1)
	    (1 0 2 0 0 2 0 0 0 0 0 0 0 0 0 0 4 4 1)
	    (1 1 1 1 1 0 1 1 1 0 1 3 1 1 0 0 4 4 1)
	    (0 0 0 0 1 0 0 0 0 0 1 1 1 1 1 1 1 1 1)
	    (0 0 0 0 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
 | Utility functions for printing states and moves.
 | You do not need to understand any of the functions below this point.
 |#

;
; Helper function of prettyMoves
; from s1 --> s2
;
(defun detectDiff (s1 s2)
  (let* ((k1 (getKeeperPosition s1 0))
	 (k2 (getKeeperPosition s2 0))
	 (deltaX (- (car k2) (car k1)))
	 (deltaY (- (cadr k2) (cadr k1)))
	 )
    (cond ((= deltaX 0) (if (> deltaY 0) 'DOWN 'UP))
	  (t (if (> deltaX 0) 'RIGHT 'LEFT))
	  );end cond
    );end let
  );end defun

;
; Translates a list of states into a list of moves.
; Usage: (prettyMoves (a* <problem> #'goal-test #'next-states #'heuristic))
;
(defun prettyMoves (m)
  (cond ((null m) nil)
	((= 1 (length m)) (list 'END))
	(t (cons (detectDiff (car m) (cadr m)) (prettyMoves (cdr m))))
	);end cond
  );

;
; Print the content of the square to stdout.
;
(defun printSquare (s)
  (cond ((= s blank) (format t " "))
	((= s wall) (format t "#"))
	((= s box) (format t "$"))
	((= s keeper) (format t "@"))
	((= s star) (format t "."))
	((= s boxstar) (format t "*"))
	((= s keeperstar) (format t "+"))
	(t (format t "|"))
	);end cond
  )

;
; Print a row
;
(defun printRow (r)
  (dolist (cur r)
    (printSquare cur)
    )
  );

;
; Print a state
;
(defun printState (s)
  (progn
    (dolist (cur s)
      (printRow cur)
      (format t "~%")
      )
    );end progn
  )

;
; Print a list of states with delay.
;
(defun printStates (sl delay)
  (dolist (cur sl)
    (printState cur)
    (sleep delay)
    );end dolist
  );end defun
