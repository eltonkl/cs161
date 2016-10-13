; DFS tree
; Implementation of left to right depth first search:
; Base case: tree is null: return nil
; tree's head is an atom: Make it head of a list, with the tail being the result of a recursive call of DFS on the rest of the tree
; tree's head is a list: Use DFS recursively on the list, and append to that result DFS on the rest of the tree
(defun DFS (tree)
    (cond
        ((null tree) nil)
        ((atom (first tree)) (cons (first tree) (DFS (rest tree))))
        ((listp (first tree)) (append (DFS (first tree)) (DFS (rest tree))))))

; DFID tree maxdepth
; Depth-first iterative-deepening search
; Call DFSID with a starting depth of 1 - the root node has no value, so traversing it won't result in anything
(defun DFID (tree maxdepth)
    (DFSID tree 1 maxdepth))

; DFSID tree depth maxdepth
; Depth first search - iteratively deepning
; Helper function for DFID - performs a depth first search at the given depth n
;   and then appends to that the result of DFSID with depth n + 1
; Stops after performing a DFS with depth == maxdepth
(defun DFSID (tree depth maxdepth)
    (cond
        ((< depth maxdepth) (append (DFSD tree depth) (DFSID tree (+ depth 1) maxdepth)))
        ((= depth maxdepth) (DFSD tree maxdepth))
        (t nil)))

; DFSD tree depth
; Depth first search (up to) depth n
; Base cases: depth of 0: nil
;             depth of 1: only put in result list those nodes that are leaves of the root node
; Depth of n: Append result of DFSD on the head of tree with depth (n - 1) to result of DFSD
;             on the tail of the tree with depth (n - 1)
(defun DFSD (tree depth)
    (cond
        ((= depth 0) nil)
        ((= depth 1)
            (cond
                ((null tree) nil)
                ((atom (first tree)) (cons (first tree) (DFSD (rest tree) 1)))
                ((listp (first tree)) (DFSD (rest tree) 1))))
        (t
            (cond
                ((null tree) nil)
                (t
                    (append
                        (cond
                            ((atom (first tree)) (list (first tree))) ; Skip calling DFSD with depth n - 1
                                                                      ; Prevents a lot of unnecessary recursion
                            ((listp (first tree)) (DFSD (first tree) (- depth 1))))
                        (DFSD (rest tree) depth)))))))

; These functions implement a depth-first iterative-deepening solver for the
; missionary-cannibal problem. In this problem, three missionaries and three
; cannibals are trying to go from the east side of a river to the west side.
; They have a single boat that can carry two people at a time from one side of
; the river to the other. There must be at least one person in the boat to cross
; the river. There can never be more cannibals on one side of the river than
; missionaries. If there are, the cannibals eat the missionaries.

; In this implementation, a state is represented by a single list (MISSIONARIES
; CANNIBALS SIDE). SIDE represents which side the boat is currently on, and is T
; if it is on the east side and NIL if on the west side. MISSIONARIES and
; CANNIBALS represent the number of missionaries and cannibals on the same side
; as the boat. Thus, the initial state for this problem is (3 3 T) (three
; missionaries, three cannibals, and the boat are all on the east side of the
; river) and the goal state is (3 3 NIL).

; The main entry point for this solver is the function ID-DFS, which is called
; with the initial state to search from and the depth up to which depth-first
; search will be performed. It returns the complete path from the initial state
; to the goal state: this path is a list of intermediate problem states. The
; first element of the path is the initial state and the last element is the
; goal state. Each intermediate state is the state that results from applying


; the appropriate operator to the preceding state.

; To solve the original problem, one would call (ID-DFS '(3 3 T) 0). 

; Examples of calls to some of the helper functions can be found after the code.


; FINAL-STATE takes a single argument (S), the current state, and returns T if
; it is the goal state (3 3 NIL) and NIL otherwise.
(defun final-state (s)
    (cond
        ((equal s '(3 3 nil)) t)
        (t nil)))

; NEXT-STATE returns the state that results from applying an operator to the
; current state. It takes three arguments: the current state (S), a number of
; missionaries to move (M), and a number of cannibals to move (C). It returns a
; list containing the state that results from moving that number of missionaries
; and cannibals from the current side of the river to the other side of the
; river. If applying this operator results in an invalid state (because there
; are more cannibals than missionaries on either side of the river, or because
; it would move more missionaries or cannibals than are on this side of the
; river) it returns NIL.
;
; NOTE that next-state returns a list containing the successor state (which is
; itself a list); the return should look something like ((1 1 T)).
(defun next-state (s m c)
    (let*
        (
            (total (+ m c))
            (start-side-m (- (first s) m))
            (start-side-c (- (second s) c))
            (end-side-m (- 3 start-side-m))
            (end-side-c (- 3 start-side-c)))
        (cond
            ((null s) nil)
            ((> total 2) nil) ; More than two people trying to cross
            ((= total 0) nil) ; No people trying to cross
            ((or (< start-side-m 0) (< start-side-c 0)) nil) ; Negative amount of people on start side
            ((and (< start-side-m start-side-c) (> start-side-m 0)) nil) ; Less missionaries than cannibals on start side (and at least one missionary to be eaten)
            ((and (< end-side-m end-side-c) (> end-side-m 0)) nil) ; Less missionaries than cannibals on end side (and at least one missionary to be eaten)
            (t (list (list end-side-m end-side-c (not (third s))))))))

; SUCC-FN returns all of the possible legal successor states to the current
; state. It takes a single argument (S), which encodes the current state, and
; returns a list of states that can be reached by applying legal operators to
; the current state.
(defun succ-fn (s)
    (append
        (next-state s 0 1) ; The five possible valid moves: > 0 and < 3 people moving
        (next-state s 1 0)
        (next-state s 1 1)
        (next-state s 2 0)
        (next-state s 0 2)))

; MULT-DFS is a helper function for SINGLE-DFS. It takes three arguments: the
; path from the initial state to the current state (PATH), the legal successor
; states to the last state on PATH (STATES), and the depth (DEPTH). PATH is a
; first-in first-out list of states; that is, the first element is the initial
; state for the current search and the last element is the most recent state
; explored. MULT-DFS does a single depth-first iteration to the given depth on
; each element of STATES in turn. If any of those searches reaches the final
; state, MULT-DFS returns the complete path from the initial state to the goal
; state. Otherwise, it returns NIL.
(defun mult-dfs (states path depth)
    (cond
        ((null states) nil)
        ((= depth 0) ; Verify that a "leaf" node is the final state
            (cond
                ((final-state (first states)) (append path (list (first states)))) ; Check head
                (t (mult-dfs (rest states) path depth)))) ; Check tail
        (t (let*
                ((cur-state (first states)))
                (cond
                    ((final-state cur-state) (append path (list (cur-state)))) ; Short circuit checking if the state is the final state
                    (t (let*
                            (
                                (successors (succ-fn cur-state)) ; Increase tree depth by 1, so depth must be decreased for next mult-dfs call
                                (cur-result (mult-dfs successors (append path (list cur-state)) (- depth 1))))
                            (cond
                                (cur-result cur-result)
                                (t (mult-dfs (rest states) path depth)))))))))) ; Evaluate other successor states

; SINGLE-DFS does a single depth-first iteration to the given depth. It takes
; three arguments: a state (S), the path from the initial state to S (PATH), and
; the depth (DEPTH). If S is the initial state in our search, PATH should be
; NIL. It performs a depth-first search starting at the given state. It returns
; the path from the initial state to the goal state, if any, or NIL otherwise.
(defun single-dfs (s path depth)
    (cond
        ((= depth 0) (cond ((final-state s) (list s))))
        (t (mult-dfs (succ-fn s) (append path (list s)) (- depth 1)))))

; ID-DFS is the top-level function. It takes two arguments: an initial state (S)
; and a search depth (DEPTH). ID-DFS performs a series of depth-first
; iterations, starting from the given depth until a solution is found. It
; returns the path from the initial state to the goal state. The very first call
; to ID-DFS should use depth = 0.
(defun id-dfs (s depth)
    (let ((result (single-dfs s nil depth)))
         (cond
            (result result)
            (t (id-dfs s (+ depth 1)))))) ; If result isn't found, increase depth

; Function execution examples

; Applying this operator would result in an invalid state, with more cannibals
; than missionaries on the east side of the river.
; (next-state '(3 3 t) 1 0) -> NIL

; Applying this operator would result in one cannibal and zero missionaries on
; the west side of the river, which is a legal operator. (note that NEXT-STATE
; returns a LIST of successor states, even when there is only one successor)
; (next-state '(3 3 t) 0 1) -> ((0 1 NIL))

; SUCC-FN returns all of the legal states that can result from applying
; operators to the current state.
; (succ-fn '(3 3 t)) -> ((0 1 NIL) (1 1 NIL) (0 2 NIL))
; (succ-fn '(1 1 t)) -> ((3 2 NIL) (3 3 NIL))
