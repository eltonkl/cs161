; generate-unassigned-values len
; Generates a list of len numbers, all initialized to 0 (the constant indicating that the value is unassigned)
(defun generate-unassigned-values (len)
    (cond
        ((= len 0) nil)
        (t (cons 0 (generate-unassigned-values (- len 1))))
    )
)

; sat? n delta
; returns a list of n integers, representing a model of delta, if delta is satisfiable, otherwise it returns nil
(defun sat? (n delta)
    (sat?-helper n delta (generate-unassigned-values n))
)

; Constants:
; -1: False
; 0: Not defined yet
; 1: True

; sign x
; Returns -1 if x < 0
; Returns 1 if x > 0
; Trust callers to not provide 0 to the function
(defun sign (x)
    (cond
        ((< x 0) -1)
        ((> x 0) 1)
    )
)

; absv x
; Returns absolute value of x
(defun absv (x)
    (cond
        ((< x 0) (* -1 x))
        (t x)
    )
)

; neq x y
; Returns t if x and y are not equal to each other
(defun neq (x y)
    (not (= x y))
)

; values list: the (1-indexed) list of assignments of constants (as defined above)
; E.g. (1 -1 0) indicates that 1 is assigned true, 2 is assigned false, and 3 is not assigned yet

; get-value values n
; Get nth value from the values list
(defun get-value (values n)
    (car (nthcdr (- n 1) values))
)

; set-value values n value
; Sets nth value of the values list to value
(defun set-value (values n value)
    (let*
        (
            (front-values (butlast values (- (length values) (- n 1)))) ; Values in front of the desired value
            (back-values (cdr (nthcdr (- n 1) values))) ; Values behind the desired value
        )
        (append front-values (list value) back-values) ; Create new values list
    )
)

; satisfies-clause clause n value
; Returns t if the given value for the given n satisfies the given clause
(defun satisfies-clause (clause n value)
    (cond
        ((null clause) nil)
        ((and (= (abs (car clause)) n) (= (sign (car clause)) value) t))
        (t (satisfies-clause (cdr clause) n value))
    )
)

; remove-n clause n
; Removes all mentions of the nth variable from the clause
(defun remove-n (clause n)
    (cond
        ((null clause) nil)
        ((= (abs (car clause)) n) (remove-n (cdr clause) n))
        (t (cons (car clause) (remove-n (cdr clause) n)))
    )
)

; reduce-clause clause n value
; If clause is satisfied by given value for n, return nil
; If clause isn't satisfied by the given value for n, return the clause with all mentions of variable n removed
(defun reduce-clause (clause n value)
    (cond
        ((satisfies-clause clause n value) nil)
        (t (remove-n clause n))
    )
)

; reduce-clauses n value
; If the given value for the given n satisfies a clause in clauses, remove it from the clauses list
; Otherwise, if there are mentions of n in a given clause in clauses, remove the mention of n from the clause
; Otherwise do nothing to the clause
(defun reduce-clauses (clauses n value)
    (cond
        ((null clauses) nil)
        (t
            (let
                ((reduced (reduce-clause (car clauses) n value)))
                (cond
                    ((null reduced) (reduce-clauses (cdr clauses) n value))
                    (t (cons reduced (reduce-clauses (cdr clauses) n value)))
                )
            )
        )
    )
)

; new-value-contradicts clauses n value
; returns t if the given value for n contradicts renders the clauses unsatisfiable
(defun new-value-contradicts (clauses n value)
    (cond
        ((null clauses) nil)
        ((and (= 1 (length (car clauses))) (= n (absv (caar clauses))) (neq (sign (caar clauses)) value)) t)
        (t (new-value-contradicts (cdr clauses) n value))
    )
)

; unit-resolution-helper seen left values
; Helps perform unit resolution
(defun unit-resolution-helper (seen left values)
    (cond
        ((null left) (list seen values))
        ((> (length (car left)) 1) (unit-resolution-helper (append seen (list (car left))) (cdr left) values)) ; Append head of left into seen, and recursively call helper with the rest of left
        (
            (= (length (car left)) 1)
            (let
                (
                    (index (absv (caar left))) ; Index of the unit clause's variable, which is also the name and number of the variable itself
                    (value-from-unit-clause (sign (caar left))) ; Constant value
                )
                (cond
                    ; this isn't needed ((and (neq (get-value values index) 0) (neq (get-value values index) value-from-unit-clause)) nil) ; If this is a unit clause, return false if there is a contradiction with a pre-existing value
                    ((new-value-contradicts (append seen left) index value-from-unit-clause) nil) ; If the value from the unit clause causes a contradiction, return false
                    (t (unit-resolution-helper nil (reduce-clauses (append seen left) index value-from-unit-clause) (set-value values index value-from-unit-clause)))
                    ; ^ Otherwise perform unit-resolution again after following the strategy described for reduce-clauses and fixing the value for index in values
                )
            )
        )
    )
)

; unit-resolution n delta
; Performs unit resolution
(defun unit-resolution (n delta values)
    (unit-resolution-helper nil delta values)
)

; convert-to-result variables start n
; Start should be 1 when this function is called the first time
; converts the given values list to the expected format for sat?
(defun convert-to-result (variables start n)
    (cond
        ((> start n) variables)
        (t (convert-to-result (set-value variables start (* (get-value variables start) start)) (+ start 1) n))
    )
)

; assign-true-to-undefined-variables values
; For values list values, assigns true to undefined variables
(defun assign-true-to-undefined-variables (values)
    (cond
        ((null values) nil)
        ((= (car values) 0) (cons 1 (assign-true-to-undefined-variables (cdr values))))
        (t (cons (car values) (assign-true-to-undefined-variables (cdr values))))
    )
)

; count-pure delta pures
; Update pures list according to the clause: the n'th item in pures is 0 if not found yet, nil if not pure, 1 if still positive pure, -1 if still negative pure
(defun count-pure (clause pures)
    (cond
        ((null clause) pures)
        (t
            (let*
                (
                    (cur-value (car clause))
                    (cur-index (absv cur-value))
                    (cur-sign (sign cur-value))
                    (prev-value (get-value pures cur-index))
                    (new-value (cond ((null prev-value) nil) ((eq 0 prev-value) cur-sign) ((eq prev-value cur-sign) prev-value) (t nil)))
                )
                (count-pure (cdr clause) (set-value pures cur-index new-value))
            )
        )
    )
)

; count-pures delta pures
; Update pures list: the n'th item in pures is 0 if not found yet, nil if not pure, 1 if all positive pure, -1 if all negative pure
(defun count-pures (delta pures)
    (cond
        ((null delta) pures)
        ((count-pures (cdr delta) (count-pure (car delta) pures)))
    )
)

; eliminate-pures delta values n start pures
; For the start'th variable, if it is pure, then assign it in values and then remove all clauses that have the pure variable
(defun eliminate-pures (delta values n start pures)
    (cond
        ((> start n) (list delta values))
        ((let*
            ((cur-pure (get-value pures start)))
            (cond
                ((or (eq 1 cur-pure) (eq -1 cur-pure)) (eliminate-pures (reduce-clauses delta start cur-pure) (set-value values start cur-pure) n (+ start 1) pures))
                ((eliminate-pures delta values n (+ start 1) pures))
            )
        ))
    )
)

; pure-literal delta n values
; Perform pure-literal elimination
(defun pure-literal (delta n values)
    (cond
        ((and (null delta) (null values)) nil) ; this is directly fed output of ur, so if both ur outputs are nil, return nil
        ((eliminate-pures delta values n 1 (count-pures delta (generate-unassigned-values n))))
    )
)

; Implentation of heuristic: find the variable that appears the most times in all of the clauses
; Slower for small CNFs, but faster for a lot of unsatisfiable CNFs

; count-clause clause counts
; Update counts list to have each n'th item be incremented by a count of how many times the n'th item appears in the clause
(defun count-clause (clause counts)
    (cond
        ((null clause) counts)
        ((count-clause (cdr clause) (set-value counts (absv (car clause)) (+ (get-value counts (absv (car clause))) 1))))
    )
)

; count-clauses delta counts
; Update counts list: the n'th item in counts is the count of how many times n appears in delta
(defun count-clauses (delta counts)
    (cond
        ((null delta) counts)
        ((count-clauses (cdr delta) (count-clause (car delta) counts)))
    )
)

; get-most-common-variable-from-counts
; Gets the index of the most common variable from the counts list
(defun get-most-common-variable-from-counts (n cur-index max-index max counts)
    (cond
        ((> cur-index n) max-index)
        (
            (let
                ((cur (get-value counts cur-index)))
                (cond
                    ((> cur max) (get-most-common-value-from-counts n (+ 1 cur-index) cur-index cur counts))
                    ((get-most-common-variable-from-counts n (+ 1 cur-index) max-index max counts))
                )
            )
        )
    )
)

; most-common-variable n delta
; For delta, returns the index of the most common variable
(defun most-common-variable (n delta)
    (get-most-common-variable-from-counts n 1 0 0 (count-clauses delta (generate-unassigned-values n)))
)

; heuristic-index-of-undefined-variable
; Uses the above functions as the heuristic
(defun heuristic-index-of-undefined-variable (start n delta counts)
    (most-common-variable n delta)
)

; sat?-helper n delta values
; Perform unit resolution
; Then DFS backtracking
(defun sat?-helper (n delta values)
    (let*
        (
            ; Perform unit resolution
            (ur-result (unit-resolution n delta values))
            (ur-delta (car ur-result))
            (ur-values (cadr ur-result))
            ; Perform pure literal elimination
            (pl-result (pure-literal ur-delta n ur-values))
            (pl-delta (car pl-result))
            (pl-values (cadr pl-result))
        )
        (cond
            ((null pl-result) nil) ; unit resolution determined that the CNF is unsatisfiable
            ((null pl-delta) (convert-to-result (assign-true-to-undefined-variables pl-values) 1 n))
            (
                (let* ; Back-tracking DFS
                    (
                        (index-of-variable-to-set (heuristic-index-of-undefined-variable 1 n pl-delta pl-values))
                    )
                    (cond
                        (
                            (let* ; DFS set positive
                                (
                                    (new-delta-true (set-value pl-values index-of-variable-to-set 1))
                                    (cant-use-true (new-value-contradicts pl-delta n new-delta-true))
                                )
                                (cond
                                    (cant-use-true nil)
                                    (t (sat?-helper n (reduce-clauses pl-delta index-of-variable-to-set 1) new-delta-true))
                                )
                            )
                        )
                        (
                            (let* ; DFS set negative
                                (
                                    (new-delta-false (set-value pl-values index-of-variable-to-set -1))
                                    (cant-use-false (new-value-contradicts pl-delta n new-delta-false))
                                )
                                (cond
                                    (cant-use-false nil)
                                    (t (sat?-helper n (reduce-clauses pl-delta index-of-variable-to-set -1) new-delta-false))
                                )
                            )
                        )
                    )
                )
            )
            (t nil) ; DFS doesn't find a solution, so this is unsatisfiable
        )
    )
)