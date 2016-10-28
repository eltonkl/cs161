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

; Helper for testing
; remove when done
(defun test-unit-resolution (n delta)
    (unit-resolution n delta (generate-unassigned-values n))
)

; convert-to-result values start n
; Start should be 1 when this function is called the first time
; converts the given values list to the expected format for sat?
(defun convert-to-result (values start n)
    (cond
        ((> start n) values)
        (t (convert-to-result (set-value values start (* (get-value values start) start)) (+ start 1) n))
    )
)

; assign-true-to-undefined-values values
; For values list values, assigns true to undefined values
(defun assign-true-to-undefined-values (values)
    (cond
        ((null values) nil)
        ((= (car values) 0) (cons 1 (assign-true-to-undefined-values (cdr values))))
        (t (cons (car values) (assign-true-to-undefined-values (cdr values))))
    )
)

; Can delta be defined and all values set? I hope not
; heuristic-index-of-undefined-value n delta values
; My function names are almost self explanatory for this assignment
; Bad heuristic: Find first unset value
(defun heuristic-index-of-undefined-value (start n delta values)
    (cond
        ((= (get-value values start) 0) start)
        (t (heuristic-index-of-undefined-value (+ start 1) n delta values))
    )
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
        )
        (cond
            ((null ur-result) nil)
            ((null ur-delta) (convert-to-result (assign-true-to-undefined-values ur-values) 1 n))
            (
                (let* ; Back-tracking DFS
                    (
                        (index-of-value-to-set (heuristic-index-of-undefined-value 1 n ur-delta ur-values))
                    )
                    (cond
                        (
                            (let* ; DFS set positive
                                (
                                    (new-delta-true (set-value ur-values index-of-value-to-set 1))
                                    (cant-use-true (new-value-contradicts ur-delta n new-delta-true))
                                )
                                (cond
                                    (cant-use-true nil)
                                    (t (sat?-helper n (reduce-clauses ur-delta index-of-value-to-set 1) new-delta-true))
                                )
                            )
                        )
                        (
                            (let* ; DFS set negative
                                (
                                    (new-delta-false (set-value ur-values index-of-value-to-set -1))
                                    (cant-use-false (new-value-contradicts ur-delta n new-delta-false))
                                )
                                (cond
                                    (cant-use-false nil)
                                    (t (sat?-helper n (reduce-clauses ur-delta index-of-value-to-set -1) new-delta-false))
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