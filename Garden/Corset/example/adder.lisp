;; This example describes a function "f(ARG_1,ARG_2) == RES" which
;; adds the two inputs together, producing a result which holds under
;; modulo arithmetic.  The following functional property should hold
;; for any two rows i,j:
;;
;; forall i,j :: (ST[i] != 0 && ST[j] != 0 && ARG_1[i] == ARG_1[j]
;;                && ARG_2[i] == ARG_2[j]) ==> RES[i] == RES[j]
;;
;; That is, for any two rows outside the padding region with matching
;; inputs, the output must also match.

(defcolumns
  (ST :i32)
  (CT :i4)
  (CT_MAX :i3)
  (BYTE_1 :i8@prove)
  (BYTE_2 :i8@prove)
  (BYTE_R :i8@prove)
  (ACC_1 :i64)
  (ACC_2 :i64)
  (ACC_R :i65)
  ;; Inputs
  (ARG_1 :i64)
  (ARG_2 :i64)
  ;; Outputs
  (RES :i65))

;; LLARGE determines the maximum number of rows in a frame.  In this
;; case, we are adding 64bit numbers which ensures the output fits
;; within 65bits.
(defconst LLARGE 8)

;; ===================================================================
;; Control Flow
;; ===================================================================

;; In the first row, ST is always zero.  This allows for an
;; arbitrary amount of padding at the beginning which has no function.
(defconstraint first (:domain {0}) (eq! ST 0))

;; In the last row of a valid frame, the counter must have its max
;; value.  This ensures that all non-padding frames are complete.
(defconstraint last (:domain {-1} :guard ST)
  ;; CT[$] == CT_MAX
  (eq! CT CT_MAX))

;; ST either remains constant, or increments by one.
(defconstraint increment ()
  (or!
   ;; ST[k] == ST[k+1]
   (eq! ST (shift ST 1))
   ;; Or, ST[k]+1 == ST[k+1]
   (eq! (+ 1 ST) (next ST))))

(defconstraint upper-bound ()
  (neq! LLARGE CT))

;; If ST changes, counter resets to zero.
(defconstraint reset ()
  (or!
   ;; ST[k] == ST[k+1]
   (eq! ST (shift ST 1))
   ;; Or, CT[k+1] == 0
   (eq! (next CT) 0)))

;; Increment or reset counter
(defconstraint heartbeat (:guard ST)
  ;; If CT[k] == CT_MAX
  (if-eq-else CT CT_MAX
              ;; Then, ST[k]+1 = ST[k+1]
              (eq! (next ST) (+ 1 ST))
              ;; Else, CT[k]+1 == CT[k+1]
              (eq! (+ 1 CT) (next CT))))

;; This should always be true for CT.
(defproperty ct-bound (or! (== ST 0) (<= CT CT_MAX)))

;; ===================================================================
;; Decompositions & Constancies
;; ===================================================================

;; ACC_1 (resp. ACC_2) are decomposed using upto 16 individual bytes
;; helds in BYTE_1 (resp. BYTE_2).
(defconstraint byte_decompositions ()
  (begin (byte-decomposition CT ACC_1 BYTE_1)
         (byte-decomposition CT ACC_2 BYTE_2)
         (byte-decomposition CT ACC_R BYTE_R)))

;; Determine which rows are constant with respect to the counter.
(defconstraint counter-constancies ()
  (begin (counter-constancy CT ARG_1)
         (counter-constancy CT ARG_2)
         (counter-constancy CT RES)
         (counter-constancy CT CT_MAX)))

;; ===================================================================
;; Target Constraints
;; ===================================================================

(defconstraint target-constraints (:guard ST)
  (if-eq CT CT_MAX
         (begin
          ;; ACC_1 proves ARG_1 is small
          (eq! ARG_1 ACC_1)
          ;; ACC_2 proves ARG_2 is small
          (eq! ARG_2 ACC_2)
          ;; ACC_R proves RES is small
          (eq! RES ACC_R))))

;; ===================================================================
;; Add Logic
;; ===================================================================

(defconstraint adder (:guard ST)
  (eq! RES (+ ARG_1 ARG_2)))
