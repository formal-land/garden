;; Copyright Consensys Software Inc.
;;
;; Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
;; the License. You may obtain a copy of the License at
;;
;; http://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
;; an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
;; specific language governing permissions and limitations under the License.
;;
;; SPDX-License-Identifier: Apache-2.0

(defpurefun (vanishes! (e0 :int)) (== e0 0))
(defpurefun ((force-bin :binary :force) x) x)
(defpurefun (is-binary (e0 :int)) (or! (== e0 0) (== e0 1)))
;; =============================================================================
;; Conditionals (DEPRECATED)
;; =============================================================================
(defpurefun (if-zero (cond :int) (then :any)) (if (== cond 0) then))
(defpurefun (if-zero (cond :int) (then :any) (else :any)) (if (== cond 0) then else))
(defpurefun (if-not-zero (cond :int) (then :any)) (if (!= cond 0) then))
(defpurefun (if-not-zero (cond :int) (then :any) (else :any)) (if (!= cond 0) then else))
(defpurefun (if-eq (x :int) (y :int) (then :any)) (if (eq! x y) then))
(defpurefun (if-eq-else (x :int) (y :int) (then :any) (else :any)) (if (eq! x y) then else))
(defpurefun (if-not-eq (x :int) (y :int) (then :any)) (if (!= x y) then))
(defpurefun (if-not-eq (x :int) (y :int) (then :any) (else :any)) (if (!= x y) then else))
(defpurefun (if-not (cond :bool) (then :any)) (if (not! cond) then))
(defpurefun (if-not (cond :bool) (then :any) (else :any)) (if (not! cond) then else))

;; =============================================================================
;; Boolean connectives (DEPRECATED)
;; =============================================================================
(defpurefun (or! (a :bool) (b :bool)) (∨ a b))
(defpurefun (or! (a :bool) (b :bool) (c :bool)) (∨ a b c))
(defpurefun (or! (a :bool) (b :bool) (c :bool) (d :bool)) (∨ a b c d))
(defpurefun (or! (a :bool) (b :bool) (c :bool) (d :bool) (e :bool)) (∨ a b c d e))
(defpurefun (or! (a :bool) (b :bool) (c :bool) (d :bool) (e :bool) (f :bool)) (∨ a b c d e f))
(defpurefun (and! (a :bool) (b :bool)) (∧ a b))
(defpurefun (and! (a :bool) (b :bool) (c :bool)) (∧ a b c))
(defpurefun (and! (a :bool) (b :bool) (c :bool) (d :bool)) (∧ a b c d))
(defpurefun (and! (a :bool) (b :bool) (c :bool) (d :bool) (e :bool)) (∧ a b c d e))
(defpurefun (and! (a :bool) (b :bool) (c :bool) (d :bool) (e :bool) (f :bool)) (∧ a b c d e f))
(defpurefun ((eq! :bool) (x :int) (y :int)) (== x y))
(defpurefun ((neq! :bool) (x :int) (y :int)) (!= x y))
(defpurefun ((not! :bool) (x :bool)) (if x (!= 0 0) (== 0 0)))
(defpurefun ((is-not-zero! :bool) (x :int)) (!= x 0))

;; =============================================================================
;; Chronological functions
;; =============================================================================
(defpurefun (next (X :any)) (shift X 1))
(defpurefun (prev (X :any)) (shift X -1))
;; Ensure e0 has increased by offset w.r.t previous row.
(defpurefun ((did-inc! :bool) (e0 :int) (offset :int)) (== e0 (+ (prev e0) offset)))
;; Ensure e0 has decreased by offset w.r.t previous row.
(defpurefun ((did-dec! :bool) (e0 :int) (offset :int)) (== e0 (- (prev e0) offset)))
;; Ensure e0 will increase by offset w.r.t next row.
(defpurefun ((will-inc! :bool) (e0 :int) (offset :int)) (will-eq! e0 (+ e0 offset)))
;; Ensure e0 will decrease by offset w.r.t next row.
(defpurefun ((will-dec! :bool) (e0 :int) (offset :int)) (== (next e0) (- e0 offset)))
;; Ensure e0 remained constant w.r.t previous row.
(defpurefun ((remained-constant! :bool) (e0 :int)) (== e0 (prev e0)))
;; Ensure e0 will remain constant w.r.t next row.
(defpurefun ((will-remain-constant! :bool) (e0 :int)) (will-eq! e0 e0))
;; Ensure e0 has changed its value w.r.t previous row.
(defpurefun ((did-change! :bool) (e0 :int)) (!= e0 (prev e0)))
;; Ensure e0 will remain constant w.r.t next row.
(defpurefun ((will-change! :bool) (e0 :int)) (will-neq! e0 e0))
;; Ensure e1 equals value of e0 in previous row.
(defpurefun ((was-eq! :bool) (e0 :int) (e1 :int)) (== (prev e0) e1))
;; Ensure e1 will equal value of e0 in next row.
(defpurefun ((will-eq! :bool) (e0 :int) (e1 :int)) (== (next e0) e1))
;; Ensure e1 will not equal value of e0 in next row.
(defpurefun ((will-neq! :bool) (e0 :int) (e1 :int)) (!= (next e0) e1))
;; SHOULD BE DEPRECATED
(defpurefun ((remained-constant :int) (e0 :int)) (- e0 (prev e0)))
;; =============================================================================
;; Helpers
;; =============================================================================

;; counter constancy constraint
(defpurefun (counter-constancy (ct :int) (X :int))
  (if (!= ct 0)
               (remained-constant! X)))

;; perspective constancy constraint
(defpurefun (perspective-constancy (PERSPECTIVE_SELECTOR :int) (X :int))
            (if (!= (* PERSPECTIVE_SELECTOR (prev PERSPECTIVE_SELECTOR)) 0)
                         (remained-constant! X)))

;; base-X decomposition constraints
(defpurefun ((base-X-decomposition :bool) (ct :int) (base :int) (acc :int) (digits :int))
  (if (== ct 0)
           (== acc digits)
           (== acc (+ (* base (prev acc)) digits))))

;; byte decomposition constraint
(defpurefun (byte-decomposition (ct :int) (acc :int) (bytes :int)) (base-X-decomposition ct 256 acc bytes))

;; bit decomposition constraint
(defpurefun (bit-decomposition (ct :int) (acc :int) (bits :int)) (base-X-decomposition ct 2 acc bits))

;; plateau constraints
(defpurefun (plateau-constraint (CT :int) (X :binary) (C :int))
            (begin (debug (stamp-constancy CT C))
                   (if (== C 0)
                            (== X 1)
                            (if (== CT 0)
                                (vanishes! X)
                              (if (== CT C)
                                  (did-inc! X 1)
                                (remained-constant! X))))))

;; stamp constancy imposes that the column C may only
;; change at rows where the STAMP column changes.
(defpurefun (stamp-constancy (STAMP :int) (C :int))
            (if (will-remain-constant! STAMP)
                (will-remain-constant! C)))
