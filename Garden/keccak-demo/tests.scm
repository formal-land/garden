;; Sanjay Adhith
;; Time-stamp: <2025-08-06 20:22:51 adhithsanjay>

;; Tests for keccak.scm

(define (test-bit? candidate)
  (and (let ([actual-result (candidate 0)]
	     [expected-result #t])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 1)]
	     [expected-result #t])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate "s")]
	     [expected-result #f])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate (list 1 2 3))]
	     [expected-result #f])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 1 2))]
	     [expected-result #f])
	 (equal? actual-result expected-result))))

(define (test-bit-xor candidate)
  (and (let ([actual-result (candidate 0 0)]
	     [expected-result 0])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 1 1)]
	     [expected-result 0])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 0 1)]
	     [expected-result 1])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 1 0)]
	     [expected-result 1])
	 (equal? actual-result expected-result))))

(define (test-zero-string candidate)
  (and (let ([actual-result (candidate 0)]
	     [expected-result (make-vector 0 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 1)]
	     [expected-result (make-vector 1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 2)]
	     [expected-result (make-vector 2 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 10)]
	     [expected-result (make-vector 10 0)])
	 (equal? actual-result expected-result))))
       
(define (test-zero-string candidate)
  (and (let ([actual-result (candidate 0)]
	     [expected-result (make-vector 0 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 1)]
	     [expected-result (make-vector 1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 2)]
	     [expected-result (make-vector 2 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 10)]
	     [expected-result (make-vector 10 0)])
	 (equal? actual-result expected-result))))

(define (test-len candidate)
  (and (let ([actual-result (candidate '#(1 0 1 0 0 0))]
	     [expected-result 6])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0))]
	     [expected-result 4])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0))]
	     [expected-result 1])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#())]
	     [expected-result 0])
	 (equal? actual-result expected-result))))

(define (test-ith candidate)
  (and (let ([actual-result (candidate '#(1 0 1 0 0 0) 2)]
	     [expected-result 1])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0) 2)]
	     [expected-result 0])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0) 0)]
	     [expected-result 0])
	 (equal? actual-result expected-result))))

(define (test-trunc candidate)
  (and (let ([actual-result (candidate 2 '#(1 0 1 0 0))]
	     [expected-result '#(1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 3 '#(1 0 1 0 0))]
	     [expected-result '#(1 0 1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 3 '#(1 1 1 1 0))]
	     [expected-result '#(1 1 1)])
	 (equal? actual-result expected-result))))

(define (test-string-XOR candidate)
  (and (let ([actual-result (candidate '#(0) '#(0))]
	     [expected-result '#(0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1) '#(1))]
	     [expected-result '#(0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1) '#(0))]
	     [expected-result '#(1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0) '#(1))]
	     [expected-result '#(1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1 1 0 0) '#(1 0 1 0))]
	     [expected-result '#(0 1 1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1 1 0 0) '#(1 0 1 1))]
	     [expected-result '#(0 1 1 1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1 1 1 1) '#(1 0 1 0))]
	     [expected-result '#(0 1 0 1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0) '#(1 0 1 0))]
	     [expected-result '#(1 0 1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0 0) '#(1 0 1 0 0))]
	     [expected-result '#(1 0 1 0 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0 0) '#(1 0 1 0 1))]
	     [expected-result '#(1 0 1 0 1)])
	 (equal? actual-result expected-result))
       ))

(define (test-string-concat candidate)
  (and (let ([actual-result (candidate '#(0) '#(0))]
	     [expected-result '#(0 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1) '#(1))]
	     [expected-result '#(1 1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1) '#(0))]
	     [expected-result '#(1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0) '#(1))]
	     [expected-result '#(0 1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1 1 0 0) '#(1 0 1 0))]
	     [expected-result '#(1 1 0 0 1 0 1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1 1 0 0) '#(1 0 1 1))]
	     [expected-result '#(1 1 0 0 1 0 1 1)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(1 1 1 1) '#(1 0 1 0))]
	     [expected-result '#(1 1 1 1 1 0 1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0) '#(1 0 1 0))]
	     [expected-result '#(0 0 0 0 1 0 1 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0 0) '#(1 0 1 0 0))]
	     [expected-result '#(0 0 0 0 0 1 0 1 0 0)])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate '#(0 0 0 0 0) '#(1 0 1 0 1))]
	     [expected-result '#(0 0 0 0 0 1 0 1 0 1)])
	 (equal? actual-result expected-result))))

(define (test-log_2 candidate)
  (and (let ([actual-result (candidate 32)]
	     [expected-result 5.0])
	 (equal? actual-result expected-result))
       (let ([actual-result (candidate 64)]
	     [expected-result 6.0])
         (equal? actual-result expected-result))))
