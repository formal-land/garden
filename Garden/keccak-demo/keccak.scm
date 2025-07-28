;; Sanjay Adhith
;; Time-stamp: <2025-07-28 23:01:21 adhithsanjay>

;; This is an implementation of the Keccak algorithm
;; as specified in:
;; https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf

(load "tests.scm")

(define (bit? a)
 (and (integer? a) (or (= a 0) (= a 1))))

(unless (test-bit? bit?)
  (errorf 'bit? "is-bit? has an error"))

(define (bit-xor a b)
  (cond [(not (bit? a))
	 (errorf 'a "not an integer a")]
	[(not (bit? b))
	 (errorf 'b "not an integer b")]
	[(= a b)
	 0]
	[else
	 1]))

(unless (test-bit-xor bit-xor)
  (errorf 'bit-xor "bit-xor has an error"))

;; "For a positive integer s, 0^s is the string that consists of s consecutive 0s.
;; If s=0, then 0^s is the empty string."

(define (zero-string s)
  (make-vector s 0))

(unless (test-zero-string zero-string)
  (errorf 'zero-string "zero-string has an error"))

;; "For a bit string X, len(X) is the length of X in bits."

(define (length x)
  (if (not (vector? x))
      (errorf 'x "not a vector x")
      (vector-length x)))

;; For a string X and an integer i such that 0 ≤ i < len(X), X[i] is the bit of X
;; with index i.
;; Bit strings are depicted with indices increasing from left to
;; right, so that X[0] appears at the left, followed by X[1], etc.
;; For example,
;; if X = 101000, then X[2] = 1.

(define (ith x i)
  (cond [(not (vector? x))
	 (errorf 'x "not a vector x")]
	[(not (integer? i))
	 (errorf 'i "not an integer i")]
	[(not (and (<= 0 i) (< i (length x))))
	 (errorf 'i "out of bounds i")]
	[else 
	 (vector-ref x i)]))

(unless (test-ith ith)
  (errorf 'ith "ith has an error"))

;; For a positive integer s and a string X,
;; Truncs (X) is the string comprised of
;; bits X[0] to X[s – 1].
;; For example, Trunc_2_(10100) = 10.

(define (trunc s x)
  (cond [(not (vector? x))
	 (errorf 'x "not a vector x")]
	[(not (integer? s))
	 (errorf 's "not an integer s")]
	[(not (and (< 0 s) (< s (length x))))
	 (errorf 's "out of bounds s")]
	[else 
	 (vector-copy x 0 s)]))

(unless (test-trunc trunc)
  (errorf 'trunc "trunc has an error"))

