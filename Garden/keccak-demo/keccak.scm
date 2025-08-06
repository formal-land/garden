;; Formal Land
;; Time-stamp: <2025-08-06 20:20:31 adhithsanjay>

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

;; For a positive integer s, 0^s is the string that consists of s consecutive 0s.
;; If s=0, then 0^s is the empty string.

(define (zero-string s)
  (make-vector s 0))

(unless (test-zero-string zero-string)
  (errorf 'zero-string "zero-string has an error"))

;; For a bit string X, len(X) is the length of X in bits.

(define (len x)
  (if (not (vector? x))
      (errorf 'x "not a vector x")
      (vector-length x)))

(unless (test-len len)
  (errorf 'len "len has an error"))

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
	[(not (and (<= 0 i) (< i (len x))))
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
	[(not (and (< 0 s) (< s (len x))))
	 (errorf 's "out of bounds s")]
	[else 
	 (vector-copy x 0 s)]))

(unless (test-trunc trunc)
  (errorf 'trunc "trunc has an error"))

;; For strings X and Y of equal bit length, X XOR Y
;; is the string that results from applying the Boolean
;; exclusive-OR operation to X and Y at each bit position.
;; For example, 1100 XOR 1010 = 0110.

(define (string-XOR x y)
  (cond [(not (vector? x))
	 (errorf 'x "not a vector x")]
	[(not (vector? y))
	 (errorf 'y "not a vector y")]
	[(not (= (len x) (len y)))
	 (errorf '"x and y" "not strings of equal length")]
	[(vector-map bit-xor x y)]))

(unless (test-string-XOR string-XOR)
  (errorf 'string-XOR "string-XOR has an error"))

;; For strings X and Y, X || Y is the concatenation of X and Y.
;; For example, 11001 || 010 = 11001010.

(define (string-concat x y)
  (cond [(not (vector? x))
	 (errorf 'x "not a vector x")]
	[(not (vector? y))
	 (errorf 'y "not a vector y")]
	[(list->vector
	  (append (vector->list x) (vector->list y)))]))

(unless (test-string-concat string-concat)
  (errorf 'string-concat "string-concat has an error"))

;; For integers m and n, m/n is the quotient, i.e., m divided by n.

;; Here we use the quotient function in Scheme.
;; Example:
;; (quotient 15 4)
;; => 3

;; For integers m and n, m mod n is the integer r for which 0 ≤ r < n
;; and m - r is a multiple of n. For example, 11 mod 5 = 1, and
;; -11 mod 5 = 4.

;; Here we use the mod function in Scheme.
;; Example:
;; (mod -11 5)
;; => 4

;; For a real number x, ceil(x) is the least integer that is not
;; strictly less than x.

;; Here we use the ceiling function in Scheme.
;; Example:
;; (ceiling -3.3)
;; => -3.0

;; For a positive real number x, log_2(x) is the real number y such
;; that 2^y = x.

(define (log_2 x)
  (cond [(not (and (number? x) (> 0)))
	 (errorf 'x "not a positive number x")]
	[(/ (log x) (log 2))]))

;; For real numbers x and y, min(x, y) is the minimum of x and y. For
;; example, min(9, 33) = 9.

;; Here we use the min function in Scheme.
;; Example:
;; (min 9 33)
;; => 9
