module prime where

open import equality
open import int
open import gcd


data Prime : Int -> Set where
  prime : (p : Int) -> Pos p
          -> ((d : Int) -> Pos d -> (d div p) -> (d != p) -> (d == (int 1)))
          -> Prime p

data PrimeFactorization : Int -> Set where
  prime-factor-one : PrimeFactorization (int 1)
  prime-factor-prime : {m n : Int}
    -> (p : Prime m) 
    -> (f : PrimeFactorization n) 
    -> PrimeFactorization (m * n)


data PrimeRec : Int -> Set where
  prime-rec-zero : PrimeRec (int 0)
  prime-rec-neg : {n : Int} -> PrimeFactorization n -> PrimeRec (- n)
  prime-rec-pos : {n : Int} -> PrimeFactorization n -> PrimeRec n


-- exists-prime-factor : (n : Int) -> Factorization n
-- exists-prime-factor :

