module prime where

open import equality
open import int
open import abs
open import nat
open import div

data PrimeUpTo : Nat -> Nat -> Set where
  prime-up-to : (p : Nat) -> (bound : Nat)
                -> ((d : Nat) -> d ≤' bound -> (d div' p) -> (d != 0) -> (d != 1) -> d == p)
                -> PrimeUpTo p bound

data Prime' : Nat -> Set where
  prime' : (p : Nat) 
          -> ((d : Nat) -> d ≤' p -> (d div' p) -> (d != 0) -> (d != 1) -> d == p)
          -> Prime' p

data Prime : Int -> Set where
  prime : (p : Int) -> Pos p
          -> ((d : Int) -> Pos d -> (d div p) -> (d != (int 1)) -> (d == p))
          -> Prime p

prime-up-to->prime' : {n : Nat} -> PrimeUpTo n n -> Prime' n
prime-up-to->prime' (prime-up-to p p f) = (prime' p f)

prime'->prime : {p : Nat} -> Prime' p -> {Pos (int p)} -> Prime (int p)
prime'->prime (prime' p f) {pos-p} = (prime (int p) pos-p g)
  where
  g : (d : Int) -> Pos d -> (d div (int p)) -> (d != (int 1)) -> (d == (int p))
  g (pos d') pos-d d-div-p not-1 = (cong int (f (suc d') nat-≤ d-div-p' nat-d-not-0 nat-d-not-1))
    where
    nat-≤-base : (suc d') ≤' abs' (int p)
    nat-≤-base = div-abs-≤ {pos d'} {int p} {pos-d} {pos-p} d-div-p
    nat-≤ : (suc d') ≤' p
    nat-≤ rewrite (sym (abs'-int-id {p})) = nat-≤-base
    nat-d-not-0 : (suc d') != 0
    nat-d-not-0 ()
    nat-d-not-1 : (suc d') != 1
    nat-d-not-1 pr = not-1 (cong int pr)
    d-div-p'-base : (suc d') div' abs' (int p)
    d-div-p'-base = div->div' {pos d'} {int p} d-div-p
    d-div-p' : (suc d') div' p
    d-div-p' rewrite (sym (abs'-int-id {p})) = d-div-p'-base
  

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

data StrongRec : Nat -> Set where
  strong-rec-zero : StrongRec zero
  strong-rec-suc : {m : Nat} -> ({n : Nat} -> n ≤' m -> StrongRec m) -> StrongRec (suc m)



-- factorize : {n : Int} -> (Pos n) -> PrimeFactorization n
-- factorize 

