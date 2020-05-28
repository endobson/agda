{-# OPTIONS --cubical --safe --exact-split #-}

module prime where

open import base
open import equality
open import int
open import abs
open import nat
open import div
open import relation
open import functions
open import unordered-list
open import ring
open import commutative-monoid

module NatSemiring = Semiring NatSemiring
open NatSemiring using (unordered-product; unordered-productʰ)

data IsPrime' : Nat -> Set where
  is-prime' : (p' : Nat)
              -> ((d : Nat) -> d <s (suc (suc p')) -> (d div' (suc (suc p'))) -> d == 1)
              -> IsPrime' (suc (suc p'))

record Prime' : Set where
  field
    value : Nat
    proof : IsPrime' value

prime-product : UList Prime' -> Nat
prime-product = unordered-product ∘ (map Prime'.value)

prime-productʰ : CommMonoidʰ prime-product
prime-productʰ = unordered-productʰ ∘ʰ mapʰ 

data PrimeFactorization' : Nat -> Set where
  prime-factorization : (ps : UList Prime') -> PrimeFactorization' (prime-product ps)


prime-only-divisors : {p d : Nat} -> IsPrime' p -> d div' p -> (d == p) ⊎ (d == 1)
prime-only-divisors {p} {d} (is-prime' _ pf) d%p with (≤->≤s (div'->≤ d%p))
... | refl-≤s = inj-l refl
... | (step-≤s pr) = inj-r (pf d (inc-≤s pr) d%p)

0-is-¬prime : ¬(IsPrime' 0)
0-is-¬prime ()
1-is-¬prime : ¬(IsPrime' 1)
1-is-¬prime ()

-- Build up machinery for decidable prime factorization
private

  data PrimeFactorizationTree : Nat -> Set where
    prime-factorization-tree-prime : {p : Nat} -> IsPrime' p -> PrimeFactorizationTree p
    prime-factorization-tree-composite : {m n : Nat}
      -> PrimeFactorizationTree m
      -> PrimeFactorizationTree n
      -> PrimeFactorizationTree (m *' n)

  data Primality : Nat -> Set where
    primality-prime : {p : Nat} -> IsPrime' p -> Primality p
    primality-composite : {a' b' : Nat} (a b : Nat) -> {a == (suc (suc a'))} -> {b == (suc (suc b'))}
                          -> Primality ((suc (suc a')) *' (suc (suc b')))

  data PrimeUpTo : Nat -> Nat -> Set where
    prime-up-to : (p' : Nat) -> (bound : Nat)
                  -> ((d : Nat) -> d <s bound -> (d div' (suc (suc p'))) -> d == 1)
                  -> PrimeUpTo (suc (suc p')) bound

  prime-up-to->is-prime' : {n : Nat} -> PrimeUpTo n n -> IsPrime' n
  prime-up-to->is-prime' (prime-up-to p' (suc (suc p')) f) = (is-prime' p' f)

  prime-up-to-zero : (p' : Nat) -> PrimeUpTo (suc (suc p')) zero
  prime-up-to-zero p' = prime-up-to p' zero (\ d ())

  prime-up-to-suc : {p b : Nat} -> PrimeUpTo p b -> ¬(b div' p) -> PrimeUpTo p (suc b)
  prime-up-to-suc {p} (prime-up-to p' b f) ¬bp = (prime-up-to p' (suc b) g)
    where
    g : (d : Nat) -> d <s (suc b) -> (d div' p) -> d == 1
    g d refl-≤s dp = bot-elim (¬bp dp)
    g d (step-≤s d≤b) dp = f d d≤b dp

  prime-up-to-one : (p' : Nat) -> PrimeUpTo (suc (suc p')) 1
  prime-up-to-one p' = prime-up-to-suc (prime-up-to-zero p') pr
    where
    pr : ¬(0 div' (suc (suc p')))
    pr 0p with (path->id (div'-zero->zero 0p))
    ...      | ()

  prime-up-to-two : (p' : Nat) -> PrimeUpTo (suc (suc p')) 2
  prime-up-to-two p' = prime-up-to p' 2 g
    where
    g : (d : Nat) -> d <s 2 -> (d div' (suc (suc p'))) -> d == 1
    g d refl-≤s dp = refl
    g d (step-≤s d≤b) dp with (prime-up-to-one p') 
    ... | (prime-up-to _ _ f) = f d d≤b dp

2-is-prime : IsPrime' 2
2-is-prime = prime-up-to->is-prime' (prime-up-to-two 0)

private
  data _≤u_ : Nat -> Nat -> Set where
    refl-≤u : {m : Nat} -> m ≤u m
    step-≤u : {m n : Nat} -> suc m ≤u n -> m ≤u n
  
  ≤u->≤ : {m n : Nat} -> m ≤u n -> m ≤ n
  ≤u->≤ (refl-≤u {m}) = same-≤ m
  ≤u->≤ (step-≤u rec) = (dec-≤ (suc-≤ (≤u->≤ rec)))
 

  div->composite : {d n : Nat} -> d != 0 -> d != 1 -> d != n -> n != 0 -> d div' n -> Primality n
  div->composite d0 d1 dn n0 (div'-exists 0 n x p) = bot-elim (d0 refl)
  div->composite d0 d1 dn n0 (div'-exists 1 n x p) = bot-elim (d1 refl)
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc _)) n 0 p) = bot-elim (n0 (sym p))
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc _)) n 1 p) = bot-elim (dn ((sym (+'-right-zero {d})) >=> p))
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc d')) n x@(suc (suc x')) pr) = 
    transport (\i -> Primality (pr i)) (primality-composite x d {refl {x = x}} {refl {x = d}})

>1 : {n' : Nat} -> 2 ≤ (suc (suc n'))
>1 {n'} = inc-≤ (inc-≤ zero-≤)

private
  compute-primality : {p : Nat} -> p > 1 -> Primality p
  compute-primality {suc (suc p')} (inc-≤ (inc-≤ _)) =
      rec (0≤i p' refl-≤u) (prime-up-to-two p')
    where
    0≤i : (i : Nat) -> i ≤u p' -> 0 ≤u p'
    0≤i 0 pr = pr
    0≤i (suc i) pr = 0≤i i (step-≤u pr)
    
    rec : {i : Nat} -> i ≤u p' -> PrimeUpTo (suc (suc p')) (suc (suc i)) -> Primality (suc (suc p'))
    rec refl-≤u pr = primality-prime (prime-up-to->is-prime' pr)
    rec {i} (step-≤u step) pr with decide-div (suc (suc i)) (suc (suc p'))
    ... | no not-div = rec step (prime-up-to-suc pr not-div)
    ... | yes div = div->composite {suc (suc i)} {suc (suc p')} 
                    (\ p -> bot-elim (zero-suc-absurd (sym p)))
                    (\ p -> bot-elim (zero-suc-absurd (sym (suc-injective p))))
                    (<->!= (inc-≤ (inc-≤ (≤u->≤ step))))
                    (\ p -> bot-elim (zero-suc-absurd (sym p)))
                    div

    
  compute-prime-factorization-tree : {n : Nat} -> n > 1 -> PrimeFactorizationTree n
  compute-prime-factorization-tree {p} p>1  = rec p>1 (same-≤ p)
    where
    rec : {i : Nat} {p : Nat} -> p > 1 -> (p ≤ i) -> PrimeFactorizationTree p
    rec {_} p@{suc (suc p')} p>1 (inc-≤ p-bound) with (compute-primality p>1)
    ... | (primality-prime prime) = (prime-factorization-tree-prime prime)
    ... | (primality-composite {m'} {n'} m n {p1} {p2})
          with (path->id p1) | (path->id p2)
    ... | refl-===     | refl-=== = 
            (prime-factorization-tree-composite 
              (rec (>1) (trans-≤ (dec-≤ m-bound) p-bound))
              (rec (>1) (trans-≤ (dec-≤ n-bound) p-bound)))
            where
            base-eq-m : n *' m == p
            base-eq-n : m *' n == p
            base-eq-m = *'-commute {n} {m} >=> base-eq-n
            base-eq-n = (\i -> p1 i *' p2 i)

            rearranged-eq2-m : (suc m) +' (1 +' (m' +' n' *' m)) == p
            rearranged-eq2-n : (suc n) +' (1 +' (n' +' m' *' n)) == p
            rearranged-eq2-m = sym (+'-right-suc {m}) >=> base-eq-m
            rearranged-eq2-n = sym (+'-right-suc {n}) >=> base-eq-n

            m-bound : (suc m ≤ p)
            n-bound : (suc n ≤ p)
            m-bound = (≤-a+'b==c rearranged-eq2-m)
            n-bound = (≤-a+'b==c rearranged-eq2-n)
    rec (inc-≤ ()) (inc-≤ zero-≤)

  
  prime-factorization-* : {m n : Nat} 
    -> PrimeFactorization' m 
    -> PrimeFactorization' n
    -> PrimeFactorization' (m *' n)
  prime-factorization-* (prime-factorization p1s) (prime-factorization p2s) =
    transport (\i -> PrimeFactorization' (p i)) (prime-factorization (p1s ++ p2s))
    where
    p = CommMonoidʰ.preserves-∙ prime-productʰ p1s p2s


PrimeDivisor : Nat -> Nat -> Set
PrimeDivisor n d = IsPrime' d × d div' n

exists-prime-divisor : {n : Nat} -> n > 1 -> exists (PrimeDivisor n)
exists-prime-divisor {n} n>1 = rec (compute-prime-factorization-tree n>1) div'-refl
  where 
  rec : {a : Nat} -> (PrimeFactorizationTree a) -> a div' n -> exists (PrimeDivisor n)
  rec {a} (prime-factorization-tree-prime prime-a) a%n = existence a (prime-a , a%n)
  rec {a} (prime-factorization-tree-composite {d} {e} df ef) a%n =
    rec ef (div'-trans (div'-exists e a d refl) a%n)
