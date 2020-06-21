{-# OPTIONS --cubical --safe --exact-split #-}

module prime-factorization where

open import base
open import commutative-monoid
open import div
open import equality
open import functions
open import nat
open import prime
open import relation
open import ring
open import unordered-list

open PrimeUpTo

module NatSemiring = Semiring NatSemiring
open NatSemiring using (unordered-product; unordered-productʰ)

prime-product : UList Prime' -> Nat
prime-product = unordered-product ∘ (map Prime'.value)

prime-productʰ : CommMonoidʰ prime-product
prime-productʰ = unordered-productʰ ∘ʰ mapʰ

data PrimeFactorization' : Nat -> Type₀ where
  prime-factorization : (ps : UList Prime') -> PrimeFactorization' (prime-product ps)

private
  data PrimeFactorizationTree : Nat -> Type₀ where
    prime-factorization-tree-prime : {p : Nat} -> IsPrime' p -> PrimeFactorizationTree p
    prime-factorization-tree-composite : {m n : Nat}
      -> PrimeFactorizationTree m
      -> PrimeFactorizationTree n
      -> PrimeFactorizationTree (m *' n)

  data Primality : Nat -> Type₀ where
    primality-prime : {p : Nat} -> IsPrime' p -> Primality p
    primality-composite : {a' b' : Nat} (a b : Nat) -> {a == (suc (suc a'))} -> {b == (suc (suc b'))}
                          -> Primality ((suc (suc a')) *' (suc (suc b')))

  -- ≤ recursion scheme that supports counting up
  data _≤u_ : Nat -> Nat -> Type₀ where
    refl-≤u : {m : Nat} -> m ≤u m
    step-≤u : {m n : Nat} -> suc m ≤u n -> m ≤u n

  ≤u->≤ : {m n : Nat} -> m ≤u n -> m ≤ n
  ≤u->≤ (refl-≤u {m}) = same-≤ m
  ≤u->≤ (step-≤u rec) = (pred-≤ (right-suc-≤ (≤u->≤ rec)))

  div->composite : {d n : Nat} -> d != 0 -> d != 1 -> d != n -> n != 0 -> d div' n -> Primality n
  div->composite d0 d1 dn n0 (div'-exists 0 n x p) = bot-elim (d0 refl)
  div->composite d0 d1 dn n0 (div'-exists 1 n x p) = bot-elim (d1 refl)
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc _)) n 0 p) = bot-elim (n0 (sym p))
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc _)) n 1 p) =
    bot-elim (dn ((sym (+'-right-zero {d})) >=> p))
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc d')) n x@(suc (suc x')) pr) =
    transport (\i -> Primality (pr i)) (primality-composite x d {refl {x = x}} {refl {x = d}})


  compute-primality : {p : Nat} -> p > 1 -> Primality p
  compute-primality {suc (suc p')} (suc-≤ (suc-≤ _)) =
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
                    (<->!= (suc-≤ (suc-≤ (≤u->≤ step))))
                    (\ p -> bot-elim (zero-suc-absurd (sym p)))
                    div


  compute-prime-factorization-tree : {n : Nat} -> n > 1 -> PrimeFactorizationTree n
  compute-prime-factorization-tree {p} p>1  = rec p>1 (same-≤ p)
    where
    >1 : {n' : Nat} -> 2 ≤ (suc (suc n'))
    >1 {n'} = suc-≤ (suc-≤ zero-≤)

    rec : {i : Nat} {p : Nat} -> p > 1 -> (p ≤ i) -> PrimeFactorizationTree p
    rec {_} p@{suc (suc p')} p>1 (suc-≤ p-bound) with (compute-primality p>1)
    ... | (primality-prime prime) = (prime-factorization-tree-prime prime)
    ... | (primality-composite {m'} {n'} m n {p1} {p2})
          with (path->id p1) | (path->id p2)
    ... | refl-===     | refl-=== =
            (prime-factorization-tree-composite
              (rec (>1) (trans-≤ (pred-≤ m-bound) p-bound))
              (rec (>1) (trans-≤ (pred-≤ n-bound) p-bound)))
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
    rec (suc-≤ ()) (suc-≤ zero-≤)


  prime-factorization-* : {m n : Nat}
    -> PrimeFactorization' m
    -> PrimeFactorization' n
    -> PrimeFactorization' (m *' n)
  prime-factorization-* (prime-factorization p1s) (prime-factorization p2s) =
    transport (\i -> PrimeFactorization' (p i)) (prime-factorization (p1s ++ p2s))
    where
    p = CommMonoidʰ.preserves-∙ prime-productʰ p1s p2s

  prime-factorization-base : {p : Nat} -> IsPrime' p
    -> PrimeFactorization' p
  prime-factorization-base {p} is-prime =
    transport (\i -> PrimeFactorization' (path i))
              (prime-factorization (record { value = p ; proof = is-prime } :: []))
    where
    path = *'-right-one {p}


  convert-prime-factorization : {n : Nat} -> PrimeFactorizationTree n -> PrimeFactorization' n
  convert-prime-factorization (prime-factorization-tree-prime is-prime) =
    prime-factorization-base is-prime
  convert-prime-factorization (prime-factorization-tree-composite t1 t2) =
    prime-factorization-* (convert-prime-factorization t1) (convert-prime-factorization t2)


PrimeDivisor : Nat -> Nat -> Type₀
PrimeDivisor n d = IsPrime' d × d div' n

exists-prime-divisor : {n : Nat} -> n > 1 -> exists (PrimeDivisor n)
exists-prime-divisor {n} n>1 = rec (compute-prime-factorization-tree n>1) div'-refl
  where
  rec : {a : Nat} -> (PrimeFactorizationTree a) -> a div' n -> exists (PrimeDivisor n)
  rec {a} (prime-factorization-tree-prime prime-a) a%n = existence a (prime-a , a%n)
  rec {a} (prime-factorization-tree-composite {d} {e} df ef) a%n =
    rec ef (div'-trans (div'-exists e a d refl) a%n)

compute-prime-factorization : {n : Nat} -> n > 0 -> (PrimeFactorization' n)
compute-prime-factorization {suc zero}    _ =
  (prime-factorization [])
compute-prime-factorization {suc (suc n)} _ =
  (convert-prime-factorization (compute-prime-factorization-tree (suc-≤ (zero-< {n}))))