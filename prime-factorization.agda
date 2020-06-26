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
    primality-composite : (a b : Nat) -> a > 1 -> b > 1 -> Primality (a *' b)

  -- ≤ recursion scheme that supports counting up
  data _≤u_ : Nat -> Nat -> Type₀ where
    refl-≤u : {m : Nat} -> m ≤u m
    step-≤u : {m n : Nat} -> suc m ≤u n -> m ≤u n

  ≤u->≤ : {m n : Nat} -> m ≤u n -> m ≤ n
  ≤u->≤ (refl-≤u {m}) = same-≤ m
  ≤u->≤ (step-≤u rec) = (pred-≤ (right-suc-≤ (≤u->≤ rec)))

  -- Helper function for turning explicitly indexed > 1 to propositionally > 1
  >1 : {n' : Nat} -> (suc (suc n')) > 1
  >1 {n'} = suc-≤ (suc-≤ zero-≤)


  div->composite : {d n : Nat} -> d != 0 -> d != 1 -> d != n -> n != 0 -> d div' n -> Primality n
  div->composite d0 d1 dn n0 (div'-exists 0 n x p) = bot-elim (d0 refl)
  div->composite d0 d1 dn n0 (div'-exists 1 n x p) = bot-elim (d1 refl)
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc _)) n 0 p) = bot-elim (n0 (sym p))
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc _)) n 1 p) =
    bot-elim (dn ((sym (+'-right-zero {d})) >=> p))
  div->composite d0 d1 dn n0 (div'-exists (suc (suc d')) n (suc (suc x')) pr) =
    transport (\i -> Primality (pr i))
              (primality-composite (suc (suc x')) (suc (suc d')) >1 >1)


  compute-primality : {p : Nat} -> p > 1 -> Primality p
  compute-primality p@{suc (suc p')} p>1  =
      rec (0≤i p' refl-≤u) (prime-up-to-two p p>1)
    where
    0≤i : (i : Nat) -> i ≤u p' -> 0 ≤u p'
    0≤i 0 pr = pr
    0≤i (suc i) pr = 0≤i i (step-≤u pr)

    rec : {i : Nat} -> i ≤u p' -> PrimeUpTo p (suc (suc i)) -> Primality p
    rec refl-≤u pr = primality-prime (prime-up-to->is-prime' pr)
    rec {i} (step-≤u step) pr with decide-div (suc (suc i)) p
    ... | no not-div = rec step (prime-up-to-suc pr not-div)
    ... | yes div = div->composite {suc (suc i)} {p}
                    (\ p -> bot-elim (zero-suc-absurd (sym p)))
                    (\ p -> bot-elim (zero-suc-absurd (sym (suc-injective p))))
                    (<->!= (suc-≤ (suc-≤ (≤u->≤ step))))
                    (\ p -> bot-elim (zero-suc-absurd (sym p)))
                    div
  compute-primality {suc zero} p>1 = bot-elim (same-≮ p>1)
  compute-primality {zero}     p>1 = bot-elim (zero-≮ p>1)


  compute-prime-factorization-tree : {n : Nat} -> n > 1 -> PrimeFactorizationTree n
  compute-prime-factorization-tree {n} = strong-induction' cases n
    where

    >1-*'->both< : {a b m : Nat} -> a > 1 -> b > 1 -> a *' b == m -> (a < m × b < m)
    >1-*'->both< {a} {b} {m} a>1 b>1 a*b==m with (transport ≤==≤Σ' a>1) | (transport ≤==≤Σ' b>1)
    ... | (a' , ssa'==a) | (b' , ssb'==b) = a<m , b<m
      where
      ssa'*ssb'==m : (suc (suc a')) *' (suc (suc b')) == m
      ssa'*ssb'==m = transport (\i -> (ssa'==a (~ i)) *' (ssb'==b (~ i)) == m) a*b==m

      rearranged-b : (suc (suc (suc b'))) +' ((suc b') +' a' *' (suc (suc b'))) == m
      rearranged-b =
        sym (+'-right-suc {suc (suc b')})
        >=> ssa'*ssb'==m

      rearranged-a : (suc (suc (suc a'))) +' ((suc a') +' b' *' (suc (suc a'))) == m
      rearranged-a =
        sym (+'-right-suc {suc (suc a')})
        >=> (*'-commute {suc (suc b')} {suc (suc a')})
        >=> ssa'*ssb'==m

      sssa'≤Σ'm : (suc (suc (suc a'))) ≤Σ' m
      sssb'≤Σ'm : (suc (suc (suc b'))) ≤Σ' m
      sssa'≤Σ'm = (_ , rearranged-a)
      sssb'≤Σ'm = (_ , rearranged-b)

      a<m : a < m
      b<m : b < m
      a<m = transport (\i -> (≤==≤Σ' {suc (ssa'==a i)} {m} (~ i))) sssa'≤Σ'm
      b<m = transport (\i -> (≤==≤Σ' {suc (ssb'==b i)} {m} (~ i))) sssb'≤Σ'm

    cases : {m : Nat}
           -> ({n : Nat} -> n < m -> n > 1 -> PrimeFactorizationTree n)
           -> m > 1 -> PrimeFactorizationTree m
    cases f m>1 with (compute-primality m>1)
    ... | (primality-prime prime) = (prime-factorization-tree-prime prime)
    ... | (primality-composite a b a>1 b>1) with (>1-*'->both< a>1 b>1 refl)
    ...   | (a<m , b<m) = prime-factorization-tree-composite (f a<m a>1) (f b<m b>1)




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

exists-prime-divisor : {n : Nat} -> n > 1 -> Σ[ d ∈ Nat ] (PrimeDivisor n d)
exists-prime-divisor {n} n>1 = rec (compute-prime-factorization-tree n>1) div'-refl
  where
  rec : {a : Nat} -> (PrimeFactorizationTree a) -> a div' n -> Σ[ d ∈ Nat ] (PrimeDivisor n d)
  rec {a} (prime-factorization-tree-prime prime-a) a%n = a , (prime-a , a%n)
  rec {a} (prime-factorization-tree-composite {d} {e} df ef) a%n =
    rec ef (div'-trans (div'-exists e a d refl) a%n)

compute-prime-factorization : {n : Nat} -> n > 0 -> (PrimeFactorization' n)
compute-prime-factorization {suc zero}    _ =
  (prime-factorization [])
compute-prime-factorization {suc (suc n)} _ =
  (convert-prime-factorization (compute-prime-factorization-tree (suc-≤ (zero-< {n}))))
