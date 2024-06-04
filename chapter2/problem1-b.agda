{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.problem1-b where

open import base
open import chapter2.prime-divisors
open import chapter2.totient
open import chapter2.totient-rational
open import div
open import equality
open import equivalence
open import finite-commutative-monoid
open import finite-product
open import functions
open import int
open import isomorphism
open import nat
open import nat.even-odd
open import nat.order
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import prime
open import prime-gcd
open import rational
open import rational-prime
open import relatively-prime
open import ring
open import ring.implementations.rational
open import semiring
open import semiring.instances.nat
open import sigma

private
  module Ring-ℚ = Ring Ring-ℚ

  Injective-ℕ->ℚ : Injective ℕ->ℚ
  Injective-ℕ->ℚ = ∘-Injective Injective-ℤ->ℚ nonneg-injective


problem1-b : (n : Nat⁺) -> (φ (2⁺ *⁺ n) == φ n) ≃ Odd ⟨ n ⟩
problem1-b n⁺@(n , _) =
  isoToEquiv (isProp->iso path->odd odd->path (isSetNat _ _) (isProp-Odd n))
  where
  module _ (on : Odd n) where
    private
      ¬2∣n : ¬ (2 div' n)
      ¬2∣n = eqFun Odd≃¬div' on

      co-prime : RelativelyPrime⁰ 2 n
      co-prime = prime->relatively-prime (2 , 2-is-prime) ¬2∣n

    odd->path : φ (2⁺ *⁺ n⁺) == φ n⁺
    odd->path =
      proj₂ Multiplicative-φ 2⁺ n⁺ co-prime >=>
      *-left (φ-prime (2 , 2-is-prime)) >=>
      *-left-one

  module _ (en : Even n) where
    same-pdivs : (p : Prime') -> (⟨ p ⟩ div' (2 * n)) ≃ (⟨ p ⟩ div' n)
    same-pdivs p@(p' , _) =
      isoToEquiv (isProp->iso div-forward div-backward (isPropDiv' (2⁺ *⁺ n⁺)) (isPropDiv' n⁺))
      where
      div-forward : (p' div' (2 * n)) -> (p' div' n)
      div-forward p∣2n = handle (prime-divides-a-factor p p∣2n)
        where
        handle : (p' div' 2) ⊎ (p' div' n) -> (p' div' n)
        handle (inj-r p∣n) = p∣n
        handle (inj-l p∣2) = div'-trans p∣2 (eqFun Even≃div' en)

      div-backward : (p' div' n) -> (p' div' (2 * n))
      div-backward (x , path) = (2 * x , *-assocᵉ 2 x p' >=> cong (2 *_) path)

    p1 : PrimeDivisor (2⁺ *⁺ n⁺) ≃ PrimeDivisor n⁺
    p1 = existential-eq same-pdivs

    p2 : (finiteProduct (FinSet-PrimeDivisor (2⁺ *⁺ n⁺))
           (\(p , _) -> (1r r+ (r- (fst (Ring-ℚ.u1/ (ℚUnit-prime p))))))) ==
         (finiteProduct (FinSet-PrimeDivisor n⁺)
           (\(p , _) -> (1r r+ (r- (fst (Ring-ℚ.u1/ (ℚUnit-prime p)))))))
    p2 = finiteMergeᵉ-convert _ _ _ (equiv⁻¹ p1) _

    p3 : φℚ (2⁺ *⁺ n⁺) == 2r * φℚ n⁺
    p3 = φℚ-finiteProduct >=>
         *-right p2 >=>
         *-left (Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ _ _) >=>
         *-assoc >=>
         *-right (sym φℚ-finiteProduct)

    p4 : φ (2⁺ *⁺ n⁺) == 2 * φ n⁺
    p4 = Injective-ℕ->ℚ (p3 >=> sym (Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ _ _))

    p5 : φ n⁺ < φ (2⁺ *⁺ n⁺)
    p5 = trans-=-< (sym *-left-one) (trans-<-= lt (sym p4))
      where
      lt : (1 * φ n⁺) < (2 * φ n⁺)
      lt = *₂-preserves-< (refl-≤ᵉ 2) (φ-0< n⁺)

    even->¬path : φ (2⁺ *⁺ n⁺) != φ n⁺
    even->¬path p = irrefl-path-< (sym p) p5

  path->odd : φ (2⁺ *⁺ n⁺) == φ n⁺ -> Odd n
  path->odd p = ¬Even->Odd n (\e -> even->¬path e p)
