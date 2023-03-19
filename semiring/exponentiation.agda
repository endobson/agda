{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.exponentiation where

open import additive-group
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import funext
open import hlevel
open import monoid
open import nat
open import nat.monoid-homomorphism
open import semiring
open import sigma.base

module _ {ℓ : Level} {D : Type ℓ} {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}}  where

  private
    instance
      IACM = ACM
    Monoid-ℕ+ : Monoid ℕ
    Monoid-ℕ+ = CommMonoid.monoid (AdditiveCommMonoid.comm-monoid useⁱ)

    module S = Semiring S

  record is^ℕ (f : D -> ℕ -> D) : Type ℓ where
    field
      one : ∀ x -> f x 1 == x
      *ʰ : ∀ n -> Monoidʰᵉ S.*-Monoid S.*-Monoid (\x -> f x n)
      +ʰ : ∀ x -> Monoidʰᵉ Monoid-ℕ+ S.*-Monoid (f x)

  private
    isProp-is^ℕ : {f : D -> ℕ -> D} -> isProp (is^ℕ f)
    isProp-is^ℕ {f} p1 p2 i = record
      { one = isPropΠ (\x -> S.isSet-Domain (f x 1) x) p1.one p2.one i
      ; *ʰ = isPropΠ (\n -> isProp-Monoidʰ) p1.*ʰ p2.*ʰ i
      ; +ʰ = isPropΠ (\n -> isProp-Monoidʰ) p1.+ʰ p2.+ʰ i
      }
      where
      module p1 = is^ℕ p1
      module p2 = is^ℕ p2

    isProp-Σis^ℕ : isProp (Σ (D -> ℕ -> D) is^ℕ)
    isProp-Σis^ℕ (f , pf) (g , pg) =
      ΣProp-path isProp-is^ℕ (funExt (\x -> Monoidʰ-ℕ-path (pf.+ʰ x) (pg.+ʰ x)
                                              (pf.one x >=> sym (pg.one x))))
      where
      module pf = is^ℕ pf
      module pg = is^ℕ pg



-- exp x 1 = x
-- exp x (a + b) = exp x a * exp x b
-- exp (x * y) n = exp x n * exp y n
