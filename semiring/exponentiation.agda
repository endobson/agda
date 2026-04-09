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
open import semiring.instances.nat
open import semiring.unit
open import sigma.base
open import truncation

-- exp x 1 = x
-- exp x (a + b) = exp x a * exp x b
-- exp (x * y) n = exp x n * exp y n

module _ {ℓ : Level} {D : Type ℓ} {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}} where

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
      +ʰ : ∀ x -> Monoidʰᵉ Monoid-ℕ+ S.*-Monoid (\n -> f x n)

  private
    opaque
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


  _^ℕ_ : D -> ℕ -> D
  x ^ℕ zero = 1#
  x ^ℕ (suc n) = x * (x ^ℕ n)

  private
    opaque
      is^ℕ-^ℕ : is^ℕ _^ℕ_
      is^ℕ-^ℕ = record
        { one = one
        ; *ʰ = *ʰ
        ; +ʰ = +ʰ
        }
        where
        one : ∀ x -> x ^ℕ 1 == x
        one _ = *-right-one

        *ʰ : ∀ n -> Monoidʰᵉ S.*-Monoid S.*-Monoid (\x -> x ^ℕ n)
        *ʰ zero .Monoidʰᵉ.preserves-ε = refl
        *ʰ zero .Monoidʰᵉ.preserves-∙ _ _ = sym *-right-one
        *ʰ (suc n) .Monoidʰᵉ.preserves-ε =
          *-left-one >=> *ʰ n .Monoidʰᵉ.preserves-ε
        *ʰ (suc n) .Monoidʰᵉ.preserves-∙ x y =
          *-right (*ʰ n .Monoidʰᵉ.preserves-∙ x y) >=>
          *-swap

        +ʰ : ∀ x -> Monoidʰᵉ Monoid-ℕ+ S.*-Monoid (\n -> x ^ℕ n)
        +ʰ x .Monoidʰᵉ.preserves-ε = refl
        +ʰ x .Monoidʰᵉ.preserves-∙ = f
          where
          f : (n1 n2 : ℕ) -> x ^ℕ (n1 + n2) == x ^ℕ n1 * x ^ℕ n2
          f zero    n2 = sym *-left-one
          f (suc n) n2 = *-right (f n n2) >=> sym *-assoc

  ∃!^ℕ : ∃! (D -> ℕ -> D) is^ℕ
  ∃!^ℕ = (_^ℕ_ , is^ℕ-^ℕ) , isProp-Σis^ℕ _

  opaque
    ^ℕ-one : {x : D} -> x ^ℕ 1 == x
    ^ℕ-one = *-right-one

    ^ℕ-preserves-1# : (n : ℕ) -> 1# ^ℕ n == 1#
    ^ℕ-preserves-1# zero = refl
    ^ℕ-preserves-1# (suc n) = *-left-one >=> ^ℕ-preserves-1# n

    ^ℕ-distrib-+-left : {x : D} (n1 n2 : ℕ) -> x ^ℕ (n1 + n2) == (x ^ℕ n1) * (x ^ℕ n2)
    ^ℕ-distrib-+-left {x} n1 n2 = (Monoidʰ.preserves-∙ (is^ℕ.+ʰ (∃!-prop ∃!^ℕ) x) n1 n2)

    ^ℕ-distrib-*-right : {x y : D} (n : Nat) -> (x * y) ^ℕ n == (x ^ℕ n) * (y ^ℕ n)
    ^ℕ-distrib-*-right {x} {y} n = (Monoidʰ.preserves-∙ (is^ℕ.*ʰ (∃!-prop ∃!^ℕ) n) x y)

    ^ℕ-distrib-*-left : {x : D} (n1 n2 : Nat) -> x ^ℕ (n1 * n2) == (x ^ℕ n1) ^ℕ n2
    ^ℕ-distrib-*-left {x} n1 n2 = cong (x ^ℕ_) (*-commuteᵉ n1 n2) >=> ^ℕ-distrib-*' n2 n1
      where
      ^ℕ-distrib-*' : (n1 n2 : Nat) -> x ^ℕ (n1 * n2) == (x ^ℕ n2) ^ℕ n1
      ^ℕ-distrib-*' zero n2 = refl
      ^ℕ-distrib-*' (suc n) n2 =
        (^ℕ-distrib-+-left n2 (n * n2)) >=>
        (*-right (^ℕ-distrib-*' n n2)) >=>
        (*-left (sym ^ℕ-one)) >=>
        sym (^ℕ-distrib-+-left 1 n)

module _ {ℓ₁ ℓ₂ : Level} {D₁ : Type ℓ₁} {D₂ : Type ℓ₂}
         {ACM₁ : AdditiveCommMonoid D₁}
         {ACM₂ : AdditiveCommMonoid D₂}
         {{S₁ : Semiring ACM₁}}
         {{S₂ : Semiring ACM₂}}
         where
  module _ {f : D₁ -> D₂} (h : Semiringʰ f) where
    private
      module h = Semiringʰ h
    Semiringʰ-preserves-^ℕ : {x : D₁} (n : Nat) -> f (x ^ℕ n) == f x ^ℕ n
    Semiringʰ-preserves-^ℕ     zero = h.preserves-1#
    Semiringʰ-preserves-^ℕ {x} (suc n) =
      h.preserves-* x (x ^ℕ n) >=> *-right (Semiringʰ-preserves-^ℕ n)


module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}}
         where
  _u^ℕ_ : Unit D -> ℕ -> Unit D
  a u^ℕ zero = 1u
  a u^ℕ (suc n) = a u* (a u^ℕ n)

  opaque
    u^ℕ-one : {x : Unit D} -> (x u^ℕ 1) == x
    u^ℕ-one = ΣProp-path isProp-isUnit *-right-one

    u^ℕ-distrib-+ : {b : Unit D} {x y : ℕ} -> b u^ℕ (x + y) == (b u^ℕ x) u* (b u^ℕ y)
    u^ℕ-distrib-+ {b} {zero} {y} =
      cong (b u^ℕ_) +-left-zero >=> sym u*-left-one
    u^ℕ-distrib-+ {b} {suc x} {y} =
      cong (b u*_) (u^ℕ-distrib-+ {b} {x} {y}) >=> sym u*-assoc
