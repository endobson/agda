{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.initial where

open import additive-group
open import additive-group.instances.nat
open import base
open import commutative-monoid
open import equality
open import functions
open import funext
open import monoid
open import nat
open import nat.monoid-homomorphism
open import semiring
open import semiring.instances.nat
open import sigma.base
open import truncation


module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

  private
    lift-nat : ℕ -> D
    lift-nat zero = 0#
    lift-nat (suc n) = (1# + (lift-nat n))

    lift-nat-0# : (lift-nat 0#) == 0#
    lift-nat-0# = refl

    lift-nat-1# : (lift-nat 1#) == 1#
    lift-nat-1# = +-right-zero

    lift-nat-+ : (x y : ℕ) -> (lift-nat (x + y)) == (lift-nat x) + (lift-nat y)
    lift-nat-+ zero    y  = sym +-left-zero
    lift-nat-+ (suc x) y = (+-right (lift-nat-+ x y)) >=> sym +-assoc

    lift-nat-* : (x y : ℕ) -> (lift-nat (x * y)) == (lift-nat x) * (lift-nat y)
    lift-nat-* x y = NatElim-01+ p0 p1 p+ x
      where
      p0 : (lift-nat (0 * y)) == (lift-nat 0) * (lift-nat y)
      p0 = sym *-left-zero
      p1 : (lift-nat (1 * y)) == (lift-nat 1) * (lift-nat y)
      p1 = sym *-left-one >=> cong2 _*_ (sym lift-nat-1#) (cong lift-nat (*-left-oneᵉ y))
      p+ : (a b : ℕ) ->
           lift-nat (a * y) == (lift-nat a) * (lift-nat y) ->
           lift-nat (b * y) == (lift-nat b) * (lift-nat y) ->
           (lift-nat ((a + b) * y)) == (lift-nat (a + b)) * (lift-nat y)
      p+ a b ap bp =
        cong lift-nat (*-distrib-+-rightᵉ a b y) >=>
        lift-nat-+ (a * y) (b * y) >=>
        +-cong ap bp >=>
        sym *-distrib-+-right >=>
        *-left (sym (lift-nat-+ a b))


    lift-natʰ : Semiringʰ lift-nat
    lift-natʰ = record
      { +ʰ = record
        { preserves-ε = lift-nat-0#
        ; preserves-∙ = lift-nat-+
        }
      ; *ʰ = record
        { preserves-ε = lift-nat-1#
        ; preserves-∙ = lift-nat-*
        }
      }

    module _ (f g : ℕ -> D) (fʰ : Semiringʰ f) (gʰ : Semiringʰ g) where
      private
        module fʰ = Semiringʰ fʰ
        module gʰ = Semiringʰ gʰ
      unique-homo-path : f == g
      unique-homo-path =
        Monoidʰ-ℕ-path fʰ.+ʰ gʰ.+ʰ (fʰ.preserves-1# >=> sym gʰ.preserves-1#)

  abstract
    ∃!ℕ->Semiring : ∃! (ℕ -> D) Semiringʰ
    ∃!ℕ->Semiring =
      (lift-nat , lift-natʰ) ,
      \(f , fʰ) -> ΣProp-path isProp-Semiringʰ (unique-homo-path lift-nat f lift-natʰ fʰ)

  ℕ->Semiring : ℕ -> D
  ℕ->Semiring = ∃!-val ∃!ℕ->Semiring

  module _ {ℓP : Level} {P : D -> Type ℓP} where
    abstract
      ℕ->Semiring-elim :
        (P 0#) -> (P 1#) ->
        (∀ a b -> P a -> P b -> P (a + b)) ->
        ∀ n -> P (ℕ->Semiring n)
      ℕ->Semiring-elim p0 p1 p+ = NatElim-01+ p'0 p'1 p'+
        where
        module h = Semiringʰ (∃!-prop ∃!ℕ->Semiring)
        p'0 : P (ℕ->Semiring 0)
        p'0 = subst P (sym h.preserves-0#) p0
        p'1 : P (ℕ->Semiring 1)
        p'1 = subst P (sym h.preserves-1#) p1
        p'+ : ∀ a b -> P (ℕ->Semiring a) -> P (ℕ->Semiring b) -> P (ℕ->Semiring (a + b))
        p'+ a b p'a p'b = subst P (sym (h.preserves-+ a b)) (p+ _ _ p'a p'b)

  module _ {ℓP : Level} {P : D -> D -> Type ℓP} where
    abstract
      ℕ->Semiring-elim2 :
        (P 0# 0#) -> (P 0# 1#) -> (P 1# 0#) ->
        (∀ a b c d -> P a b -> P c d -> P (a + c) (b + d)) ->
        ∀ n m -> P (ℕ->Semiring n) (ℕ->Semiring m)
      ℕ->Semiring-elim2 p00 p01 p10 p+ =
        (\n m -> subst2 P  +-right-zero +-left-zero (p+ _ _ _ _ (∀P-0 n) (∀P0- m)))
        where
        module h = Semiringʰ (∃!-prop ∃!ℕ->Semiring)
        P0- : D -> Type ℓP
        P0- d = P 0# d
        P-0 : D -> Type ℓP
        P-0 d = P d 0#
        ∀P0- : ∀ n -> P0- (ℕ->Semiring n)
        ∀P0- = ℕ->Semiring-elim p00 p01 p'+
          where
          p'+ : (∀ a b -> P0- a -> P0- b -> P0- (a + b))
          p'+ a b p'a p'b = subst2 P (+-left-zero) refl (p+ _ _ _ _ p'a p'b)
        ∀P-0 : ∀ n -> P-0 (ℕ->Semiring n)
        ∀P-0 = ℕ->Semiring-elim p00 p10 p'+
          where
          p'+ : (∀ a b -> P-0 a -> P-0 b -> P-0 (a + b))
          p'+ a b p'a p'b = subst2 P refl (+-left-zero) (p+ _ _ _ _ p'a p'b)

abstract
  ℕ->Semiring-ℕ-path : ∀ n -> ℕ->Semiring n == n
  ℕ->Semiring-ℕ-path n = (\i -> ∃!-unique ∃!ℕ->Semiring id-f idʰ i n)
    where
    id-f : ℕ -> ℕ
    id-f = (\n -> n)
    idʰ : Semiringʰ id-f
    idʰ = record
      { +ʰ = record
        { preserves-ε = refl
        ; preserves-∙ = \_ _ -> refl
        }
      ; *ʰ = record
        { preserves-ε = refl
        ; preserves-∙ = \_ _ -> refl
        }
      }
