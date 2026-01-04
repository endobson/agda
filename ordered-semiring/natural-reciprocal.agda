{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.natural-reciprocal where

open import additive-group
open import base
open import equality-path
open import hlevel.base
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.initial
open import semiring
open import semiring.initial
open import semiring.natural-reciprocal
open import sum
open import truncation

private
  variable
    ℓD ℓ< ℓ≤ : Level

module _ {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}}
         {{_ : ℕ->Semiring-Op D}}
         {{_ : 1/ℕ-Op D}}
         {{LO : isLinearOrder D<}}
         {{PO : isPartialOrder D≤}}
         {{CO : CompatibleOrderStr LO PO}}
         {{POA : PartiallyOrderedAdditiveStr ACM PO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{SPOA : StronglyPartiallyOrderedAdditiveStr ACM PO}}
         where
  private
    iℕ : Nat -> D
    iℕ = ℕ->Semiring

    opaque
      0≤iℕ : (n : Nat⁺) -> 0# ≤ iℕ ⟨ n ⟩
      0≤iℕ (suc n , _) =
        trans-=-≤
          (sym ℕ->Semiring-preserves-0#)
          (ℕ->Semiring-preserves-≤ zero-≤)

  opaque
    0≤1/ℕ : (n : Nat⁺) -> 0# ≤ 1/ℕ n
    0≤1/ℕ n = rep+-reflects-0≤ n (1/ℕ n) (trans-≤-= 0≤1 (sym (rep+-iℕ n)))
      where
      rep+ : (n : Nat) -> D -> D
      rep+ zero _ = 0#
      rep+ (suc n) x = x + (rep+ n x)

      rep+-reflects-≮0 : ∀ (n : Nat) -> Pos' n -> (x : D) -> rep+ n x ≮ 0# -> x ≮ 0#
      rep+-reflects-≮0' : ∀ (n : Nat) -> Pos' n -> (x : D) -> rep+ n x ≮ 0# -> x < 0# ->
                          (x < (x + rep+ (pred n) x)) -> Bot
      rep+-reflects-≮0 (zero) ()
      rep+-reflects-≮0 (suc zero)      _ _ x+0≮0  x<0 = x+0≮0 (trans-=-< +-right-zero x<0)
      rep+-reflects-≮0 (suc n@(suc _)) _ x x+nx≮0 x<0 =
        unsquash isPropBot (∥-map (either case₁ x+nx≮0) (comparison-< _ _ _ x<0))
        where
        case₁ : (x < (x + rep+ n x)) -> Bot
        case₁ = rep+-reflects-≮0' (suc n) tt x x+nx≮0 x<0

      rep+-reflects-≮0' (zero) ()
      rep+-reflects-≮0' (suc zero)      _ _ x+0≮0  x<0 _ = x+0≮0 (trans-=-< +-right-zero x<0)
      rep+-reflects-≮0' (suc n@(suc _)) _ x x+0≮0  x<0 x<x+nx = rep+-reflects-≮0 n tt x rec-≮ x<0
        where
        rec-≮ : (rep+ n x) ≮ 0#
        rec-≮ = convert-≤ (+₁-reflects-≤ (trans-=-≤ +-right-zero (weaken-< x<x+nx)))

      rep+-reflects-0≤ : ∀ (n : Nat⁺) x -> 0# ≤ rep+ ⟨ n ⟩ x -> 0# ≤ x
      rep+-reflects-0≤ (n , pn) x 0≤nx =
        convert-≮ (rep+-reflects-≮0 n pn x (convert-≤ 0≤nx))

      rep+-path : ∀ n x -> rep+ n x == iℕ n * x
      rep+-path zero x =
        sym (*-left ℕ->Semiring-preserves-0# >=> *-left-zero)
      rep+-path (suc n) x =
        sym (*-left (Semiringʰ.preserves-+ ℕ->Semiringʰ 1 n >=>
                     +-left ℕ->Semiring-preserves-1#) >=>
             *-distrib-+-right >=>
             +-left *-left-one >=>
             +-right (sym (rep+-path n x)))

      rep+-iℕ : ∀ (n : Nat⁺) -> rep+ ⟨ n ⟩ (1/ℕ n) == 1#
      rep+-iℕ n⁺@(n , _) = rep+-path n (1/ℕ n⁺) >=> ℕ-1/ℕ-path n⁺

    1/ℕ≤1 : (n : Nat⁺) -> 1/ℕ n ≤ 1#
    1/ℕ≤1 n@(suc n' , _) =
      trans-=-≤ (sym +-right-zero) (trans-≤-= (+₁-preserves-≤ 0≤n'/n) 1/n+n'/n=1)

      where
      0≤n' : 0# ≤ iℕ n'
      0≤n' = trans-=-≤ (sym ℕ->Semiring-preserves-0#) (ℕ->Semiring-preserves-≤ zero-≤)

      0≤n'/n : 0# ≤ (iℕ n' * 1/ℕ n)
      0≤n'/n = *-preserves-0≤ 0≤n' (0≤1/ℕ n)

      1/n+n'/n=1 : 1/ℕ n + (iℕ n' * 1/ℕ n) == 1#
      1/n+n'/n=1 =
        +-left (sym *-left-one) >=>
        sym *-distrib-+-right >=>
        *-left (+-left (sym ℕ->Semiring-preserves-1#) >=>
                sym (Semiringʰ.preserves-+ ℕ->Semiringʰ 1 n')) >=>
        ℕ-1/ℕ-path n


module _ {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} {{LO : isLinearOrder D<}}
         {{_ : ℕ->Semiring-Op D}}
         {{_ : 1/ℕ-Op D}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{NTO : NonTrivialLinearlyOrderedSemiringStr LOS}}
         {{SLOS : StronglyLinearlyOrderedSemiringStr S LO}}
         where
  private
    iℕ : Nat -> D
    iℕ = ℕ->Semiring

    opaque
      0<iℕ : (n : Nat⁺) -> 0# < iℕ ⟨ n ⟩
      0<iℕ (suc n , _) =
        trans-=-<
          (sym ℕ->Semiring-preserves-0#)
          (ℕ->Semiring-preserves-< zero-<)

  opaque
    0<1/ℕ : (n : Nat⁺) -> 0# < 1/ℕ n
    0<1/ℕ n = *₁-reflects-0< (asym-< (0<iℕ n)) (trans-<-= 0<1 (sym (ℕ-1/ℕ-path n)))


  opaque
    1/ℕ-flips-< : (a b : Nat⁺) -> ⟨ a ⟩ < ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
    1/ℕ-flips-< a⁺@(a' , _) b⁺@(b' , _) a'<b' =
      subst2 _<_ (sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ a⁺)) >=> *-left-one)
                 (*-right *-commute >=> sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ b⁺)) >=> *-left-one)
            a/ab<b/ab
      where
      a<b : iℕ a' < iℕ b'
      a<b = ℕ->Semiring-preserves-<  a'<b'
      1/a 1/b 1/ab : D
      1/a = 1/ℕ a⁺
      1/b = 1/ℕ b⁺
      1/ab = 1/a * 1/b
      0<1/ab : 0# < (1/a * 1/b)
      0<1/ab = *-preserves-0< (0<1/ℕ a⁺) (0<1/ℕ b⁺)
      a/ab<b/ab : (iℕ a' * (1/a * 1/b)) < (iℕ b' * (1/a * 1/b))
      a/ab<b/ab = *₂-preserves-< a<b 0<1/ab



  module _ {ℓ≤ : Level} {D≤ : Rel D ℓ≤} {{PO : isPartialOrder D≤}}
           {{POA : PartiallyOrderedAdditiveStr ACM PO}}
           {{POS : PartiallyOrderedSemiringStr S PO}}
           {{CO : CompatibleOrderStr LO PO}} where
    opaque
      1/ℕ-flips-≤ : (a b : Nat⁺) -> ⟨ a ⟩ ≤ ⟨ b ⟩ -> 1/ℕ b ≤ 1/ℕ a
      1/ℕ-flips-≤ a⁺@(a' , _) b⁺@(b' , _) a'≤b' =
        subst2 _≤_ (sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ a⁺)) >=> *-left-one)
                   (*-right *-commute >=> sym *-assoc >=> *-left (∃!-prop (∃!1/ℕ b⁺)) >=> *-left-one)
              a/ab≤b/ab
        where
        a≤b : iℕ a' ≤ iℕ b'
        a≤b = ℕ->Semiring-preserves-≤ a'≤b'
        1/a 1/b 1/ab : D
        1/a = 1/ℕ a⁺
        1/b = 1/ℕ b⁺
        1/ab = 1/a * 1/b
        0<1/ab : 0# < (1/a * 1/b)
        0<1/ab = *-preserves-0< (0<1/ℕ a⁺) (0<1/ℕ b⁺)
        a/ab≤b/ab : (iℕ a' * (1/a * 1/b)) ≤ (iℕ b' * (1/a * 1/b))
        a/ab≤b/ab = *₂-preserves-≤ a≤b (weaken-< 0<1/ab)


  opaque
    0<1/2 : 0# < 1/2
    0<1/2 = 0<1/ℕ 2⁺

    1/2<1 : 1/2 < 1#
    1/2<1 = trans-<-= (1/ℕ-flips-< 1⁺ 2⁺ refl-≤) 1/1-path
