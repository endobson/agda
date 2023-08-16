{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.decidable where

open import additive-group
open import base
open import equality
open import order
open import ordered-semiring
open import semiring
open import sum
open import relation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D}  {S : Semiring ACM}
         {O : isLinearOrder D<} {{LOS : LinearlyOrderedSemiringStr S O}}
         {{DLO : DecidableLinearOrderStr O}} where
  private
    instance
      IACM = ACM
      IS = S
      IO = O

  StronglyLinearlyOrderedSemiringStr-Dec< : StronglyLinearlyOrderedSemiringStr S O
  StronglyLinearlyOrderedSemiringStr-Dec< = record
    { *₁-fully-reflects-< = *₁-fully-reflects-<'
    }
    where
    *₁-fully-reflects-<' : {a b c : D} -> (a * b) < (a * c) ->
        (b < c × 0# < a) ⊎ (c < b × a < 0#)
    *₁-fully-reflects-<' {a} {b} {c} ab<ac =
      handle (trichotomous-< b c) (trichotomous-< 0# a)
      where
      handle : Tri< b c -> Tri< 0# a -> _
      handle (tri= _ b=c _) _ = bot-elim (irrefl-path-< (cong (a *_) b=c) ab<ac)
      handle (tri< _ _ _) (tri= _ 0=a _) =
        bot-elim (irrefl-< (subst2 _<_ (*-left (sym 0=a) >=> *-left-zero)
                                       (*-left (sym 0=a) >=> *-left-zero) ab<ac))
      handle (tri> _ _ _) (tri= _ 0=a _) =
        bot-elim (irrefl-< (subst2 _<_ (*-left (sym 0=a) >=> *-left-zero)
                                       (*-left (sym 0=a) >=> *-left-zero) ab<ac))
      handle (tri< b<c _ _) (tri< 0<a _ _) = inj-l (b<c , 0<a)
      handle (tri> _ _ c<b) (tri> _ _ a<0) = inj-r (c<b , a<0)
      handle (tri< b<c _ _) (tri> _ _ a<0) =
        bot-elim (asym-< ab<ac (*₁-flips-< a<0 b<c))
      handle (tri> _ _ c<b) (tri< 0<a _ _) =
        bot-elim (asym-< ab<ac (*₁-preserves-< 0<a c<b))


module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{CO : CompatibleOrderStr LO PO}}
         {{POS : PartiallyOrderedSemiringStr S PO}}
         {{LOS : LinearlyOrderedSemiringStr S LO}}
         {{DLO : DecidableLinearOrderStr LO}}
         where
  private
    instance
      IACM = ACM
      IS = S
      ILO = LO
      IPO = PO

  StronglyPartiallyOrderedSemiringStr-Dec< : StronglyPartiallyOrderedSemiringStr S LO PO
  StronglyPartiallyOrderedSemiringStr-Dec< = record
    { *₁-reflects-≤ = *₁-reflects-≤'
    ; *₁-flip-reflects-≤ = *₁-flip-reflects-≤'
    }
    where
    *₁-reflects-≤' : {a b c : D} -> 0# < a -> (a * b) ≤ (a * c) -> b ≤ c
    *₁-reflects-≤' {a} {b} {c} 0<a ab≤ac =
      proj-¬l (split-< c b) (\c<b -> irrefl-< (trans-<-≤ (*₁-preserves-< 0<a c<b) ab≤ac))

    *₁-flip-reflects-≤' : {a b c : D} -> a < 0# -> (a * b) ≤ (a * c) -> c ≤ b
    *₁-flip-reflects-≤' {a} {b} {c} a<0 ab≤ac =
      proj-¬l (split-< b c) (\b<c -> irrefl-< (trans-<-≤ (*₁-flips-< a<0 b<c) ab≤ac))
