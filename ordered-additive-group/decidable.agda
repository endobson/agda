{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.decidable where

open import additive-group
open import base
open import equality
open import order
open import ordered-additive-group
open import sum
open import relation

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {{ACM : AdditiveCommMonoid D}}
         {O : isLinearOrder D<} {{DLO : DecidableLinearOrderStr O}} where
  private
    instance
      IO = O

  LinearlyOrderedAdditiveStr-Dec< :
    ({a b c : D} -> b < c -> (a + b) < (a + c)) ->
    LinearlyOrderedAdditiveStr ACM O
  LinearlyOrderedAdditiveStr-Dec< +₁-preserves-< = record
    { +₁-preserves-< = +₁-preserves-<
    ; +₁-reflects-< = \ab<ac -> stable-< (+₁-reflects-<' ab<ac)
    }
    where

    +₁-reflects-<' : {a b c : D} -> (a + b) < (a + c) -> ¬ (¬ (b < c))
    +₁-reflects-<' {a} {b} {c} ab<ac b≮c = irrefl-path-< (cong (a +_) b=c) ab<ac
      where
      c≮b : c ≮ b
      c≮b c<b = asym-< ab<ac (+₁-preserves-< c<b)
      b=c : b == c
      b=c = connected-< b≮c c≮b

module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D}
         {LO : isLinearOrder D<} {PO : isPartialOrder D≤}
         {{CO : CompatibleOrderStr LO PO}}
         {{LOS : LinearlyOrderedAdditiveStr ACM LO}}
         {{DLO : DecidableLinearOrderStr LO}}
         where
  private
    instance
      IACM = ACM
      ILO = LO
      IPO = PO

  StronglyPartiallyOrderedAdditiveStr-Dec< : StronglyPartiallyOrderedAdditiveStr ACM PO
  StronglyPartiallyOrderedAdditiveStr-Dec< = record
    { +₁-reflects-≤ = +₁-reflects-≤'
    }
    where
    +₁-reflects-≤' : {a b c : D} -> (a + b) ≤ (a + c) -> b ≤ c
    +₁-reflects-≤' {a} {b} {c} ab≤ac =
      proj-¬l (split-< c b) (\c<b -> irrefl-< (trans-<-≤ (+₁-preserves-< c<b) ab≤ac))
