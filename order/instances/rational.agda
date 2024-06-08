{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.rational where

open import order
open import rational
open import rational.order
open import base
open import equivalence
open import equality
open import relation
open import isomorphism
open import apartness

open import rational.order public using
 ( ℚ⁺
 ; ℚ⁻
 ; isLinearOrder-ℚ<
 ; DecidableLinearOrderStr-ℚ
 ; isPartialOrder-ℚ≤
 ; TotalOrderStr-ℚ
 ; CompatibleOrderStr-ℚ
 )

instance
  ApartLinearOrderStr-ℚ : ApartLinearOrderStr isTightApartness-ℚ# isLinearOrder-ℚ<
  ApartLinearOrderStr-ℚ = record
    { <>-equiv-# = f
    }
    where
    f : {a b : ℚ} -> (a <> b) ≃ (a # b)
    f {a} {b} = isoToEquiv (isProp->iso forward backward (isProp-<> {D = ℚ}) isProp-#)
      where
      forward : a <> b -> a # b
      forward (inj-l a<b) a=b = irrefl-path-< a=b a<b
      forward (inj-r b<a) a=b = irrefl-path-< (sym a=b) b<a
      backward : a # b -> a <> b
      backward ¬a=b =
        case (trichotomous-ℚ< a b) of
          (\{ (tri< a<b _ _) -> inj-l a<b
            ; (tri= _ a=b _) -> bot-elim (¬a=b a=b)
            ; (tri> _ _ b<a) -> inj-r b<a
            })
