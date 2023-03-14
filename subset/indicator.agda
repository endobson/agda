{-# OPTIONS --cubical --safe --exact-split #-}

module subset.indicator where

open import additive-group
open import base
open import equality
open import funext
open import hlevel
open import relation
open import semiring
open import sigma.base
open import subset
open import truncation

module _ {ℓD : Level} {D : Type ℓD}
         {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}}
         where
  private
    instance
      IACM = ACM

    isSet-D : isSet D
    isSet-D = Semiring.isSet-Domain S

  module _ {ℓI ℓS : Level} {I : Type ℓI} (S : Subtype I ℓS) (DetS : Detachable S) where
    abstract
      ∃!indicator : ∃![ f ∈ (I -> D) ]
                     ((∀ (s : ∈-Subtype S) -> f (fst s) == 1#) ×
                      (∀ (s : ∉-Subtype S) -> f (fst s) == 0#))
      ∃!indicator = (f , ∈-case , ∉-case) , isProp-f _
        where
        decf : {i : I} -> Dec (⟨ S i ⟩) -> D
        decf (yes _) = 1#
        decf (no _) = 0#
        f : I -> D
        f i = decf (DetS i)
        ∈-case : (∀ (s : ∈-Subtype S) -> f (fst s) == 1#)
        ∈-case (i , s) = cong decf (isPropDec (snd (S i)) (DetS i) (yes s))
        ∉-case : (∀ (s : ∉-Subtype S) -> f (fst s) == 0#)
        ∉-case (i , ¬s) = cong decf (isPropDec (snd (S i)) (DetS i) (no ¬s))
        isProp-f : isProp (Σ[ f ∈ (I -> D) ]
                             ((∀ (s : ∈-Subtype S) -> f (fst s) == 1#) ×
                             (∀ (s : ∉-Subtype S) -> f (fst s) == 0#)))
        isProp-f (f , ∈f , ∉f) (g , ∈g , ∉g) =
          ΣProp-path (isProp× (isPropΠ \_ -> isSet-D _ _) (isPropΠ \_ -> isSet-D _ _))
            (funExt \i -> case (DetS i) of
              \{ (yes s) -> ∈f (i , s) >=> sym (∈g (i , s))
               ; (no ¬s) -> ∉f (i , ¬s) >=> sym (∉g (i , ¬s))
               })

    indicator : I -> D
    indicator = ∃!-val ∃!indicator
