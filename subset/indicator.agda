{-# OPTIONS --cubical --safe --exact-split #-}

module subset.indicator where

open import additive-group
open import base
open import equality
open import funext
open import hlevel
open import order
open import ordered-semiring
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

  module _ {ℓ< ℓ≤ : Level}
           {LO : LinearOrderStr D ℓ<}
           {PO : PartialOrderStr D ℓ≤}
           {{LOS : LinearlyOrderedSemiringStr S LO}}
           {{CO : CompatibleOrderStr LO PO}}
           where
    private
      instance
        ILO = LO
        IPO = PO

    module _ {ℓI ℓS : Level} {I : Type ℓI} (S : Subtype I ℓS) (DetS : Detachable S)
      where
      abstract
        indicator-≤1 : ∀ (i : I) -> indicator S DetS i ≤ 1#
        indicator-≤1 i = case (DetS i) of
          \{ (yes s) -> path-≤ (proj₁ (∃!-prop (∃!indicator S DetS)) (i , s))
           ; (no ¬s) -> trans-=-≤ (proj₂ (∃!-prop (∃!indicator S DetS)) (i , ¬s)) (convert-≮ 1≮0)
           }

        indicator-0≤ : ∀ (i : I) -> 0# ≤ indicator S DetS i
        indicator-0≤ i = case (DetS i) of
          \{ (yes s) -> trans-≤-= (convert-≮ 1≮0) (sym (proj₁ (∃!-prop (∃!indicator S DetS)) (i , s)))
           ; (no ¬s) -> path-≤ (sym (proj₂ (∃!-prop (∃!indicator S DetS)) (i , ¬s)))
           }


    module _ {ℓI ℓS1 ℓS2 : Level} {I : Type ℓI}
             (S1 : Subtype I ℓS1) (DetS1 : Detachable S1)
             (S2 : Subtype I ℓS2) (DetS2 : Detachable S2)
             where
      abstract
        indicator-≤ : (∀ i -> ⟨ S1 i ⟩ -> ⟨ S2 i ⟩) -> (i : I) ->
                      indicator S1 DetS1 i ≤ indicator S2 DetS2 i
        indicator-≤ S1->S2 i = handle (DetS1 i)
          where
          handle : Dec ⟨ S1 i ⟩ -> indicator S1 DetS1 i ≤ indicator S2 DetS2 i
          handle (yes s1) =
            path-≤ ((proj₁ (∃!-prop (∃!indicator S1 DetS1)) (i , s1)) >=>
                    sym (proj₁ (∃!-prop (∃!indicator S2 DetS2)) (i , (S1->S2 i s1))))
          handle (no ¬s1) =
            trans-=-≤ (proj₂ (∃!-prop (∃!indicator S1 DetS1)) (i , ¬s1))
                      (indicator-0≤ S2 DetS2 i)
