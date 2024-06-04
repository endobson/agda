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
    opaque
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

  module _ {ℓI ℓS : Level} {I : Type ℓI} {S : Subtype I ℓS} {DetS : Detachable S} where
    opaque
      indicator-=1 : {i : I} -> ⟨ S i ⟩ -> indicator S DetS i == 1#
      indicator-=1 s = proj₁ (∃!-prop (∃!indicator S DetS)) (_ , s)

      indicator-=0 : {i : I} -> ¬ ⟨ S i ⟩ -> indicator S DetS i == 0#
      indicator-=0 s = proj₂ (∃!-prop (∃!indicator S DetS)) (_ , s)

      indicator-= : {i j : I} ->
        (⟨ S i ⟩ -> ⟨ S j ⟩) ->
        (⟨ S j ⟩ -> ⟨ S i ⟩) ->
        indicator S DetS i == indicator S DetS j
      indicator-= {i} {j} Si->Sj Sj->Si = case (DetS i) of
        \{ (yes s) -> indicator-=1 s >=> sym (indicator-=1 (Si->Sj s))
         ; (no s) -> indicator-=0 s >=> sym (indicator-=0 (\s' -> s (Sj->Si s')))
         }

  module _ {ℓ< ℓ≤ : Level} {D< : Rel D ℓ<} {D≤ : Rel D ℓ≤}
           {LO : isLinearOrder D<}
           {PO : isPartialOrder D≤}
           {{LOS : LinearlyOrderedSemiringStr S LO}}
           {{CO : CompatibleOrderStr LO PO}}
           where
    private
      instance
        ILO = LO
        IPO = PO

    module _ {ℓI ℓS : Level} {I : Type ℓI} {S : Subtype I ℓS} {DetS : Detachable S}
      where
      opaque
        indicator-≤1 : ∀ {i : I} -> indicator S DetS i ≤ 1#
        indicator-≤1 {i} = case (DetS i) of
          \{ (yes s) -> path-≤ (indicator-=1 s)
           ; (no ¬s) -> trans-=-≤ (indicator-=0 ¬s) 0≤1
           }

        indicator-0≤ : ∀ {i : I} -> 0# ≤ indicator S DetS i
        indicator-0≤ {i} = case (DetS i) of
          \{ (yes s) -> trans-≤-= 0≤1 (sym (indicator-=1 s))
           ; (no ¬s) -> path-≤ (sym (indicator-=0 ¬s))
           }

    module _ {ℓI ℓS1 ℓS2 : Level} {I : Type ℓI}
             {S1 : Subtype I ℓS1} {DetS1 : Detachable S1}
             {S2 : Subtype I ℓS2} {DetS2 : Detachable S2}
             where
      opaque
        indicator-≤ : (∀ i -> ⟨ S1 i ⟩ -> ⟨ S2 i ⟩) -> {i : I} ->
                      indicator S1 DetS1 i ≤ indicator S2 DetS2 i
        indicator-≤ S1->S2 {i} = handle (DetS1 i)
          where
          handle : Dec ⟨ S1 i ⟩ -> indicator S1 DetS1 i ≤ indicator S2 DetS2 i
          handle (yes s1) =
            path-≤ (indicator-=1 s1 >=> sym (indicator-=1(S1->S2 i s1)))
          handle (no ¬s1) =
            trans-=-≤ (indicator-=0 ¬s1) indicator-0≤
