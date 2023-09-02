{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.category where

open import additive-group
open import additive-group.instances.nat
open import base
open import category.base
open import category.constructions.product
open import category.constructions.triple-product
open import category.monoidal.base
open import category.monoidal.formal.base
open import equality
open import hlevel
open import nat

record WMor (s t : WObj) : Type₀ where
  constructor wmor
  field
    length : (WObj-length s) == (WObj-length t)

isProp-WMor : {s t : WObj} -> isProp (WMor s t)
isProp-WMor (wmor l1) (wmor l2) i = wmor (isSetNat _ _ l1 l2 i)

wmor-path : {s t : WObj} {a b : WMor s t} -> a == b
wmor-path = isProp-WMor _ _

WSorts : CategorySorts ℓ-zero ℓ-zero
WSorts .CategorySorts.Obj = WObj
WSorts .CategorySorts.Mor = WMor

WOps : CategoryOps WSorts
WOps .CategoryOps.id = (wmor refl)
WOps .CategoryOps._⋆_ (wmor l1) (wmor l2) = wmor (l1 >=> l2)

WLaws : CategoryLaws WOps
WLaws .CategoryLaws.⋆-left-id _ = wmor-path
WLaws .CategoryLaws.⋆-right-id _ = wmor-path
WLaws .CategoryLaws.⋆-assoc _ _ _ = wmor-path
WLaws .CategoryLaws.isSet-Mor = isProp->isSet isProp-WMor

WCat : PreCategory ℓ-zero ℓ-zero
WCat = Laws->Category WLaws

MonoidalW : MonoidalStr WCat
MonoidalW = record
  { ⊗ = Bi-⊗
  ; unit = ε
  ; unitorˡ = unitorˡ
  ; unitorʳ = unitorʳ
  ; associator = associator
  ; triangle = wmor-path
  ; pentagon = wmor-path
  }
  where

  Bi-⊗ : BiFunctor WCat WCat WCat
  Bi-⊗ .Functor.obj (s , t) = s ⊗ t
  Bi-⊗ .Functor.mor (wmor l1 , wmor l2) = wmor (\i -> l1 i + l2 i)
  Bi-⊗ .Functor.id _ = wmor-path
  Bi-⊗ .Functor.⋆ _ _ = wmor-path

  unitorˡ : NaturalIsomorphism (appˡ {C = WCat} Bi-⊗ ε) (idF WCat)
  unitorˡ = record
    { NT-obj = \_ -> wmor +-left-zero
    ; NT-mor = \_ -> wmor-path
    } ,
    \c -> record
      { inv = wmor (sym +-left-zero)
      ; sec = wmor-path
      ; ret = wmor-path
      }

  unitorʳ : NaturalIsomorphism (appʳ {D = WCat} Bi-⊗ ε) (idF WCat)
  unitorʳ = record
    { NT-obj = \_ -> wmor +-right-zero
    ; NT-mor = \_ -> wmor-path
    } ,
    \c -> record
      { inv = wmor (sym +-right-zero)
      ; sec = wmor-path
      ; ret = wmor-path
      }

  associator : NaturalIsomorphism (LeftBiasedDoubleApplicationFunctor Bi-⊗)
                                  (RightBiasedDoubleApplicationFunctor Bi-⊗)
  associator = record
    { NT-obj = \{ (triple a b c) -> wmor (+-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c)) }
    ; NT-mor = \_ -> wmor-path
    } ,
    \{ (triple a b c) -> record
      { inv = wmor (sym (+-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c)))
      ; sec = wmor-path
      ; ret = wmor-path
      } }
