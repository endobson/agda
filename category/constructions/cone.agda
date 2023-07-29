{-# OPTIONS --cubical --safe --exact-split #-}

open import category.base

module category.constructions.cone
  {ℓOJ ℓMJ ℓOC ℓMC}
  {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
  (D : Diagram J C) where

open import base
open import cubical
open import equality-path hiding (J)
open import equivalence
open import funext
open import hlevel
open import isomorphism
open import relation

private
  ℓO : Level
  ℓO = (ℓ-max* 4 ℓOJ ℓMJ ℓOC ℓMC)
  ℓM : Level
  ℓM = (ℓ-max ℓOJ ℓMC)

record ConeStr (v : Obj C) : Type (ℓ-max* 3 ℓOJ ℓMJ ℓMC) where
  private
    module D = Functor D

  field
    component : (j : Obj J) -> C [ v , D.obj j ]
    component-compose :
      {j1 j2 : Obj J} -> (f : J [ j1 , j2 ]) ->
      component j1 ⋆⟨ C ⟩ (D.mor f) == component j2

Cone : Type ℓO
Cone = Σ (Obj C) ConeStr

record ConeMor (s t : Cone) : Type ℓM where
  constructor cone-mor
  private
    os = fst s
    ot = fst t
    ss = snd s
    st = snd t

  field
    f : C [ os , ot ]
    component : ∀ j -> ConeStr.component ss j == f ⋆⟨ C ⟩ ConeStr.component st j

private
  ConeMor' : (s t : Cone) -> Type ℓM
  ConeMor' (os , ss) (ot , st) =
    Σ[ f ∈ C [ os , ot ] ] (∀ j -> ConeStr.component ss j == f ⋆⟨ C ⟩ ConeStr.component st j)

  isSet-ConeMor' : {s t : Cone} -> isSet (ConeMor' s t)
  isSet-ConeMor' = isSetΣ (isSet-Mor C) (\f -> isSetΠ (\j -> isProp->isSet (isSet-Mor C _ _)))

  ConeMor'≃ConeMor : {s t : Cone} -> (ConeMor' s t) ≃ (ConeMor s t)
  ConeMor'≃ConeMor {s} {t} = isoToEquiv i
    where
    i : Iso (ConeMor' s t) (ConeMor s t)
    i .Iso.fun (f , c) = cone-mor f c
    i .Iso.inv (cone-mor f c) = f , c
    i .Iso.rightInv _ = refl
    i .Iso.leftInv _ = refl

  isSet-ConeMor : {s t : Cone} -> isSet (ConeMor s t)
  isSet-ConeMor {s} {t} = ≃-isSet ConeMor'≃ConeMor (isSet-ConeMor' {s} {t})


private
  ConeSorts : CategorySorts ℓO ℓM
  ConeSorts .CategorySorts.Obj = Cone
  ConeSorts .CategorySorts.Mor = ConeMor

  ConeOps : CategoryOps ConeSorts
  ConeOps .CategoryOps.id = record
    { f = id C
    ; component = \ _ -> sym (PreCategory.⋆-left-id C _)
    }
  ConeOps .CategoryOps._⋆_ (cone-mor f1 p1) (cone-mor f2 p2) = record
    { f = f1 ⋆⟨ C ⟩ f2
    ; component = \ j -> p1 j >=> cong (\m -> f1 ⋆⟨ C ⟩ m) (p2 j) >=>
                         sym (PreCategory.⋆-assoc C _ _ _)
    }

  ConeLaws : CategoryLaws ConeOps
  ConeLaws .CategoryLaws.⋆-left-id _ =
    cong2-dep cone-mor m-path c-path
    where
    m-path = PreCategory.⋆-left-id C _
    c-path = funExtP (\j -> isProp->PathP (\i -> PreCategory.isSet-Mor C _ _))
  ConeLaws .CategoryLaws.⋆-right-id _ =
    cong2-dep cone-mor m-path c-path
    where
    m-path = PreCategory.⋆-right-id C _
    c-path = funExtP (\j -> isProp->PathP (\i -> PreCategory.isSet-Mor C _ _))
  ConeLaws .CategoryLaws.⋆-assoc _ _ _ =
    cong2-dep cone-mor m-path c-path
    where
    m-path = PreCategory.⋆-assoc C _ _ _
    c-path = funExtP (\j -> isProp->PathP (\i -> PreCategory.isSet-Mor C _ _))
  ConeLaws .CategoryLaws.isSet-Mor = isSet-ConeMor

ConeC : PreCategory ℓO ℓM
ConeC = Laws->Category ConeLaws
