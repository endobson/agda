{-# OPTIONS --cubical --safe --exact-split #-}

open import category.base
open import category.functor

module category.constructions.comma
  {ℓOA ℓMA ℓOB ℓMB ℓOC ℓMC}
  {A : PreCategory ℓOA ℓMA}
  {B : PreCategory ℓOB ℓMB}
  {C : PreCategory ℓOC ℓMC}
  (S : Functor A C) (T : Functor B C) where

open import base
open import sigma.base
open import equality
open import hlevel

private
  module A = PreCategory A
  module B = PreCategory B
  module C = PreCategory C
  module S = Functor S
  module T = Functor T
  ℓO = ℓ-max* 3 ℓOA ℓOB ℓMC
  ℓM = ℓ-max* 3 ℓMA ℓMB ℓMC

private
  open CategoryHelpers C

  CommaSorts : CategorySorts ℓO ℓM
  CommaSorts .CategorySorts.Obj =
    Σ[ a ∈ Obj A ] Σ[ b ∈ Obj B ] C [ S.obj a , T.obj b ]
  CommaSorts .CategorySorts.Mor (a1 , b1 , h1) (a2 , b2 , h2) =
    Σ[ f ∈ A [ a1 , a2 ] ] Σ[ g ∈ B [ b1 , b2 ] ]
      (S.mor f ⋆⟨ C ⟩ h2 == h1 ⋆⟨ C ⟩ T.mor g)

  CommaOps : CategoryOps CommaSorts
  CommaOps .CategoryOps.id = (id A , id B ,
     ⋆-left (S.id _) >=>
     ⋆-left-id >=> sym ⋆-right-id >=>
     ⋆-right (sym (T.id _)))
  CommaOps .CategoryOps._⋆_ {a1 , b1 , h1} {a2 , b2 , h2} {a3 , b3 , h3}
                            (f1 , g1 , p1) (f2 , g2 , p2) =
    (f1 ⋆⟨ A ⟩ f2 , g1 ⋆⟨ B ⟩ g2 , p)
    where
    p =
      ⋆-cong (S.⋆ f1 f2) refl >=>
      ⋆-assoc >=>
      ⋆-right p2 >=>
      sym ⋆-assoc >=>
      ⋆-left p1 >=>
      ⋆-assoc >=>
      ⋆-right (sym (T.⋆ g1 g2))
  private
    module O = CategoryOps CommaOps

    ΣΣ-path : {ℓ₁ ℓ₂ ℓ₃ : Level} {A1 : Type ℓ₁} {A2 : Type ℓ₂} {B3 : A1 -> A2 -> Type ℓ₃}
              {s1 s2 : Σ[ a1 ∈ A1 ] Σ[ a2 ∈ A2 ] (B3 a1 a2)} ->
              (p1 : fst s1 == fst s2)
              (p2 : fst (snd s1) == fst (snd s2))
              (p3 : PathP (\i -> B3 (p1 i) (p2 i)) (snd (snd s1)) (snd (snd s2))) ->
              s1 == s2
    ΣΣ-path p1 p2 p3 i = p1 i , p2 i , p3 i

  CommaLaws : CategoryLaws CommaOps
  CommaLaws .CategoryLaws.⋆-left-id _ =
    ΣΣ-path (A.⋆-left-id _) (B.⋆-left-id _) (isProp->PathP (\i -> C.isSet-Mor _ _))
  CommaLaws .CategoryLaws.⋆-right-id _ =
    ΣΣ-path (A.⋆-right-id _) (B.⋆-right-id _) (isProp->PathP (\i -> C.isSet-Mor _ _))
  CommaLaws .CategoryLaws.⋆-assoc _ _ _ =
    ΣΣ-path (A.⋆-assoc _ _ _) (B.⋆-assoc _ _ _) (isProp->PathP (\i -> C.isSet-Mor _ _))
  CommaLaws .CategoryLaws.isSet-Mor =
    isSetΣ A.isSet-Mor (\a -> isSetΣ B.isSet-Mor (\b -> isProp->isSet (C.isSet-Mor _ _)))


CommaC : PreCategory ℓO ℓM
CommaC = Laws->Category CommaLaws
