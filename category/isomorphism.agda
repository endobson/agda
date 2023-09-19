{-# OPTIONS --cubical --safe --exact-split #-}

module category.isomorphism where

open import base
open import category.base
open import category.morphism
open import cubical hiding (i0 ; i1)
open import equality
open import hlevel

private
  variable
    ℓO ℓM : Level

record isIso (C : PreCategory ℓO ℓM) {x y : C .Obj} (mor : C [ x , y ]) : Type ℓM where
  constructor is-iso
  field
    inv : C [ y , x ]
    sec : inv ⋆⟨ C ⟩ mor == C .id
    ret : mor ⋆⟨ C ⟩ inv == C .id

isProp-isIso : {C : PreCategory ℓO ℓM} -> {x y : C .Obj} {mor : C [ x , y ]} -> isProp (isIso C mor)
isProp-isIso {C = C} {x} {y} {mor} i1 i2 = (\i -> record
    { inv = ip i
    ; sec = ans-sec i
    ; ret = ans-ret i
    })
  where
  module C = PreCategory C
  module i1 = isIso i1
  module i2 = isIso i2

  ip : i1.inv == i2.inv
  ip = sym (C.⋆-left-id _) >=>
       cong (C._⋆ i1.inv) (sym i2.sec) >=>
       C.⋆-assoc i2.inv mor i1.inv >=>
       cong (i2.inv C.⋆_) i1.ret >=>
       (C.⋆-right-id i2.inv)

  ret-line : I -> Type _
  ret-line i = mor ⋆⟨ C ⟩ ip i == C.id
  ans-ret : PathP ret-line i1.ret i2.ret
  ans-ret = isProp->PathP (\i -> (C.isSet-Mor _ _))

  sec-line : I -> Type _
  sec-line i = ip i ⋆⟨ C ⟩ mor == C.id
  ans-sec : PathP sec-line i1.sec i2.sec
  ans-sec = isProp->PathP (\i -> (C.isSet-Mor _ _))

module _ {ℓOC ℓMC ℓOD ℓMD} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD} where
  module _ (F : Functor C D) where
    private
      module F = Functor F
    functor-preserves-isIso :
      {a b : Obj C} -> {m : C [ a , b ]} ->
      isIso C m -> isIso D (F.mor m)
    functor-preserves-isIso {m = m} (is-iso m-inv m-sec m-ret) = record
      { inv = F.mor m-inv
      ; sec =
        sym (F.⋆ m-inv m) >=>
        cong F.mor m-sec >=>
        F.id _
      ; ret =
        sym (F.⋆ m m-inv) >=>
        cong F.mor m-ret >=>
        F.id _
      }

module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  open CategoryHelpers C

  isIso-id : {a : Obj C} -> isIso C (idᵉ C a)
  isIso-id = is-iso (id C) ⋆-id² ⋆-id²

module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} where
  open CategoryHelpers C

  isIso->isEpi : {a b : Obj C} {f : C [ a , b ]} -> isIso C f -> isEpi C f
  isIso->isEpi {a} {b} {f} (is-iso inv sec ret) {c} {g₁} {g₂} p =
    sym ⋆-left-id >=>
    (\i -> sec (~ i) ⋆ g₁) >=>
    ⋆-assoc >=>
    (\i -> inv ⋆ p i) >=>
    sym ⋆-assoc >=>
    (\i -> sec i ⋆ g₂) >=>
    ⋆-left-id

  isIso->isMono : {a b : Obj C} {f : C [ a , b ]} -> isIso C f -> isMono C f
  isIso->isMono {a} {b} {f} (is-iso inv sec ret) {c} {g₁} {g₂} p =
    sym ⋆-right-id >=>
    (\i -> g₁ ⋆ ret (~ i)) >=>
    sym ⋆-assoc >=>
    (\i -> p i ⋆ inv) >=>
    ⋆-assoc >=>
    (\i -> g₂ ⋆ ret i) >=>
    ⋆-right-id

  sym-isIso : {a b : Obj C} {m : C [ a , b ]} -> (i : isIso C m) -> isIso C (isIso.inv i)
  sym-isIso {m = m} (is-iso inv sec ret) = (is-iso m ret sec)

  isIso-⋆ : {a b c : Obj C} {m1 : C [ a , b ]} {m2 : C [ b , c ]} ->
            isIso C m1 -> isIso C m2 -> isIso C (m1 ⋆ m2)
  isIso-⋆ (is-iso i₁ sec₁ ret₁) (is-iso i₂ sec₂ ret₂) = is-iso (i₂ ⋆ i₁) sec ret
    where
    sec = ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> ⋆-left sec₁ >=> ⋆-left-id) >=> sec₂
    ret = ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> ⋆-left ret₂ >=> ⋆-left-id) >=> ret₁
