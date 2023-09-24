{-# OPTIONS --cubical --safe --exact-split #-}

open import category.base
open import category.functor

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
open import sigma.base

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

-- Paths for cones and related objects

cone-str-pathp :
  {o1 o2 : Obj C} {s1 : ConeStr o1} {s2 : ConeStr o2} ->
  (op : o1 == o2) ->
  (cps : ∀ j -> PathP (\i -> C [ op i , F-obj D j ])
                (ConeStr.component s1 j)
                (ConeStr.component s2 j)) ->
  PathP (\i -> ConeStr (op i)) s1 s2
cone-str-pathp op cps i .ConeStr.component j = cps j i
cone-str-pathp {s1 = s1} {s2} op cps i .ConeStr.component-compose {j1} {j2} m = ans i
  where
  ans : PathP (\i -> cps j1 i ⋆⟨ C ⟩ F-mor D m == cps j2 i)
              (ConeStr.component-compose s1 m)
              (ConeStr.component-compose s2 m)
  ans = isProp->PathP (\i -> isSet-Mor C _ _)

cone-str-path : {o : Obj C} -> {s1 s2 : ConeStr o} ->
                (∀ j -> ConeStr.component s1 j == ConeStr.component s2 j) ->
                s1 == s2
cone-str-path = cone-str-pathp refl

cone-path : {c1 c2 : Cone} ->
  (op : fst c1 == fst c2) ->
  (cps : ∀ j -> PathP (\i -> C [ op i , F-obj D j ])
                (ConeStr.component (snd c1) j)
                (ConeStr.component (snd c2) j)) ->
  c1 == c2
cone-path op cps = Σ-path op (cone-str-pathp op cps)

abstract
  isSet-ConeStr : {o : Obj C} -> isSet (ConeStr o)
  isSet-ConeStr s1 s2 p1 p2 =
    \i j -> record { component = cp i j ; component-compose = ccp i j }
    where
    module _ where
      cp = isSet->Square (isSetΠ (\j -> isSet-Mor C))

      ccp = isSet->SquarePᵉ
              (\i k -> isSetΠⁱ (\j1 -> (isSetΠⁱ (\j2 -> isSetΠ (\f -> isProp->isSet
                       (isSet-Mor C (cp i k j1 ⋆⟨ C ⟩ (F-mor D f)) (cp i k j2)))))))
            (cong ConeStr.component-compose p1) (cong ConeStr.component-compose p2)
            refl refl

cone-path-path : {c1 c2 : Cone} -> (p1 p2 : c1 == c2) ->
                 (cong fst p1) == (cong fst p2) ->
                 p1 == p2
cone-path-path {c1} {c2} p1 p2 op i j .fst = op i j
cone-path-path {c1} {c2} p1 p2 op i j .snd =
  isSet->SquarePᵉ (\i j -> isSet-ConeStr {op i j})
    (cong snd p1) (cong snd p2) (\i -> (snd c1)) (\i -> (snd c2)) i j
