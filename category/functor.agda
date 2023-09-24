{-# OPTIONS --cubical --safe --exact-split #-}

module category.functor where

open import base
open import category.base
open import equality-path
open import hlevel

record Functor {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
               (C : PreCategory ℓObjC ℓMorC) (D : PreCategory ℓObjD ℓMorD) :
               Type (ℓ-max* 4 ℓObjC ℓObjD ℓMorC ℓMorD) where
  no-eta-equality
  field
    obj : Obj C -> Obj D
    mor : {x y : Obj C} -> C [ x , y ] -> D [ obj x , obj y ]
    id : (x : Obj C) -> (mor (idᵉ C x)) == (id D)
    ⋆ : {x y z : Obj C} -> (f : C [ x , y ]) -> (g : C [ y , z ]) ->
         mor (f ⋆⟨ C ⟩ g) == (mor f ⋆⟨ D ⟩ mor g)

open Functor public renaming
  ( obj to F-obj
  ; mor to F-mor
  ; id to F-id
  ; ⋆ to F-⋆
  )

-- Add an alias for Diagrams.
Diagram = Functor

-- Identity Functor
idF : {ℓObjC ℓMorC : Level} (C : PreCategory ℓObjC ℓMorC) -> Functor C C
idF _ .F-obj x = x
idF _ .F-mor f = f
idF _ .F-id _ = refl
idF _ .F-⋆ f g = refl

module _ {ℓO ℓM : Level}
         {C : PreCategory ℓO ℓM} {D : PreCategory ℓO ℓM}
         {F G : Functor C D} where
  private
    module F = Functor F
    module G = Functor G

  module _ (op : ∀ c -> F.obj c == G.obj c)
           (mp : ∀ {c1 c2} (m : C [ c1 , c2 ]) ->
                   PathP (\i -> D [ op c1 i , op c2 i ]) (F.mor m) (G.mor m))
    where

    opaque
      id-p : ∀ c -> PathP (\i -> (mp (idᵉ C c) i) == (id D)) (F.id c) (G.id c)
      id-p _ = isSet->SquareP (\i j -> isSet-Mor D)

      ⋆-p : ∀ {c1 c2 c3} (m1 : C [ c1 , c2 ]) (m2 : C [ c2 , c3 ]) ->
            PathP (\i -> (mp (m1 ⋆⟨ C ⟩ m2) i) == (mp m1 i) ⋆⟨ D ⟩ (mp m2 i))
              (F.⋆ m1 m2) (G.⋆ m1 m2)
      ⋆-p _ _ = isSet->SquareP (\i j -> isSet-Mor D)

    functor-path : F == G
    functor-path i .Functor.obj c = op c i
    functor-path i .Functor.mor m = mp m i
    functor-path i .Functor.id c = id-p c i
    functor-path i .Functor.⋆ m1 m2 = ⋆-p m1 m2 i
