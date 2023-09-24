{-# OPTIONS --cubical --safe --exact-split #-}

module category.bicategory where

open import base
open import category.base renaming (Obj to Obj' ; id to id')
open import category.functor
open import category.natural-transformation
open import category.constructions.product
open import category.constructions.triple-product
open import category.natural-isomorphism
open import equality-path

module _ {ℓO ℓM : Level} {C12 C23 C34 C13 C14 : PreCategory ℓO ℓM}
         (F : BiFunctor C12 C23 C13) (G : BiFunctor C13 C34 C14) where
  private
    module F = Functor F
    module G = Functor G

  LeftBiasedDoubleApplicationFunctor : Functor (TripleCat C12 C23 C34) C14
  LeftBiasedDoubleApplicationFunctor =
    record
    { obj = \(triple o1 o2 o3) -> G.obj (F.obj (o1 , o2) , o3)
    ; mor = \(triple m1 m2 m3) -> G.mor (F.mor (m1 , m2 ) , m3)
    ; id = \_ -> cong (\x -> G.mor (x , _)) (F.id _) >=> (G.id _)
    ; ⋆ = \f g -> cong (\x -> G.mor (x , _)) (F.⋆ _ _) >=> (G.⋆ _ _)
    }

module _ {ℓO ℓM : Level} {C12 C23 C34 C24 C14 : PreCategory ℓO ℓM}
         (F : BiFunctor C23 C34 C24) (G : BiFunctor C12 C24 C14) where
  private
    module F = Functor F
    module G = Functor G

  RightBiasedDoubleApplicationFunctor : Functor (TripleCat C12 C23 C34) C14
  RightBiasedDoubleApplicationFunctor =
    record
    { obj = \(triple o1 o2 o3) -> G.obj (o1 , F.obj (o2 , o3))
    ; mor = \(triple m1 m2 m3) -> G.mor (m1 , F.mor (m2 , m3))
    ; id = \_ -> cong (\x -> G.mor (_ , x)) (F.id _) >=> (G.id _)
    ; ⋆ = \f g -> cong (\x -> G.mor (_ , x)) (F.⋆ _ _) >=> (G.⋆ _ _)
    }


record PreBiCategory (ℓObj ℓ1Cell ℓ2Cell : Level) : Type (ℓ-suc (ℓ-max* 3 ℓObj ℓ1Cell ℓ2Cell)) where
  field
    Obj : Type ℓObj
    Mor : (s t : Obj) -> PreCategory ℓ1Cell ℓ2Cell

  1Cell : (s t : Obj) -> Type ℓ1Cell
  1Cell s t = Obj' (Mor s t)
  2Cell : {s t : Obj} -> (f g : 1Cell s t) -> Type ℓ2Cell
  2Cell {s} {t} f g = (Mor s t) [ f , g ]

  field
    id₁ : (s : Obj) -> 1Cell s s
    ⊗ : {s t u : Obj} -> BiFunctor (Mor s t) (Mor t u) (Mor s u)

  id₂ : {s t : Obj} -> (f : 1Cell s t) -> 2Cell f f
  id₂ {s} {t} f = idᵉ (Mor s t) f

  field
    unitorˡ : (s t : Obj) -> NaturalIsomorphism (appˡ ⊗ (id₁ s)) (idF (Mor s t))
    unitorʳ : (s t : Obj) -> NaturalIsomorphism (appʳ ⊗ (id₁ t)) (idF (Mor s t))
    associator : (s t u v : Obj) ->
      NaturalIsomorphism
        (LeftBiasedDoubleApplicationFunctor (⊗ {s} {t} {u}) (⊗ {s} {u} {v}))
        (RightBiasedDoubleApplicationFunctor (⊗ {t} {u} {v}) (⊗ {s} {t} {v}))

  _⊗₁_ : {s t u : Obj} -> 1Cell s t -> 1Cell t u -> 1Cell s u
  f ⊗₁ g = F-obj ⊗ (f , g)

  _⊗₂_ : {s t u : Obj} {f g : 1Cell s t} {h i : 1Cell t u} ->
         2Cell f g -> 2Cell h i -> 2Cell (f ⊗₁ h) (g ⊗₁ i)
  c ⊗₂ d = F-mor ⊗ (c , d)

  _⋆_ : {s t : Obj} {f g h : 1Cell s t} -> 2Cell f g -> 2Cell g h -> 2Cell f h
  _⋆_ {s} {t} c d = c ⋆⟨ Mor s t ⟩ d

  _▶_ : {s t u : Obj} {f g : 1Cell s t} -> 2Cell f g -> (h : 1Cell t u) ->
        2Cell (f ⊗₁ h) (g ⊗₁ h)
  n ▶ h = n ⊗₂ (id₂ h)

  _◀_ : {s t u : Obj} {f g : 1Cell t u} -> (h : 1Cell s t) -> 2Cell f g ->
        2Cell (h ⊗₁ f) (h ⊗₁ g)
  h ◀ n = (id₂ h) ⊗₂ n


  λ⇒ : {s t : Obj} {f : 1Cell s t} -> 2Cell (id₁ s ⊗₁ f) f
  λ⇒ {s} {t} {f} = NT-obj (fst (unitorˡ s t)) f
  ρ⇒ : {s t : Obj} {f : 1Cell s t} -> 2Cell (f ⊗₁ id₁ t) f
  ρ⇒ {s} {t} {f} = NT-obj (fst (unitorʳ s t)) f

  α⇒ : {s t u v : Obj} {f : 1Cell s t} {g : 1Cell t u} {h : 1Cell u v} ->
       2Cell ((f ⊗₁ g) ⊗₁ h) (f ⊗₁ (g ⊗₁ h))
  α⇒ {s} {t} {u} {v} {f} {g} {h} = NT-obj (fst (associator s t u v)) (triple f g h)

  field
    triangle :
      ∀ {s t u : Obj} {f : 1Cell s t} {g : 1Cell t u} ->
      Path (2Cell ((f ⊗₁ id₁ t) ⊗₁ g) (f ⊗₁ g)) (α⇒ ⋆ (f ◀ λ⇒)) (ρ⇒ ▶ g)

    pentagon :
      ∀ {o1 o2 o3 o4 o5}
        {f : 1Cell o1 o2} {g : 1Cell o2 o3} {h : 1Cell o3 o4} {i : 1Cell o4 o5} ->
        Path (2Cell (((f ⊗₁ g) ⊗₁ h) ⊗₁ i) (f ⊗₁ (g ⊗₁ (h ⊗₁ i))))
         (α⇒ ⋆ α⇒) (((α⇒ ▶ i) ⋆ α⇒) ⋆ (f ◀ α⇒))



module BiCategoryHelpers {ℓO ℓ1 ℓ2 : Level} (C : PreBiCategory ℓO ℓ1 ℓ2) where
  open PreBiCategory public hiding
    ( Obj
    ; Mor
    )
