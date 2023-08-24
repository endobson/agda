{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.base where

open import base
open import equality
open import category.base
open import fin-algebra
open import category.constructions.product
open import category.constructions.triple-product

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (⊗ : BiFunctor C C C) where
  private
    module C = PreCategory C
    module ⊗ = Functor ⊗

    _⊗₀_ : C.Obj -> C.Obj -> C.Obj
    c1 ⊗₀ c2 = ⊗.obj (c1 , c2)

    _⊗₁_ : {x y z w : C.Obj} -> C [ x , y ] -> C [ z , w ] -> C [ (x ⊗₀ z) , (y ⊗₀ w) ]
    f ⊗₁ g = ⊗.mor (f , g)

    i0 : FinT 3
    i0 = inj-l tt
    i1 : FinT 3
    i1 = inj-r (inj-l tt)
    i2 : FinT 3
    i2 = inj-r (inj-r (inj-l tt))

  LeftBiasedDoubleApplicationFunctor : Functor (TripleCat C C C) C
  LeftBiasedDoubleApplicationFunctor = record
    { obj = \(triple o1 o2 o3) -> (o1 ⊗₀ o2 ) ⊗₀ o3
    ; mor = \(triple m1 m2 m3) -> (m1 ⊗₁ m2 ) ⊗₁ m3
    ; id = \_ -> cong (_⊗₁ id C) (⊗.id _) >=> (⊗.id _)
    ; ⋆ = \f g -> cong (_⊗₁ _) (⊗.⋆ _ _) >=> (⊗.⋆ _ _)
    }

  RightBiasedDoubleApplicationFunctor : Functor (TripleCat C C C) C
  RightBiasedDoubleApplicationFunctor = record
    { obj = \(triple o1 o2 o3) -> o1 ⊗₀ (o2 ⊗₀ o3)
    ; mor = \(triple m1 m2 m3) -> m1 ⊗₁ (m2 ⊗₁ m3)
    ; id = \_ -> cong (id C ⊗₁_) (⊗.id _) >=> (⊗.id _)
    ; ⋆ = \f g -> cong (_ ⊗₁_) (⊗.⋆ _ _) >=> (⊗.⋆ _ _)
    }

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  open CategoryHelpers C

  record MonoidalStr : Type (ℓ-max ℓO ℓM) where
    field
      ⊗ : BiFunctor C C C
      unit : Obj C
      unitorˡ : NaturalIsomorphism (appˡ ⊗ unit) (idF C)
      unitorʳ : NaturalIsomorphism (appʳ ⊗ unit) (idF C)
      associator : NaturalIsomorphism (LeftBiasedDoubleApplicationFunctor ⊗)
                                      (RightBiasedDoubleApplicationFunctor ⊗)

    _⊗₀_ : Obj C -> Obj C -> Obj C
    c1 ⊗₀ c2 = F-obj ⊗ (c1 , c2)

    _⊗₁_ : {x y z w : Obj C} -> C [ x , y ] -> C [ z , w ] -> C [ (x ⊗₀ z) , (y ⊗₀ w) ]
    f ⊗₁ g = F-mor ⊗ (f , g)

    α⇒ : {a b c : Obj C} -> C [ ( a ⊗₀ b) ⊗₀ c , a ⊗₀ (b ⊗₀ c) ]
    α⇒ {a} {b} {c} = NT-obj (fst associator) (triple a b c)

    λ⇒ : {a : Obj C} -> C [ unit ⊗₀ a , a ]
    λ⇒ {a} = NT-obj (fst unitorˡ) a

    ρ⇒ : {a : Obj C} -> C [ a ⊗₀ unit , a ]
    ρ⇒ {a} = NT-obj (fst unitorʳ) a


module MonoidalStrHelpers {ℓO ℓM : Level} {C : PreCategory ℓO ℓM}
                          (M : MonoidalStr C) where
  open MonoidalStr M public
  open CategoryHelpers C

  ⊗-distrib-⋆ :
    {a b c d e f : Obj C}
    {f-ab : C [ a , b ]} {f-bc : C [ b , c ]}
    {f-de : C [ d , e ]} {f-ef : C [ e , f ]} ->
    (f-ab ⋆ f-bc) ⊗₁ (f-de ⋆ f-ef) ==
    (f-ab ⊗₁ f-de) ⋆ (f-bc ⊗₁ f-ef)
  ⊗-distrib-⋆ = F-⋆ ⊗ _ _

  α⇐ : {a b c : Obj C} -> C [ a ⊗₀ (b ⊗₀ c) , ( a ⊗₀ b) ⊗₀ c ]
  α⇐ {a} {b} {c} = isIso.inv (snd associator (triple a b c))
  λ⇐ : {a : Obj C} -> C [ a , unit ⊗₀ a ]
  λ⇐ {a} = isIso.inv (snd unitorˡ a)
  ρ⇐ : {a : Obj C} -> C [ a , a ⊗₀ unit ]
  ρ⇐ {a} = isIso.inv (snd unitorʳ a)

  α⇒-swap : {a₁ a₂ b₁ b₂ c₁ c₂ : Obj C}
            {f : C [ a₁ , a₂ ]} {g : C [ b₁ , b₂ ]} {h : C [ c₁ , c₂ ]} ->
            Path (C [ ( a₁ ⊗₀ b₁) ⊗₀ c₁ , a₂ ⊗₀ (b₂ ⊗₀ c₂) ])
              (α⇒ ⋆ (f ⊗₁ (g ⊗₁ h))) (((f ⊗₁ g) ⊗₁ h) ⋆ α⇒)
  α⇒-swap = NT-mor (fst associator) (triple _ _ _)

  λ⇒-swap : {a b : Obj C} {f : C [ a , b ]} ->
            Path (C [ unit ⊗₀ a , b ]) (λ⇒ ⋆ f) ((id C ⊗₁ f) ⋆ λ⇒)
  λ⇒-swap = NT-mor (fst unitorˡ) _

  ρ⇒-swap : {a b : Obj C} {f : C [ a , b ]} ->
            Path (C [ a ⊗₀ unit , b ]) (ρ⇒ ⋆ f) ((f ⊗₁ id C) ⋆ ρ⇒)
  ρ⇒-swap = NT-mor (fst unitorʳ) _
