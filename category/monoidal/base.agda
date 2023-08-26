{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.base where

open import base
open import category.base
open import category.constructions.product
open import category.constructions.triple-product
open import category.zipper
open import equality
open import fin-algebra

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

    field
      triangle :
        ∀ {a b} -> Path (C [ (a ⊗₀ unit) ⊗₀ b , a ⊗₀ b ]) (α⇒ ⋆ (id C ⊗₁ λ⇒)) (ρ⇒ ⊗₁ id C)
      pentagon :
        ∀ {a b c d} -> Path (C [ (((a ⊗₀ b) ⊗₀ c) ⊗₀ d) , (a ⊗₀ (b ⊗₀ (c ⊗₀ d))) ])
           (α⇒ ⋆ α⇒)
           ((α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ α⇒))

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

  open ZReasoning C

  ⊗₁-left : {a₁ a₂ b₁ b₂ : Obj C} -> {f g : C [ a₁ , b₁ ]} {h : C [ a₂ , b₂ ]} ->
            f == g -> Path (C [ a₁ ⊗₀ a₂ , b₁ ⊗₀ b₂ ]) (f ⊗₁ h) (g ⊗₁ h)
  ⊗₁-left {h = h} p i = (p i) ⊗₁ h

  ⊗₁-right : {a₁ a₂ b₁ b₂ : Obj C} -> {f : C [ a₁ , b₁ ]} {g h : C [ a₂ , b₂ ]} ->
             g == h -> Path (C [ a₁ ⊗₀ a₂ , b₁ ⊗₀ b₂ ]) (f ⊗₁ g) (f ⊗₁ h)
  ⊗₁-right {f = f} p i = f ⊗₁ (p i)

  -- Took names of helpers from Categories library.
  -- Splits out serial composition over multiple tensor compositions

  serialize₁₂ : {a₁ a₂ b₁ b₂ : Obj C} {f : C [ a₁ , b₁ ]} {g : C [ a₂ , b₂ ]} ->
                Path (C [ a₁ ⊗₀ a₂ , b₁ ⊗₀ b₂ ]) (f ⊗₁ g) ((f ⊗₁ id C) ⋆ (id C ⊗₁ g))
  serialize₁₂ = cong2 _⊗₁_ (sym ⋆-right-id) (sym ⋆-left-id) >=> ⊗-distrib-⋆

  serialize₂₁ : {a₁ a₂ b₁ b₂ : Obj C} {f : C [ a₁ , b₁ ]} {g : C [ a₂ , b₂ ]} ->
                Path (C [ a₁ ⊗₀ a₂ , b₁ ⊗₀ b₂ ]) (f ⊗₁ g) ((id C ⊗₁ g) ⋆ (f ⊗₁ id C))
  serialize₂₁ =  cong2 _⊗₁_ (sym ⋆-left-id) (sym ⋆-right-id) >=> ⊗-distrib-⋆

  split₁ˡ : {a₁ a₂ b₁ c₁ c₂ : Obj C}
            {f : C [ a₁ , b₁ ]} {g : C [ b₁ , c₁ ]} {h : C [ a₂ , c₂ ]} ->
            (f ⋆ g) ⊗₁ h == (f ⊗₁ h) ⋆ (g ⊗₁ id C)
  split₁ˡ = ⊗₁-right (sym ⋆-right-id) >=> ⊗-distrib-⋆

  split₁ʳ : {a₁ a₂ b₁ c₁ c₂ : Obj C}
            {f : C [ a₁ , b₁ ]} {g : C [ b₁ , c₁ ]} {h : C [ a₂ , c₂ ]} ->
            (f ⋆ g) ⊗₁ h == (f ⊗₁ id C) ⋆ (g ⊗₁ h)
  split₁ʳ = ⊗₁-right (sym ⋆-left-id) >=> ⊗-distrib-⋆

  split₂ˡ : {a₁ a₂ b₂ c₁ c₂ : Obj C}
            {f : C [ a₁ , c₁ ]} {g : C [ a₂ , b₂ ]} {h : C [ b₂ , c₂ ]} ->
            f ⊗₁ (g ⋆ h) == (f ⊗₁ g) ⋆ (id C ⊗₁ h)
  split₂ˡ = ⊗₁-left (sym ⋆-right-id) >=> ⊗-distrib-⋆

  split₂ʳ : {a₁ a₂ b₂ c₁ c₂ : Obj C}
            {f : C [ a₁ , c₁ ]} {g : C [ a₂ , b₂ ]} {h : C [ b₂ , c₂ ]} ->
            f ⊗₁ (g ⋆ h) == (id C ⊗₁ g) ⋆ (f ⊗₁ h)
  split₂ʳ = ⊗₁-left (sym ⋆-left-id) >=> ⊗-distrib-⋆

  retract-unit⊗ : {x y : Obj C} -> {f g : C [ x , y ]} ->
                  Path (C [ unit ⊗₀ x , unit ⊗₀ y ]) (id C ⊗₁ f) (id C ⊗₁ g) -> f == g
  retract-unit⊗ p =
    sym ⋆-left-id >=>
    ⋆-left (sym (isIso.sec ((snd unitorˡ) _))) >=>
    ⋆-assoc >=>
    ⋆-right λ⇒-swap >=>
    (\ i -> λ⇐ ⋆ (p i ⋆ λ⇒)) >=>
    ⋆-right (sym λ⇒-swap) >=>
    sym ⋆-assoc >=>
    ⋆-left (isIso.sec ((snd unitorˡ) _)) >=>
    ⋆-left-id

  retract-⊗unit : {x y : Obj C} -> {f g : C [ x , y ]} ->
                  Path (C [ x ⊗₀ unit , y ⊗₀ unit ]) (f ⊗₁ id C) (g ⊗₁ id C) -> f == g
  retract-⊗unit p =
    sym ⋆-left-id >=>
    ⋆-left (sym (isIso.sec ((snd unitorʳ) _))) >=>
    ⋆-assoc >=>
    ⋆-right ρ⇒-swap >=>
    (\ i -> ρ⇐ ⋆ (p i ⋆ ρ⇒)) >=>
    ⋆-right (sym ρ⇒-swap) >=>
    sym ⋆-assoc >=>
    ⋆-left (isIso.sec ((snd unitorʳ) _)) >=>
    ⋆-left-id
