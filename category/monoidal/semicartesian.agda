{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.semicartesian where

open import base
open import equality
open import category.base
open import category.morphism
open import category.monoidal.base
open import category.isomorphism
open import category.object.terminal
open import category.object.product
open import category.constructions.isomorphism
open import category.constructions.product
open import category.zipper

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (M : MonoidalStr C) where
  record isSemiCartesian : Type (ℓ-max ℓO ℓM) where
    field
      isTerminal-unit : isTerminal C (MonoidalStr.unit M)

    term : Terminal C
    term = record { obj = MonoidalStr.unit M ; universal = isTerminal-unit }

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} {M : MonoidalStr C}
         (SC : isSemiCartesian M) where
  open MonoidalStrHelpers M
  open CategoryHelpers C
  open TerminalHelpers (isSemiCartesian.term SC)

  record isCartesian : Type (ℓ-max ℓO ℓM) where
    π₁ : {x y : Obj C} -> C [ x ⊗₀ y , x ]
    π₁ = (id C ⊗₁ !) ⋆ ρ⇒

    π₂ : {x y : Obj C} -> C [ x ⊗₀ y , y ]
    π₂ = (! ⊗₁ id C) ⋆ λ⇒

    field
      isProduct-⊗ : (x y : Obj C) -> isProduct C x y (x ⊗₀ y) π₁ π₂

    prod : (x y : Obj C) -> Product C x y
    prod x y = record { universal = isProduct-⊗ x y }

    module _ {x y : Obj C} where
      open ProductHelpers (prod x y) hiding (π₁ ; π₂) public

    Δ : {x : Obj C} -> C [ x , x ⊗₀ x ]
    Δ {x} = ×⟨ id C , id C ⟩


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

    π₁-swap : {a₁ a₂ b₁ b₂ : Obj C} {f : C [ a₁ , b₁ ]} {g : C [ a₂ , b₂ ]} ->
               Path (C [ a₁ ⊗₀ a₂ , b₁ ]) (π₁ ⋆ f) ((f ⊗₁ g) ⋆ π₁)
    π₁-swap {f = f} {g = g} = begin
      [ [] , π₁ ⋆ f , [] ]=<
        right⇒ >z> shift⇐ >
      [ [] <: (id C ⊗₁ !) , ρ⇒ ⋆ f , [] ]=<
        z-cong ρ⇒-swap >z> shift⇒ >
      [ [] , (id C ⊗₁ !) ⋆ (f ⊗₁ id C) , ρ⇒ :> [] ]=<
        z-cong (sym serialize₂₁) >
      [ [] , (f ⊗₁ !) , ρ⇒ :> [] ]=<
        z-cong (⊗₁-right !-unique) >
      [ [] , (f ⊗₁ (g ⋆ !)) , ρ⇒ :> [] ]=<
        z-cong split₂ˡ >
      [ [] , (f ⊗₁ g) ⋆ (id C ⊗₁ !) , ρ⇒ :> [] ]=<
        shift⇐ >z> left⇒ >
      [ [] , (f ⊗₁ g) ⋆ π₁ , [] ]end

    π₂-swap : {a₁ a₂ b₁ b₂ : Obj C} {f : C [ a₁ , b₁ ]} {g : C [ a₂ , b₂ ]} ->
               Path (C [ a₁ ⊗₀ a₂ , b₂ ]) (π₂ ⋆ g) ((f ⊗₁ g) ⋆ π₂)
    π₂-swap {f = f} {g = g} = begin
      [ [] , π₂ ⋆ g , [] ]=<
        right⇒ >z> shift⇐ >
      [ [] <: (! ⊗₁ id C) , λ⇒ ⋆ g , [] ]=<
        z-cong λ⇒-swap >z> shift⇒ >
      [ [] , (! ⊗₁ id C) ⋆ (id C ⊗₁ g) , λ⇒ :> [] ]=<
        z-cong (sym serialize₁₂) >
      [ [] , ! ⊗₁ g , λ⇒ :> [] ]=<
        z-cong (⊗₁-left !-unique) >
      [ [] , (f ⋆ !) ⊗₁ g , λ⇒ :> [] ]=<
        z-cong split₁ˡ >
      [ [] , (f ⊗₁ g) ⋆ (! ⊗₁ id C) , λ⇒ :> [] ]=<
        shift⇐ >z> left⇒ >
      [ [] , (f ⊗₁ g) ⋆ π₂ , [] ]end

    α⇒π₁-reduce : {x y z : Obj C} -> Path (C [ ((x ⊗₀ y) ⊗₀ z) , x ]) (α⇒ ⋆ π₁) (π₁ ⋆ π₁)
    α⇒π₁-reduce = begin
      [ [] , α⇒ ⋆ π₁ , [] ]=<
        left⇐ >z> right⇒ >
      [ [] <: α⇒ , (id C ⊗₁ !) , ρ⇒ :> [] ]=<
        z-cong (⊗₁-right !-unique) >
      [ [] <: α⇒ , (id C ⊗₁ ((! ⊗₁ !) ⋆ λ⇒)) , ρ⇒ :> [] ]=<
        z-cong split₂ˡ >
      [ [] <: α⇒ , (id C ⊗₁ (! ⊗₁ !)) ⋆ (id C ⊗₁ λ⇒) , ρ⇒ :> [] ]=<
        shift⇒ >
      [ [] , α⇒ ⋆ (id C ⊗₁ (! ⊗₁ !)) , (id C ⊗₁ λ⇒) :> ρ⇒ :> [] ]=<
        z-cong α⇒-swap >
      [ [] , ((id C ⊗₁ !) ⊗₁ !) ⋆ α⇒ , (id C ⊗₁ λ⇒) :> ρ⇒ :> [] ]=<
        shift⇐ >z> z-cong triangle >
      [ [] <: ((id C ⊗₁ !) ⊗₁ !) , (ρ⇒ ⊗₁ id C) , ρ⇒ :> [] ]=<
        left⇒ >z> z-cong (sym split₁ˡ) >
      [ [] , π₁ ⊗₁ ! , ρ⇒ :> [] ]=<
        z-cong serialize₂₁ >
      [ [] , (id C ⊗₁ !) ⋆ (π₁ ⊗₁ id C) , ρ⇒ :> [] ]=<
        shift⇐ >z> z-cong (sym ρ⇒-swap) >
      [ [] <: (id C ⊗₁ !) , ρ⇒ ⋆ π₁ , [] ]=<
        shift⇒ >z> right⇐ >
      [ [] , π₁ ⋆ π₁ , [] ]end

    check1 : {x y : Obj C} -> C [ (unit ⊗₀ x) ⊗₀ y , x ⊗₀ y ]
    check1 = λ⇒ ⊗₁ id C

    check2 : {x y : Obj C} -> C [ (unit ⊗₀ x) ⊗₀ y , x ⊗₀ y ]
    check2 = α⇒ ⋆ λ⇒

    retract-1⊗ : {x y : Obj C} -> {f g : C [ x , y ]} ->
                 Path (C [ unit ⊗₀ x , unit ⊗₀ y ]) (id C ⊗₁ f) (id C ⊗₁ g) -> f == g
    retract-1⊗ {x} {y} {f} {g} p =
      sym ⋆-left-id >=>
      ⋆-left (sym (isIso.sec ((snd unitorˡ) _))) >=>
      ⋆-assoc >=>
      ⋆-right λ⇒-swap >=>
      (\ i -> λ⇐ ⋆ (p i ⋆ λ⇒)) >=>
      ⋆-right (sym λ⇒-swap) >=>
      sym ⋆-assoc >=>
      ⋆-left (isIso.sec ((snd unitorˡ) _)) >=>
      ⋆-left-id


    check4 : {x y : Obj C} -> Path (C [ ((unit ⊗₀ unit) ⊗₀ x) ⊗₀ y , unit ⊗₀ (x ⊗₀ y) ])
             ((α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ (α⇒ ⋆ λ⇒)))
             ((α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ (λ⇒ ⊗₁ id C)))
    check4 = begin
     [ [] , (α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ (α⇒ ⋆ λ⇒)) , [] ]=<
       left⇐ >
     [ [] <: ((α⇒ ⊗₁ id C) ⋆ α⇒) , (id C ⊗₁ (α⇒ ⋆ λ⇒)) , [] ]=<
       z-cong split₂ˡ >z> shift⇒ >
     [ [] , (α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ α⇒) , (id C ⊗₁ λ⇒) :> [] ]=<
       z-cong (sym pentagon) >
     [ [] , α⇒ ⋆ α⇒ , (id C ⊗₁ λ⇒) :> [] ]=<
       shift⇐ >z> z-cong triangle >
     [ [] <: α⇒ , ρ⇒ ⊗₁ id C , [] ]=<
       z-cong (⊗₁-left (sym !-unique)) >
     [ [] <: α⇒ , ! ⊗₁ id C , [] ]=<
       z-cong (cong2 _⊗₁_ !-unique (sym (F-id ⊗ _))) >
     [ [] <: α⇒ , (ρ⇒ ⊗₁ (id C ⊗₁ id C)) , [] ]=<
       left⇒ >z> z-cong α⇒-swap >z> right⇒ >
     [ [] , (ρ⇒ ⊗₁ id C) ⊗₁ id C , α⇒ :> [] ]=<
       z-cong (⊗₁-left (sym triangle)) >
     [ [] , (α⇒ ⋆ (id C ⊗₁ λ⇒)) ⊗₁ id C , α⇒ :> [] ]=<
       z-cong split₁ˡ >z> shift⇐ >
     [ [] <: (α⇒ ⊗₁ id C) , ((id C ⊗₁ λ⇒) ⊗₁ id C) ⋆ α⇒ , [] ]=<
       z-cong (sym α⇒-swap) >
     [ [] <: (α⇒ ⊗₁ id C) , α⇒ ⋆ (id C ⊗₁ (λ⇒ ⊗₁ id C)) , [] ]=<
       shift⇒ >z> right⇐ >
     [ [] , (α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ (λ⇒ ⊗₁ id C)) , [] ]end


    α⇒λ⇒-reduce : {x y : Obj C} ->
      Path (C [ (unit ⊗₀ x) ⊗₀ y , (x ⊗₀ y) ])
      (α⇒ ⋆ λ⇒) (λ⇒ ⊗₁ id C)
    α⇒λ⇒-reduce {x} {y} = retract-1⊗ (isIso->isEpi isIso-αα check4)
      where
      isIso-αα : isIso C ((α⇒ ⊗₁ id C) ⋆ α⇒)
      isIso-αα =
        snd (((α⇒ ⊗₁ id C) , (functor-preserves-isIso (appʳ ⊗ y) (iso-α⇒ {unit} {unit} {x})))
             ⋆⟨ D ⟩
             (α⇒ , iso-α⇒))
        where
        D = IsoC C
        iso-α⇒ : {a b c : Obj C} -> isIso C (α⇒ {a} {b} {c})
        iso-α⇒ {a} {b} {c} = (snd associator) _

    --1⊗ : Functor C C
    --1⊗ = record
    --  { obj = \c -> unit ⊗₀ c
    --  ; mor = \f -> id C ⊗₁ f
    --  ; id = \c -> F-id ⊗ (unit , c)
    --  ; ⋆ = \f g -> cong (F-mor ⊗) (\i -> PreCategory.⋆-id² C (~ i) , f ⋆ g) >=>
    --                F-⋆ ⊗ (id C , f) (id C , g)
    --  }

    -- NatIso-1⊗ : NaturalIsomorphism 1⊗ (idF C)
    -- NatIso-1⊗ = unitorˡ

    {-

    α⇒π₂π₁-reduce : {x y z : Obj C} -> Path (C [ ((x ⊗₀ y) ⊗₀ z) , y ]) (α⇒ ⋆ π₂ ⋆ π₁) (π₁ ⋆ π₂)
    α⇒π₂π₁-reduce = begin
      [ [] , α⇒ ⋆ π₂ ⋆ π₁ , [] ]=<
        right⇒ >z> left⇐ >z> left⇐ >z> right⇐ >z> left⇐ >z> shift⇒ >
      [ [] <: α⇒ <: (! ⊗₁ id C) , λ⇒ ⋆ (id C ⊗₁ !) , ρ⇒ :> [] ]=<
        z-cong λ⇒-swap >
      [ [] <: α⇒ <: (! ⊗₁ id C) , (id C ⊗₁ (id C ⊗₁ !)) ⋆ λ⇒ , ρ⇒ :> [] ]=<
        shift⇐ >z> z-cong λ⇒-swap >
      [ [] <: α⇒ <: (! ⊗₁ id C) <: (id C ⊗₁ (id C ⊗₁ !)) , (id C ⊗₁ ρ⇒) ⋆ λ⇒ , [] ]=<
        shift⇒ >z> z-cong (sym split₂ʳ) >
      [ [] <: α⇒ <: (! ⊗₁ id C) , id C ⊗₁ π₁ , λ⇒ :> [] ]=<
        right⇐ >z> z-cong (sym λ⇒-swap) >
      [ [] <: α⇒ <: (! ⊗₁ id C) , λ⇒ ⋆ π₁ , [] ]=< ? >
      [ [] , π₁ ⋆ π₂ , [] ]end

    -}


    -- Δ-assoc :
    --   {x : Obj C} -> Path (C [ x , x ⊗₀ (x ⊗₀ x) ])
    --     (Δ ⋆ (Δ ⊗₁ id C) ⋆ α⇒)
    --     (Δ ⋆ (id C ⊗₁ Δ) )
    -- Δ-assoc {x} =
    --   prod-unique
    --     ?
    --     ?




