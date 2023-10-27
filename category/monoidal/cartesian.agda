{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.cartesian where

open import base
open import category.base
open import category.functor
open import category.monoidal.base
open import category.object.product
open import category.object.terminal
open import category.zipper
open import equality-path

module _ {ℓO ℓM : Level} (MC@(C , M) : MonoidalCategory ℓO ℓM) where
  open MonoidalStrHelpers M
  open CategoryHelpers C

  record isCartesian : Type (ℓ-max ℓO ℓM) where
    field
      isTerminal-unit : isTerminal C unit

    term : Terminal C
    term = record { universal = isTerminal-unit }

    open TerminalHelpers term

    π₁ : {x y : Obj C} -> C [ x ⊗₀ y , x ]
    π₁ = (id C ⊗₁ !) ⋆ ρ⇒

    π₂ : {x y : Obj C} -> C [ x ⊗₀ y , y ]
    π₂ = (! ⊗₁ id C) ⋆ λ⇒

    field
      isProduct-⊗ : (x y : Obj C) -> isProduct C x y (x ⊗₀ y) π₁ π₂

    prod : (x y : Obj C) -> Product C x y
    prod x y = record { universal = isProduct-⊗ x y }

CartesianMonoidalCategory : (ℓO ℓM : Level) -> Type (ℓ-suc (ℓ-max ℓO ℓM))
CartesianMonoidalCategory ℓO ℓM = Σ (Σ (PreCategory ℓO ℓM) MonoidalStr) isCartesian

module CartesianHelpers
  {ℓO ℓM : Level} {MC@(C , M) : MonoidalCategory ℓO ℓM}
  (Cart : isCartesian MC) where

  open CategoryHelpers C
  open MonoidalStrHelpers M
  open TerminalHelpers (isCartesian.term Cart) public
  module _ {x y : Obj C} where
    open ProductHelpers (isCartesian.prod Cart x y) public
  open ZReasoning C

  Δᵉ : (x : Obj C) -> C [ x , x ⊗₀ x ]
  Δᵉ _ = ×⟨ id C , id C ⟩

  Δ : {x : Obj C} -> C [ x , x ⊗₀ x ]
  Δ {x} = Δᵉ x

  opaque
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

    ⊗π₁-reduce : {a₁ a₂ b₁ b₂ : Obj C} {f : C [ a₁ , b₁ ]} {g : C [ a₂ , b₂ ]} ->
                 Path (C [ a₁ ⊗₀ a₂ , b₁ ]) ((f ⊗₁ g) ⋆ π₁) (π₁ ⋆ f)
    ⊗π₁-reduce = sym π₁-swap
    ⊗π₂-reduce : {a₁ a₂ b₁ b₂ : Obj C} {f : C [ a₁ , b₁ ]} {g : C [ a₂ , b₂ ]} ->
                 Path (C [ a₁ ⊗₀ a₂ , b₂ ]) ((f ⊗₁ g) ⋆ π₂) (π₂ ⋆ g)
    ⊗π₂-reduce = sym π₂-swap

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

    α⇒π₂-reduce : {x y z : Obj C} -> Path (C [ ((x ⊗₀ y) ⊗₀ z) , (y ⊗₀ z) ]) (α⇒ ⋆ π₂) (π₂ ⊗₁ id C)
    α⇒π₂-reduce = begin
      [ [] , α⇒ ⋆ π₂ , [] ]=<
        left⇐ >z> right⇒ >
      [ [] <: α⇒ , (! ⊗₁ id C) , λ⇒ :> [] ]=<
        z-cong (⊗₁-right (sym (F-id ⊗ _))) >z> left⇒ >
      [ [] , α⇒ ⋆ (! ⊗₁ (id C ⊗₁ id C)) , λ⇒ :> [] ]=<
        z-cong α⇒-swap >z> shift⇐ >z> z-cong α⇒λ⇒-reduce >
      [ [] <: ((! ⊗₁ id C) ⊗₁ id C) , λ⇒ ⊗₁ id C , [] ]=<
        left⇒ >z> z-cong (sym split₁ˡ) >
      [ [] , (π₂ ⊗₁ id C) , [] ]end

    α⇒π₂π₁-reduce : {x y z : Obj C} -> Path (C [ ((x ⊗₀ y) ⊗₀ z) , y ]) (α⇒ ⋆ π₂ ⋆ π₁) (π₁ ⋆ π₂)
    α⇒π₂π₁-reduce = ⋆-left α⇒π₂-reduce >=> ⊗π₁-reduce
    α⇒π₂π₂-reduce : {x y z : Obj C} -> Path (C [ ((x ⊗₀ y) ⊗₀ z) , z ]) (α⇒ ⋆ π₂ ⋆ π₂) π₂
    α⇒π₂π₂-reduce = ⋆-left α⇒π₂-reduce >=> ⊗π₂-reduce >=> ⋆-right-id



    Δ-swapᵉ : {x y : Obj C} (f : C [ x , y ]) -> Path (C [ x , (y ⊗₀ y) ]) (Δ ⋆ (f ⊗₁ f)) (f ⋆ Δ)
    Δ-swapᵉ f = prod-unique
      (⋆-assoc >=>
       ⋆-right (sym π₁-swap) >=>
       sym ⋆-assoc >=>
       ⋆-left π₁-reduce >=>
       ⋆-left-id >=>
       sym ⋆-right-id >=>
       ⋆-right (sym π₁-reduce) >=>
       sym ⋆-assoc)
      (⋆-assoc >=>
       ⋆-right (sym π₂-swap) >=>
       sym ⋆-assoc >=>
       ⋆-left π₂-reduce >=>
       ⋆-left-id >=>
       sym ⋆-right-id >=>
       ⋆-right (sym π₂-reduce) >=>
       sym ⋆-assoc)

    Δ-swap : {x y : Obj C} {f : C [ x , y ]} -> Path (C [ x , (y ⊗₀ y) ]) (Δ ⋆ (f ⊗₁ f)) (f ⋆ Δ)
    Δ-swap {f = f} = Δ-swapᵉ f

    Δπ₁-reduce : {x : Obj C} -> Path (C [ x , x ]) (Δ ⋆ π₁) (id C)
    Δπ₁-reduce = π₁-reduce
    Δπ₂-reduce : {x : Obj C} -> Path (C [ x , x ]) (Δ ⋆ π₂) (id C)
    Δπ₂-reduce = π₂-reduce

    Δ⊗π₁-reduce : {x y z : Obj C} {f : C [ x , y ]} {g : C [ x , z ]} ->
                  Path (C [ x , y ]) (Δ ⋆ (f ⊗₁ g) ⋆ π₁) f
    Δ⊗π₁-reduce = ⋆-assoc >=> ⋆-right (sym π₁-swap) >=> sym ⋆-assoc >=>
                  ⋆-left Δπ₁-reduce >=> ⋆-left-id

    Δ⊗π₂-reduce : {x y z : Obj C} {f : C [ x , y ]} {g : C [ x , z ]} ->
                  Path (C [ x , z ]) (Δ ⋆ (f ⊗₁ g) ⋆ π₂) g
    Δ⊗π₂-reduce = ⋆-assoc >=> ⋆-right (sym π₂-swap) >=> sym ⋆-assoc >=>
                  ⋆-left Δπ₂-reduce >=> ⋆-left-id

    ΔΔ-assoc : {x : Obj C} -> Path (C [ x , (x ⊗₀ (x ⊗₀ x)) ]) (Δ ⋆ (Δ ⊗₁ id C) ⋆ α⇒) (Δ ⋆ (id C ⊗₁ Δ))
    ΔΔ-assoc =
      prod-unique
        (⋆-assoc >=>
         ⋆-right α⇒π₁-reduce >=>
         sym ⋆-assoc >=>
         ⋆-left Δ⊗π₁-reduce >=>
         Δπ₁-reduce >=>
         sym Δ⊗π₁-reduce)
        (prod-unique
          (⋆-assoc >=> ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> α⇒π₂π₁-reduce) >=>
           sym ⋆-assoc >=> ⋆-left Δ⊗π₁-reduce >=> Δπ₂-reduce >=>
           sym (⋆-left Δ⊗π₂-reduce >=> Δπ₁-reduce))
          (⋆-assoc >=> ⋆-assoc >=> ⋆-right (sym ⋆-assoc >=> α⇒π₂π₂-reduce) >=>
           Δ⊗π₂-reduce >=>
           sym (⋆-left Δ⊗π₂-reduce >=> Δπ₂-reduce)))

    π₁Δ!-id : {a : Obj C} -> Path (C [ a ⊗₀ 1C , a ⊗₀ 1C ]) (π₁ ⋆ Δ ⋆ (id C ⊗₁ !)) (id C)
    π₁Δ!-id =
      prod-unique
        (⋆-assoc >=>
         ⋆-right (⊗π₁-reduce >=> ⋆-right-id) >=>
         ⋆-assoc >=>
         ⋆-right Δπ₁-reduce >=>
         ⋆-right-id >=>
         sym ⋆-left-id)
        !-unique

    π₂Δ!-id : {a : Obj C} -> Path (C [ 1C ⊗₀ a , 1C ⊗₀ a ]) (π₂ ⋆ Δ ⋆ (! ⊗₁ id C)) (id C)
    π₂Δ!-id =
      prod-unique
        !-unique
        (⋆-assoc >=>
         ⋆-right (⊗π₂-reduce >=> ⋆-right-id) >=>
         ⋆-assoc >=>
         ⋆-right Δπ₂-reduce >=>
         ⋆-right-id >=>
         sym ⋆-left-id)
