{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.semicartesian where

open import base
open import category.base
open import category.constructions.isomorphism
open import category.constructions.product
open import category.functor
open import category.isomorphism
open import category.monoidal.base
open import category.morphism
open import category.object.product
open import category.object.terminal
open import category.zipper
open import equality

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (M : MonoidalStr C) where
  record isSemiCartesian : Type (ℓ-max ℓO ℓM) where
    field
      isTerminal-unit : isTerminal C (MonoidalStr.unit M)

    term : Terminal C
    term = record { universal = isTerminal-unit }

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

module CartesianHelpers
  {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} {M : MonoidalStr C}
  {SC : isSemiCartesian M} (Cart : isCartesian SC) where

  open MonoidalStrHelpers M
  open CategoryHelpers C
  open TerminalHelpers (isSemiCartesian.term SC)
  module _ {x y : Obj C} where
    open ProductHelpers (isCartesian.prod Cart x y) public
  open ZReasoning C

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

  α⇒λ⇒-reduce : {x y : Obj C} ->
    Path (C [ (unit ⊗₀ x) ⊗₀ y , (x ⊗₀ y) ])
    (α⇒ ⋆ λ⇒) (λ⇒ ⊗₁ id C)
  α⇒λ⇒-reduce {x} {y} = retract-unit⊗ (isIso->isEpi isIso-αα full-path)
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

    full-path : Path (C [ ((unit ⊗₀ unit) ⊗₀ x) ⊗₀ y , unit ⊗₀ (x ⊗₀ y) ])
                ((α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ (α⇒ ⋆ λ⇒)))
                ((α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ (λ⇒ ⊗₁ id C)))
    full-path = begin
     [ [] , (α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ (α⇒ ⋆ λ⇒)) , [] ]=<
       left⇐ >
     [ [] <: ((α⇒ ⊗₁ id C) ⋆ α⇒) , (id C ⊗₁ (α⇒ ⋆ λ⇒)) , [] ]=<
       z-cong split₂ˡ >z> shift⇒ >
     [ [] , (α⇒ ⊗₁ id C) ⋆ α⇒ ⋆ (id C ⊗₁ α⇒) , (id C ⊗₁ λ⇒) :> [] ]=<
       z-cong (sym pentagon) >
     [ [] , α⇒ ⋆ α⇒ , (id C ⊗₁ λ⇒) :> [] ]=<
       shift⇐ >z> z-cong triangle >
     [ [] <: α⇒ , ρ⇒ ⊗₁ id C , [] ]=<
       z-cong (⊗₁-right (sym (F-id ⊗ _))) >
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


  λ⇒=ρ⇒ : Path (C [ unit ⊗₀ unit , unit ]) λ⇒ ρ⇒
  λ⇒=ρ⇒ = retract-⊗unit λ⇒=ρ⇒'
    where
    λ⇒-reduce1 : {a : Obj C} -> Path (C [ unit ⊗₀ (unit ⊗₀ a) , unit ⊗₀ a ]) λ⇒ (id C ⊗₁ λ⇒)
    λ⇒-reduce1 =
      sym ⋆-right-id >=>
      ⋆-right (sym (isIso.ret (snd unitorˡ _))) >=>
      sym ⋆-assoc >=>
      ⋆-left λ⇒-swap >=>
      ⋆-assoc >=>
      ⋆-right (isIso.ret (snd unitorˡ _)) >=>
      ⋆-right-id

    λ⇒=ρ⇒' : Path (C [ (unit ⊗₀ unit) ⊗₀ unit , unit ⊗₀ unit ]) (λ⇒ ⊗₁ id C) (ρ⇒ ⊗₁ id C)
    λ⇒=ρ⇒' = sym α⇒λ⇒-reduce >=> ⋆-right λ⇒-reduce1 >=> triangle


--   α⇐ρ⇒-reduce : {x y : Obj C} ->
--     Path (C [ x ⊗₀ (y ⊗₀ unit) , (x ⊗₀ y) ])
--     (α⇐ ⋆ ρ⇒) (id C ⊗₁ ρ⇒)
--   α⇐ρ⇒-reduce {x} {y} = ?
--     where
--
--     full-path' : Path (C [ x ⊗₀ (y ⊗₀ (unit ⊗₀ unit)) , ((x ⊗₀ y) ⊗₀ unit)])
--                 ((id C ⊗₁ α⇐) ⋆ α⇐ ⋆ ((α⇐ ⋆ ρ⇒) ⊗₁ id C))
--                 ((id C ⊗₁ α⇐) ⋆ α⇐ ⋆ ((id C ⊗₁ ρ⇒) ⊗₁ id C))
--     full-path' = ?
--
--
--     full-path : Path (C [ (((x ⊗₀ y) ⊗₀ unit) ⊗₀ unit) , ((x ⊗₀ y) ⊗₀ unit)])
--                 ((α⇒ ⊗₁ id C) ⋆ ((α⇐ ⋆ ρ⇒) ⊗₁ id C))
--                 -- (ρ⇒ ⊗₁ id C)
--                 -- (α⇒ ⋆ (id C ⊗₁ λ⇒))
--                 -- (α⇒ ⋆ (id C ⊗₁ ρ⇒))
--                 ((α⇒ ⊗₁ id C) ⋆ ((id C ⊗₁ ρ⇒) ⊗₁ id C))
--     full-path = ?



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


  Δ : {x : Obj C} -> C [ x , x ⊗₀ x ]
  Δ {x} = ×⟨ id C , id C ⟩

  -- Δ-assoc :
  --   {x : Obj C} -> Path (C [ x , x ⊗₀ (x ⊗₀ x) ])
  --     (Δ ⋆ (Δ ⊗₁ id C) ⋆ α⇒)
  --     (Δ ⋆ (id C ⊗₁ Δ) )
  -- Δ-assoc {x} =
  --   prod-unique
  --     ?
  --     ?




