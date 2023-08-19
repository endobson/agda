{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.group where

open import base
open import category.base
open import category.monoidal.base
open import category.monoidal.semicartesian
open import category.natural-transformation
open import category.object.product
open import category.object.terminal
open import cubical
open import equality
open import hlevel

module _ {ℓO ℓM} {C : PreCategory ℓO ℓM}
         {M : MonoidalStr C} {SC : isSemiCartesian M} (Cart : isCartesian SC)
         (magic : Magic) where
  private
    open MonoidalStrHelpers M
    open CategoryHelpers C
    open TerminalHelpers (isSemiCartesian.term SC)
    module Cart = isCartesian Cart
    module _ {x y : Obj C} where
      open ProductHelpers (Cart.prod x y) public

  module _ (g : Obj C) (op : C [ g ⊗₀ g , g ]) where
    isAssociative : Type ℓM
    isAssociative =
      α⇒ ⋆⟨ C ⟩ (id C ⊗₁ op) ⋆⟨ C ⟩ op == (op ⊗₁ id C) ⋆⟨ C ⟩ op


  record isUnital (g : Obj C) (op : C [ g ⊗₀ g , g ]) : Type ℓM where
    field
      ε : C [ 1C , g ]

    ε' : {x : Obj C} -> C [ x , g ]
    ε' = ! ⋆ ε

    field
      ε-left-id' : ×⟨ ε' , id C ⟩ ⋆ op == id C
      ε-right-id' : ×⟨ id C , ε' ⟩ ⋆ op == id C

    opaque
      ε-left-id : ∀ {x : Obj C} (f : C [ x , g ]) -> (×⟨ ε' , f ⟩ ⋆ op) == f
      ε-left-id f =
        (\ i -> ×⟨ ε' , ⋆-right-idᵉ f (~ i) ⟩ ⋆ op) >=>
        ⋆-left lemma1 >=>
        ⋆-assoc >=>
        ⋆-right ε-left-id' >=>
        ⋆-right-id
        where
        lemma1 : ×⟨ ε' , f ⋆⟨ C ⟩ id C ⟩ ==  f ⋆⟨ C ⟩ ×⟨ ε' , id C ⟩
        lemma1 = magic
          -- gg.unique
          --   ((⋆-assoc >=>
          --         ⋆-right π₁-reduce >=>
          --         sym ⋆-assoc >=>
          --         ⋆-left !-unique))
          --   ((⋆-assoc >=>
          --         ⋆-right π₂-reduce))

      ε-right-id : ∀ {x : Obj C} (f : C [ x , g ]) -> (×⟨ f , ε' ⟩ ⋆⟨ C ⟩ op) == f
      ε-right-id f =
        (\ i -> ×⟨ ⋆-right-idᵉ f (~ i) , ε' ⟩ ⋆ op) >=>
        ⋆-left lemma1 >=>
        ⋆-assoc >=>
        ⋆-right ε-right-id' >=>
        ⋆-right-id
        where
        lemma1 : ×⟨ f ⋆⟨ C ⟩ id C , ε' ⟩ ==  f ⋆⟨ C ⟩ ×⟨ id C , ε' ⟩
        lemma1 = magic
          -- gg.unique
          --   (⋆-assoc >=>
          --    ⋆-right π₁-reduce)
          --   (⋆-assoc >=>
          --    ⋆-right π₂-reduce >=>
          --    sym ⋆-assoc >=>
          --    ⋆-left !-unique)

  opaque
    isProp-isUnital : ∀ {g op} -> isProp (isUnital g op)
    isProp-isUnital {g} {op}
      u₁@(record { ε = ε₁ ; ε-left-id' = ε₁-left-id' ; ε-right-id' = ε₁-right-id' })
      u₂@(record { ε = ε₂ ; ε-left-id' = ε₂-left-id' ; ε-right-id' = ε₂-right-id' }) =
      \i -> record
        { ε = ε-path i
        ; ε-left-id' = isProp->PathPᵉ (\i -> isSet-Mor C (l-path i) _) ε₁-left-id' ε₂-left-id' i
        ; ε-right-id' = isProp->PathPᵉ (\i -> isSet-Mor C (r-path i) _) ε₁-right-id' ε₂-right-id' i
        }
      where
      ε₁'-path : isUnital.ε' u₁ == ε₁
      ε₁'-path = ⋆-left !-unique >=> ⋆-left-id
      ε₂'-path : isUnital.ε' u₂ == ε₂
      ε₂'-path = ⋆-left !-unique >=> ⋆-left-id

      ε-path : ε₁ == ε₂
      ε-path =
        sym (isUnital.ε-right-id u₂ ε₁) >=>
        (\ i -> ×⟨ (ε₁'-path (~ i)) , (ε₂'-path i) ⟩ ⋆ op) >=>
        isUnital.ε-left-id u₁ ε₂

      l-path : (ε₁-left-id' i0) == (ε₂-left-id' i0)
      l-path i = ×⟨ (! ⋆ ε-path i) , (id C) ⟩ ⋆ op
      r-path : (ε₁-right-id' i0) == (ε₂-right-id' i0)
      r-path i = ×⟨ (id C) , (! ⋆ ε-path i ) ⟩ ⋆ op

  module _ {g : Obj C} {op : C [ g ⊗₀ g , g ]} (unit : isUnital g op) where
    private
      Δ : C [ g , g ⊗₀ g ]
      Δ = ×⟨ id C , id C ⟩

    record hasInverse : Type ℓM where
      field
        inv : C [ g , g ]

        inv-left : ×⟨ inv , id C ⟩ ⋆⟨ C ⟩ op == isUnital.ε' unit
        inv-right : ×⟨ id C , inv ⟩ ⋆⟨ C ⟩ op == isUnital.ε' unit

    module _ (assoc : isAssociative g op) where
      isProp-hasInverse : isProp hasInverse
      isProp-hasInverse
        s₁@(record { inv = inv₁ ; inv-left = inv₁-left ; inv-right = inv₁-right })
        s₂@(record { inv = inv₂ ; inv-left = inv₂-left ; inv-right = inv₂-right }) =
        \i -> record
          { inv = inv-path i
          ; inv-left = isProp->PathPᵉ (\i -> isSet-Mor C (l-path i) _) inv₁-left inv₂-left i
          ; inv-right = isProp->PathPᵉ (\i -> isSet-Mor C (r-path i) _) inv₁-right inv₂-right i
          }
        where
        lemma1 : ×⟨ inv₁ , ×⟨ id C , inv₂ ⟩ ⋆⟨ C ⟩ op ⟩ ⋆⟨ C ⟩ op == inv₁
        lemma1 =
          (\i -> ×⟨ inv₁ , inv₂-right i ⟩ ⋆⟨ C ⟩ op) >=>
          isUnital.ε-right-id unit inv₁

        lemma2 : ×⟨ ×⟨ inv₁ , id C ⟩ ⋆⟨ C ⟩ op , inv₂ ⟩ ⋆⟨ C ⟩ op == inv₂
        lemma2 =
          (\i -> ×⟨ inv₁-left i , inv₂ ⟩ ⋆⟨ C ⟩ op) >=>
          isUnital.ε-left-id unit inv₂

        -- swap : ×⟨ inv₁ , gg.×⟨ id C , inv₂ ⟩ ⋆⟨ C ⟩ op ⟩ ⋆⟨ C ⟩ op ==
        --        ×⟨ inv₁ , (? ⋆⟨ C ⟩ (id C ⊗₁ inv₂)) ⋆⟨ C ⟩ op ⟩ ⋆⟨ C ⟩ op
        -- swap = refl

        -- check : (f1 f2 : C [ g , g ]) -> ×⟨ f1 , f2 ⟩ == Δ ⋆⟨ C ⟩ (f1 ⊗₁ f2)
        -- check f1 f2 =
        --   unique path1 magic
        --   where
        --   path1 : Δ ⋆⟨ C ⟩ (f1 ⊗₁ f2) ⋆⟨ C ⟩ π₁ == f1
        --   path1 =
        --     C.⋆-assocⁱ >=>
        --     C.⋆-right ?ⁱ >=>
        --     ?

        check2 : Path (C [ g ⊗₀ g , g ]) ((id C ⊗₁ !) ⋆⟨ C ⟩ π₁) (π₁ ⋆⟨ C ⟩ id C )
        check2 = magic
          where
          u : (a : Obj C) -> C [ (1C ⊗₀ a) , a ]
          u a = NT-obj (fst unitorˡ) a

          check4 : {a b : Obj C} -> (f : C [ a , b ]) ->
            Path (C [ (1C ⊗₀ a) , (1C ⊗₀ b) ])
            (id C ⊗₁ f)
            ((id C ⊗₁ f) ⋆⟨ C ⟩ (! ⊗₁ id C))
          check4 f =
            (\ i -> (⋆-left-idᵉ (id C) (~ i)) ⊗₁ (⋆-right-idᵉ f (~ i))) >=>
            (\ i -> (id C ⋆⟨ C ⟩ !-uniqueᵉ ! (id C) (~ i)) ⊗₁ (f ⋆⟨ C ⟩ id C)) >=>
            ⊗-distrib-⋆

          check3 : {a b : Obj C} -> (f : C [ a , b ]) ->
            Path (C [ (1C ⊗₀ a) , b ])
            (u a ⋆⟨ C ⟩ f)
            ((id C ⊗₁ f) ⋆⟨ C ⟩ u b)
          check3 f = (NT-mor (fst unitorˡ) f)




        inv-path : inv₁ == inv₂
        inv-path = sym lemma1 >=> magic >=> lemma2

        l-path : inv₁-left i0 == inv₂-left i0
        l-path i = ×⟨ inv-path i , id C ⟩ ⋆⟨ C ⟩ op
        r-path : inv₁-right i0 == inv₂-right i0
        r-path i = ×⟨ id C , inv-path i ⟩ ⋆⟨ C ⟩ op











