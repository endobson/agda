{-# OPTIONS --cubical --safe --exact-split #-}

module category.cartesian-test where

open import base
open import category.base
open import equality hiding (begin_)
open import category.object.product

open import category.zipper

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} 
  (prod : ∀ x y -> Product C x y)
  where

  module _ {x y : Obj C} where
    open Product (prod x y) 
      using (π₁ ; π₂ ; π₁-reduce ; π₂-reduce ; ×⟨_,_⟩) 
      renaming (unique₂ to prod-unique)
      public
  open PreCategory C using (_⋆_)
  module C = PreCategory C

  _⊗₀_ : Obj C -> Obj C -> Obj C
  a ⊗₀ b = Product.obj (prod a b)

  module _ (o0 o1 o2 : Obj C) where
    nt-o : C [ (o0 ⊗₀ o1) ⊗₀ o2 , o0 ⊗₀ (o1 ⊗₀ o2) ]
    nt-o = ×⟨ (π₁ ⋆ π₁) , ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⟩

    private
      open ZReasoning C

      nt-inv : C [ o0 ⊗₀ (o1 ⊗₀ o2) , (o0 ⊗₀ o1) ⊗₀ o2 ]
      nt-inv = ×⟨ ×⟨ π₁ , π₂ ⋆ π₁ ⟩ , π₂ ⋆ π₂ ⟩

      sub1-no-zip : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
      sub1-no-zip = 
         (C.⋆-assocⁱ >=>
          C.⋆-right π₁-reduce >=>
          sym C.⋆-assocⁱ >=>
          C.⋆-left π₁-reduce >=>
          π₂-reduce)


      sub1-zip-no-anno : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
      sub1-zip-no-anno = 
        (begin
          []=< right⇒ >
          []=< shift⇐ >
          []=< z-cong π₁-reduce >
          []=< shift⇒ >
          []=< z-cong π₁-reduce >
          []=< right⇐ >
          []=< z-cong π₂-reduce >
          []end)

      sub1-zip-no-mor : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
      sub1-zip-no-mor = 
        (begin
          [ []           , _                                  ,       [] ]=< right⇒ >
          [ []           , _                                  , π₁ :: [] ]=< shift⇐ >
          [ [] :: nt-inv , _                                  ,       [] ]=< z-cong π₁-reduce >
          [ [] :: nt-inv , _                                  ,       [] ]=< shift⇒ >
          [ []           , _                                  , π₂ :: [] ]=< z-cong π₁-reduce >
          [ []           , _                                  , π₂ :: [] ]=< right⇐ >
          [ []           , _                                  ,       [] ]=< z-cong π₂-reduce >
          [ []           , _                                  ,       [] ]end)

      sub1-zip : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
      sub1-zip = 
        (begin
          [ []           , nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁   ,       [] ]=< right⇒ >
          [ []           , nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩        , π₁ :: [] ]=< shift⇐ >
          [ [] :: nt-inv , ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁            ,       [] ]=< z-cong π₁-reduce >
          [ [] :: nt-inv , π₁ ⋆ π₂                           ,       [] ]=< shift⇒ >
          [ []           , nt-inv ⋆ π₁                       , π₂ :: [] ]=< z-cong π₁-reduce >
          [ []           , ×⟨ π₁ , π₂ ⋆ π₁ ⟩                 , π₂ :: [] ]=< right⇐ >
          [ []           , ×⟨ π₁ , π₂ ⋆ π₁ ⟩ ⋆ π₂            ,       [] ]=< z-cong π₂-reduce >
          [ []           , π₂ ⋆ π₁                           ,       [] ]end)
