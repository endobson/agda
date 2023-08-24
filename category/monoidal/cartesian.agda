{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.cartesian where

open import base
open import category.base
open import category.constructions.product
open import category.constructions.triple-product
open import category.monoidal.base
open import category.object.product
open import category.object.terminal
open import equality
open import fin-algebra
open import truncation
open import category.zipper

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM}
  (prod : ∀ x y -> Product C x y)
  (term : Terminal C) where
  private
    C2 = ProductCat C C
    C3 = TripleCat C C C

    open CategoryHelpers C
    open TerminalHelpers term
    module _ {x y : Obj C} where
      open ProductHelpers (prod x y) public

    _⊗₀_ : Obj C -> Obj C -> Obj C
    a ⊗₀ b = Product.obj (prod a b)

    _⊗₁_ : {a b c d : Obj C} ->
           C [ a , b ] ->  C [ c , d ] ->
           C [ a ⊗₀ c , b ⊗₀ d ]
    _⊗₁_ f g = ×⟨ π₁ ⋆ f , π₂ ⋆ g ⟩

    ⊗ : BiFunctor C C C
    ⊗ = record
      { obj = \ (a , b) -> a ⊗₀ b
      ; mor = \ (f , g) -> f ⊗₁ g
      ; id = \ (a , b) -> id-proof a b
      ; ⋆ = ⋆-proof
      }
      where
      abstract
        id-proof : (a b : Obj C) -> (idᵉ C a) ⊗₁ (idᵉ C b) == (idᵉ C (a ⊗₀ b))
        id-proof a b =
          Product.unique (prod a b)
            (⋆-left-id >=> sym ⋆-right-id)
            (⋆-left-id >=> sym ⋆-right-id)

        ⋆-proof : {a b c : Obj C × Obj C} ->
                  (f : C2 [ a , b ]) ->
                  (g : C2 [ b , c ]) ->
                  proj₁ (f ⋆⟨ C2 ⟩ g) ⊗₁ proj₂ (f ⋆⟨ C2 ⟩ g) ==
                  (proj₁ f ⊗₁ proj₂ f) ⋆ (proj₁ g ⊗₁ proj₂ g)
        ⋆-proof {c = c1 , c2} f@(f1 , f2) g@(g1 , g2) = Product.unique (prod c1 c2) p1 p2
          where

          p1 : (f1 ⊗₁ f2) ⋆ (g1 ⊗₁ g2) ⋆ π₁ == π₁ ⋆ (f1 ⋆ g1)
          p1 =
            ⋆-assoc >=>
            ⋆-right π₁-reduce >=>
            sym ⋆-assoc >=>
            ⋆-left π₁-reduce >=>
            ⋆-assoc

          p2 : (f1 ⊗₁ f2) ⋆ (g1 ⊗₁ g2) ⋆ π₂ == π₂ ⋆ (f2 ⋆ g2)
          p2 =
            ⋆-assoc >=>
            ⋆-right π₂-reduce >=>
            sym ⋆-assoc >=>
            ⋆-left π₂-reduce >=>
            ⋆-assoc

    unit : Obj C
    unit = 1C

    unitorˡ : NaturalIsomorphism (appˡ ⊗ unit) (idF C)
    unitorˡ = record
      { NT-obj = \c -> π₂
      ; NT-mor = \f -> sym π₂-reduce
      } ,
      niso

      where
      module _ (c : Obj C) where
        niso : isIso C π₂
        niso .isIso.inv = ×⟨ ! , id C ⟩
        niso .isIso.sec = π₂-reduce
        niso .isIso.ret =
          prod-unique !-unique
                      (⋆-assoc >=> ⋆-right π₂-reduce >=>
                       ⋆-right-id >=> sym ⋆-left-id)

    unitorʳ : NaturalIsomorphism (appʳ ⊗ unit) (idF C)
    unitorʳ = record
      { NT-obj = \c -> π₁
      ; NT-mor = \f -> sym π₁-reduce
      } ,
      niso

      where
      module _ (c : Obj C) where
        niso : isIso C π₁
        niso .isIso.inv = ×⟨ id C , ! ⟩
        niso .isIso.sec = π₁-reduce
        niso .isIso.ret =
          prod-unique (⋆-assoc >=> ⋆-right π₁-reduce >=>
                       ⋆-right-id >=> sym ⋆-left-id)
                      !-unique


    associator : NaturalIsomorphism (LeftBiasedDoubleApplicationFunctor ⊗)
                                    (RightBiasedDoubleApplicationFunctor ⊗)
    associator = record
      { NT-obj = nt-o
      ; NT-mor = nt-mor
      } ,
      is-niso
      where

      module _ (o@(triple o0 o1 o2) : Obj C3) where

        nt-o : C [ (o0 ⊗₀ o1) ⊗₀ o2 , o0 ⊗₀ (o1 ⊗₀ o2) ]
        nt-o = ×⟨ (π₁ ⋆ π₁) , ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⟩

        private
          nt-inv : C [ o0 ⊗₀ (o1 ⊗₀ o2) , (o0 ⊗₀ o1) ⊗₀ o2 ]
          nt-inv = ×⟨ ×⟨ π₁ , π₂ ⋆ π₁ ⟩ , π₂ ⋆ π₂ ⟩

          nt-sec : nt-inv ⋆⟨ C ⟩ nt-o == id C
          nt-sec = prod-unique
            (⋆-assoc >=>
             ⋆-right π₁-reduce >=>
             sym ⋆-assoc >=>
             ⋆-left π₁-reduce >=>
             π₁-reduce >=>
             sym ⋆-left-id)
            (⋆-assoc >=>
             ⋆-right π₂-reduce >=>
             (prod-unique
               (⋆-assoc >=>
                ⋆-right π₁-reduce >=>
                sym ⋆-assoc >=>
                ⋆-left π₁-reduce >=>
                π₂-reduce)
               (⋆-assoc >=>
                ⋆-right π₂-reduce >=>
                π₂-reduce)) >=>
             sym ⋆-left-id)

          nt-ret : nt-o ⋆⟨ C ⟩ nt-inv == id C
          nt-ret = prod-unique
            (⋆-assoc >=>
             ⋆-right π₁-reduce >=>
             (prod-unique
               (⋆-assoc >=>
                ⋆-right π₁-reduce >=>
                π₁-reduce)
               (⋆-assoc >=>
                ⋆-right π₂-reduce >=>
                sym ⋆-assoc >=>
                ⋆-left π₂-reduce >=>
                π₁-reduce)) >=>
             sym ⋆-left-id)
            (⋆-assoc >=>
             ⋆-right π₂-reduce >=>
             sym ⋆-assoc >=>
             ⋆-left π₂-reduce >=>
             π₂-reduce >=>
             sym ⋆-left-id)

        abstract
          is-niso : isIso C nt-o
          is-niso = record { inv = nt-inv ; sec = nt-sec ; ret = nt-ret }

      module _ {x@(triple x0 x1 x2) y@(triple y0 y1 y2) : Obj C3}
               (f@(triple f0 f1 f2) : C3 [ x , y ]) where

        side-l = nt-o x ⋆⟨ C ⟩ (F-mor (RightBiasedDoubleApplicationFunctor ⊗) f)
        side-r = (F-mor (LeftBiasedDoubleApplicationFunctor ⊗) f) ⋆⟨ C ⟩ nt-o y

        abstract
          nt-mor : side-l == side-r
          nt-mor = prod-unique (s0x >=> sym s0y)
                     (prod-unique (s1x >=> sym s1y) (s2x >=> sym s2y))
            where
            s0x : side-l ⋆ π₁ == π₁ ⋆ π₁ ⋆ f0
            s0x =
              ⋆-assoc >=>
              ⋆-right π₁-reduce >=>
              sym ⋆-assoc >=>
              ⋆-left π₁-reduce

            s1x : side-l ⋆ π₂ ⋆ π₁ == π₁ ⋆ π₂ ⋆ f1
            s1x =
              ⋆-left (⋆-assoc >=> ⋆-right π₂-reduce) >=>
              ⋆-assoc >=>
              ⋆-right (⋆-assoc >=> ⋆-right π₁-reduce) >=>
              sym ⋆-assoc >=>
              ⋆-left π₂-reduce >=>
              sym ⋆-assoc >=>
              ⋆-left π₁-reduce

            s2x : side-l ⋆ π₂ ⋆ π₂ == π₂ ⋆ f2
            s2x =
              ⋆-left (⋆-assoc >=> ⋆-right π₂-reduce) >=>
              ⋆-assoc >=>
              ⋆-right (⋆-assoc >=> ⋆-right π₂-reduce) >=>
              sym ⋆-assoc >=>
              ⋆-left π₂-reduce >=>
              sym ⋆-assoc >=>
              ⋆-left π₂-reduce

            s0y : side-r ⋆ π₁ == π₁ ⋆ π₁ ⋆ f0
            s0y =
              ⋆-assoc >=>
              ⋆-right π₁-reduce >=>
              sym ⋆-assoc >=>
              ⋆-left π₁-reduce >=>
              ⋆-assoc >=>
              ⋆-right π₁-reduce >=>
              sym ⋆-assoc

            s1y : side-r ⋆ π₂ ⋆ π₁ == π₁ ⋆ π₂ ⋆ f1
            s1y =
              ⋆-left (⋆-assoc >=> ⋆-right π₂-reduce) >=>
              ⋆-assoc >=>
              ⋆-right π₁-reduce >=>
              sym ⋆-assoc >=>
              ⋆-left π₁-reduce >=>
              ⋆-assoc >=>
              ⋆-right π₂-reduce >=>
              sym ⋆-assoc

            s2y : side-r ⋆ π₂ ⋆ π₂ == π₂ ⋆ f2
            s2y =
              ⋆-left (⋆-assoc >=> ⋆-right π₂-reduce) >=>
              ⋆-assoc >=>
              ⋆-right π₂-reduce >=>
              π₂-reduce

  CartesianMonoidalStr : MonoidalStr C
  CartesianMonoidalStr = record
    { ⊗ = ⊗
    ; unit = unit
    ; unitorˡ = unitorˡ
    ; unitorʳ = unitorʳ
    ; associator = associator
    }
