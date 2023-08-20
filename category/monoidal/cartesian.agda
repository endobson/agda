{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.cartesian where

open import base
open import category.base
open import category.constructions.product
open import category.constructions.triple-product
open import category.monoidal.base
open import category.object.product
open import category.object.terminal
open import equality hiding (begin_ ; _end)
open import fin-algebra
open import truncation
open import category.zipper

module _ {ℓO ℓM : Level} {C@(record {}) : PreCategory ℓO ℓM}
  (prod : ∀ x y -> Product C x y)
  (term : Terminal C)
  (magic : Magic) where
  private
    C2 = ProductCat C C
    C3 = TripleCat C C C

    module C = PreCategory C
    module term = Terminal term

    module _ {x y : Obj C} where
      open Product (prod x y) 
        using (π₁ ; π₂ ; π₁-reduce ; π₂-reduce ; ×⟨_,_⟩) 
        renaming (unique₂ to prod-unique)
        public
    open PreCategory C using (_⋆_)


    _⊗₀_ : Obj C -> Obj C -> Obj C
    a ⊗₀ b = Product.obj (prod a b)

    _⊗₁_ : {a b c d : Obj C} ->
           C [ a , b ] ->  C [ c , d ] ->
           C [ a ⊗₀ c , b ⊗₀ d ]
    _⊗₁_ {a} {b} {c} {d} f g = ×⟨ π₁ ⋆ f , π₂ ⋆ g ⟩


    ⊗ : BiFunctor C C C
    ⊗ = record
      { obj = \ (a , b) -> a ⊗₀ b
      ; mor = \ (f , g) -> f ⊗₁ g
      ; id = \ (a , b) -> id-proof a b
      ; ⋆ = ⋆-proof
      }
      where
      id-proof : (a b : Obj C) -> (idᵉ C a) ⊗₁ (idᵉ C b) == (idᵉ C (a ⊗₀ b))
      id-proof a b =
        Product.unique (prod a b)
          (C.⋆-left-id _ >=> sym (C.⋆-right-id _))
          (C.⋆-left-id _ >=> sym (C.⋆-right-id _))

      ⋆-proof : {a b c : Obj C × Obj C} ->
                (f : C2 [ a , b ]) ->
                (g : C2 [ b , c ]) ->
                proj₁ (f ⋆⟨ C2 ⟩ g) ⊗₁ proj₂ (f ⋆⟨ C2 ⟩ g) ==
                (proj₁ f ⊗₁ proj₂ f) ⋆ (proj₁ g ⊗₁ proj₂ g)
      ⋆-proof {a1 , a2} {b1 , b2} {c1 , c2} f@(f1 , f2) g@(g1 , g2) = c.unique p1 p2
        where
        module a = Product (prod a1 a2)
        module b = Product (prod b1 b2)
        module c = Product (prod c1 c2)
        -- p1' : (f1 ⊗₁ f2) ⋆⟨ C ⟩ (g1 ⊗₁ g2) ⋆⟨ C ⟩ c.π₁ == a.π₁ ⋆⟨ C ⟩ proj₁ (f ⋆⟨ C2 ⟩ g)
        -- p1' = zrule C (
        --   right⇒ >z>
        --   shift⇐ >z>
        --   z-cong c.π₁-reduce >z>
        --   shift⇒ >z>
        --   z-cong b.π₁-reduce >z>
        --   shift⇐ >z>
        --   left⇒)
          
        p1 : (f1 ⊗₁ f2) ⋆ (g1 ⊗₁ g2) ⋆ π₁ == π₁ ⋆ (f1 ⋆ g1)
        p1 = 
          C.⋆-assocⁱ >=>
          C.⋆-right c.π₁-reduce >=>
          sym C.⋆-assocⁱ >=>
          C.⋆-left b.π₁-reduce >=>
          C.⋆-assocⁱ

        p2 : (f1 ⊗₁ f2) ⋆ (g1 ⊗₁ g2) ⋆ π₂ == π₂ ⋆ (f2 ⋆ g2)
        p2 =
          C.⋆-assocⁱ >=>
          C.⋆-right c.π₂-reduce >=>
          sym C.⋆-assocⁱ >=>
          C.⋆-left b.π₂-reduce >=>
          C.⋆-assocⁱ

    unit : Obj C
    unit = Terminal.obj term

    unitorˡ : NaturalIsomorphism (appˡ ⊗ unit) (idF C)
    unitorˡ = record
      { NT-obj = \c -> π₂
      ; NT-mor = \f -> sym π₂-reduce
      } ,
      niso

      where
      module _ (c : Obj C) where
        niso : isIso C π₂
        niso .isIso.inv = ×⟨ term.mor , id C ⟩
        niso .isIso.sec = π₂-reduce
        niso .isIso.ret =
          prod-unique (term.unique₂ _ _)
                      (C.⋆-assocⁱ >=> C.⋆-right π₂-reduce >=> 
                       C.⋆-right-id _ >=> sym (C.⋆-left-id _))

    unitorʳ : NaturalIsomorphism (appʳ ⊗ unit) (idF C)
    unitorʳ = record
      { NT-obj = \c -> π₁
      ; NT-mor = \f -> sym π₁-reduce
      } ,
      niso

      where
      module _ (c : Obj C) where
        niso : isIso C π₁
        niso .isIso.inv = ×⟨ id C , term.mor ⟩
        niso .isIso.sec = π₁-reduce
        niso .isIso.ret =
          prod-unique (C.⋆-assocⁱ >=> C.⋆-right π₁-reduce >=>
                       C.⋆-right-id _ >=> sym (C.⋆-left-id _))
                      (term.unique₂ _ _)


    associator : NaturalIsomorphism (LeftBiasedDoubleApplicationFunctor ⊗)
                                    (RightBiasedDoubleApplicationFunctor ⊗)
    associator = record
      { NT-obj = nt-o
      ; NT-mor = magic -- nt-mor
      } ,
      is-niso
      where

      module _ (o@(triple o0 o1 o2) : Obj C3) where
        nt-o : C [ (o0 ⊗₀ o1) ⊗₀ o2 , o0 ⊗₀ (o1 ⊗₀ o2) ]
        nt-o = ×⟨ (π₁ ⋆ π₁) , ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⟩

        private
          open ZReasoning C

          nt-inv : C [ o0 ⊗₀ (o1 ⊗₀ o2) , (o0 ⊗₀ o1) ⊗₀ o2 ]
          nt-inv = ×⟨ ×⟨ π₁ , π₂ ⋆ π₁ ⟩ , π₂ ⋆ π₂ ⟩


          sub1 : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
          sub1 = 
            (begin
              [ []           , nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁   ,       [] ]=< right⇒ >
              [ []           , nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩        , π₁ :: [] ]=< shift⇐ >
              [ [] :: nt-inv , ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁            ,       [] ]=< z-cong π₁-reduce >
              [ [] :: nt-inv , π₁ ⋆ π₂                           ,       [] ]=< shift⇒ >
              [ []           , nt-inv ⋆ π₁                       , π₂ :: [] ]=< z-cong π₁-reduce >
              [ []           , ×⟨ π₁ , π₂ ⋆ π₁ ⟩                 , π₂ :: [] ]=< right⇐ >
              [ []           , ×⟨ π₁ , π₂ ⋆ π₁ ⟩ ⋆ π₂            ,       [] ]=< z-cong π₂-reduce >
              [ []           , π₂ ⋆ π₁                           ,       [] ]end)
          sub1' : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
          sub1' = 
            (begin
              [ []           , _                                  ,       [] ]=< right⇒ >
              [ []           , _                                  , π₁ :: [] ]=< shift⇐ >
              [ [] :: nt-inv , _                                  ,       [] ]=< z-cong π₁-reduce >
              [ [] :: nt-inv , _                                  ,       [] ]=< shift⇒ >
              [ []           , _                                  , π₂ :: [] ]=< z-cong π₁-reduce >
              [ []           , _                                  , π₂ :: [] ]=< right⇐ >
              [ []           , _                                  ,       [] ]=< z-cong π₂-reduce >
              [ []           , _                                  ,       [] ]end)

          sub1'' : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
          sub1'' = 
            (begin
              []=< right⇒ >
              []=< shift⇐ >
              []=< z-cong π₁-reduce >
              []=< shift⇒ >
              []=< z-cong π₁-reduce >
              []=< right⇐ >
              []=< z-cong π₂-reduce >
              []end)

          sub1-no-zip : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₁ == π₂ ⋆ π₁
          sub1-no-zip = 
             (C.⋆-assocⁱ >=>
              C.⋆-right π₁-reduce >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left π₁-reduce >=>
              π₂-reduce)


          sub2 : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₂ == π₂ ⋆ π₂
          sub2 = 
            (begin
              [ []           , nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₂   ,       [] ]=< right⇒ >
              [ []           , nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩        , π₂ :: [] ]=< shift⇐ >
              [ [] :: nt-inv , ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ⋆ π₂            ,       [] ]=< z-cong π₂-reduce >
              [ [] :: nt-inv , π₂                                ,       [] ]=< left⇒ >
              [ []           , nt-inv ⋆ π₂                       ,       [] ]=< z-cong π₂-reduce >
              [ []           , π₂ ⋆ π₂                           ,       [] ]end) 


          lemma1 : nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ == π₂
          lemma1 = prod-unique sub1 sub2


          nt-sec : nt-inv ⋆⟨ C ⟩ nt-o == id C
          nt-sec = 
            prod-unique
            (begin
             [ []           , (nt-inv ⋆ nt-o) ⋆ π₁   ,       [] ]=< right⇒ >
             [ []           , nt-inv ⋆ nt-o          , π₁ :: [] ]=< left⇐ >
             [ [] :: nt-inv , nt-o                   , π₁ :: [] ]=< right⇐ >
             [ [] :: nt-inv , nt-o ⋆ π₁              ,       [] ]=< z-cong π₁-reduce >
             [ [] :: nt-inv , π₁ ⋆ π₁                ,       [] ]=< shift⇒ >
             [ []           , nt-inv ⋆ π₁            , π₁ :: [] ]=< z-cong π₁-reduce >
             [ []           , ×⟨ π₁ , π₂ ⋆ π₁ ⟩      , π₁ :: [] ]=< right⇐ >
             [ []           , ×⟨ π₁ , π₂ ⋆ π₁ ⟩ ⋆ π₁ ,       [] ]=< z-cong π₁-reduce >
             [ []           , π₁                     ,       [] ]=< z-cong (sym (C.⋆-left-id _)) >
             [ []           , id C ⋆ π₁              ,       [] ]end)
            (begin
             [ []           , (nt-inv ⋆ nt-o) ⋆ π₂       ,       [] ]=< right⇒ >
             [ []           , (nt-inv ⋆ nt-o)            , π₂ :: [] ]=< shift⇐ >
             [ [] :: nt-inv , nt-o ⋆ π₂                  ,       [] ]=< z-cong π₂-reduce >
             [ [] :: nt-inv , ×⟨ π₁ ⋆ π₂ , π₂ ⟩          ,       [] ]=< left⇒ >
             [ []           , nt-inv ⋆ ×⟨ π₁ ⋆ π₂ , π₂ ⟩ ,       [] ]=< z-cong lemma1 >
             [ []           , π₂                         ,       [] ]=< z-cong (sym (C.⋆-left-id _)) >
             [ []           , id C ⋆ π₂                  ,       [] ]end)

          nt-ret : nt-o ⋆⟨ C ⟩ nt-inv == id C
          nt-ret = prod-unique
            (C.⋆-assocⁱ >=>
             C.⋆-right π₁-reduce >=>
             (prod-unique
               (C.⋆-assocⁱ >=>
                C.⋆-right π₁-reduce >=>
                π₁-reduce)
               (C.⋆-assocⁱ >=>
                C.⋆-right π₂-reduce >=>
                sym C.⋆-assocⁱ >=>
                C.⋆-left π₂-reduce >=>
                π₁-reduce)) >=>
             sym (C.⋆-left-id _))
            (C.⋆-assocⁱ >=>
             C.⋆-right π₂-reduce >=>
             sym C.⋆-assocⁱ >=>
             C.⋆-left π₂-reduce >=>
             π₂-reduce >=>
             sym (C.⋆-left-id _))

        abstract
          is-niso : isIso C nt-o
          is-niso = record { inv = nt-inv ; sec = nt-sec ; ret = nt-ret }

{-
      module _ {x@(triple x0 x1 x2) y@(triple y0 y1 y2) : Obj C3}
               (f@(triple f0 f1 f2) : C3 [ x , y ]) where

        module px01 = Product (prod x0 x1)
        module px12 = Product (prod x1 x2)
        module px0-12 = Product (prod x0 px12.obj)
        module px01-2 = Product (prod px01.obj x2)
        module py01 = Product (prod y0 y1)
        module py12 = Product (prod y1 y2)
        module py0-12 = Product (prod y0 py12.obj)
        module py01-2 = Product (prod py01.obj y2)

        side-l = nt-o x ⋆⟨ C ⟩ (F-mor (RightBiasedDoubleApplicationFunctor ⊗) f)
        side-r = (F-mor (LeftBiasedDoubleApplicationFunctor ⊗) f) ⋆⟨ C ⟩ nt-o y

        abstract
          nt-mor : side-l == side-r
          nt-mor = py0-12.unique₂ (s0x >=> sym s0y)
                     (py12.unique₂ (s1x >=> sym s1y) (s2x >=> sym s2y))
            where
            s0x : side-l ⋆⟨ C ⟩ py0-12.π₁ == px01-2.π₁ ⋆⟨ C ⟩ px01.π₁ ⋆⟨ C ⟩ f0
            s0x =
              C.⋆-assocⁱ >=>
              C.⋆-right py0-12.π₁-reduce >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left px0-12.π₁-reduce


            s1x : side-l ⋆⟨ C ⟩ py0-12.π₂ ⋆⟨ C ⟩ py12.π₁ == px01-2.π₁ ⋆⟨ C ⟩ px01.π₂ ⋆⟨ C ⟩ f1
            s1x =
              C.⋆-left (C.⋆-assocⁱ >=> C.⋆-right py0-12.π₂-reduce) >=>
              C.⋆-assocⁱ >=>
              C.⋆-right (C.⋆-assocⁱ >=> C.⋆-right py12.π₁-reduce) >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left px0-12.π₂-reduce >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left px12.π₁-reduce

            s2x : side-l ⋆⟨ C ⟩ py0-12.π₂ ⋆⟨ C ⟩ py12.π₂ == px01-2.π₂ ⋆⟨ C ⟩ f2
            s2x =
              C.⋆-left (C.⋆-assocⁱ >=> C.⋆-right py0-12.π₂-reduce) >=>
              C.⋆-assocⁱ >=>
              C.⋆-right (C.⋆-assocⁱ >=> C.⋆-right py12.π₂-reduce) >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left px0-12.π₂-reduce >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left px12.π₂-reduce

            s0y : side-r ⋆⟨ C ⟩ py0-12.π₁ == px01-2.π₁ ⋆⟨ C ⟩ px01.π₁ ⋆⟨ C ⟩ f0
            s0y =
              C.⋆-assocⁱ >=>
              C.⋆-right py0-12.π₁-reduce >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left py01-2.π₁-reduce >=>
              C.⋆-assocⁱ >=>
              C.⋆-right py01.π₁-reduce >=>
              sym C.⋆-assocⁱ

            s1y : side-r ⋆⟨ C ⟩ py0-12.π₂ ⋆⟨ C ⟩ py12.π₁ ==
                  px01-2.π₁ ⋆⟨ C ⟩ px01.π₂ ⋆⟨ C ⟩ f1
            s1y =
              C.⋆-left (C.⋆-assocⁱ >=> C.⋆-right py0-12.π₂-reduce) >=>
              C.⋆-assocⁱ >=>
              C.⋆-right py12.π₁-reduce >=>
              sym C.⋆-assocⁱ >=>
              C.⋆-left py01-2.π₁-reduce >=>
              C.⋆-assocⁱ >=>
              C.⋆-right py01.π₂-reduce >=>
              sym C.⋆-assocⁱ

            s2y : side-r ⋆⟨ C ⟩ py0-12.π₂ ⋆⟨ C ⟩ py12.π₂ == px01-2.π₂ ⋆⟨ C ⟩ f2
            s2y =
              C.⋆-left (C.⋆-assocⁱ >=> C.⋆-right py0-12.π₂-reduce) >=>
              C.⋆-assocⁱ >=>
              C.⋆-right py12.π₂-reduce >=>
              py01-2.π₂-reduce

  CartesianMonoidalStr : MonoidalStr C
  CartesianMonoidalStr = record
    { ⊗ = ⊗
    ; unit = unit
    ; unitorˡ = unitorˡ
    ; unitorʳ = unitorʳ
    ; associator = associator
    }
-}
