{-# OPTIONS --cubical --safe --exact-split #-}

module category.monoidal.cartesian where

open import base
open import category.base
open import category.constructions.product
open import category.monoidal.base
open import category.object.product
open import category.object.terminal
open import category.constructions.power
open import equality
open import fin-algebra
open import truncation

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM}
  (prod : ∀ x y -> Product C x y)
  (term : Terminal C)
  (magic : Magic) where
  private
    C2 = ProductCat C C
    C3 = PowerCat C 3

    module C = PreCategory C
    module term = Terminal term

    _⊗₀_ : Obj C -> Obj C -> Obj C
    a ⊗₀ b = Product.obj (prod a b)

    _⊗₁_ : {a b c d : Obj C} ->
         C [ a , b ] ->  C [ c , d ] ->
         C [ a ⊗₀ c , b ⊗₀ d ]
    _⊗₁_ {a} {b} {c} {d} f g =
      bd ×⟨ (Product.π₁ ac) ⋆⟨ C ⟩ f , (Product.π₂ ac) ⋆⟨ C ⟩ g ⟩
      where
      bd = prod b d
      ac = prod a c



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
        ab.unique -- (ab.π₁ ⋆⟨ C ⟩ (id C)) (ab.π₂ ⋆⟨ C ⟩ (id C))
          (C.⋆-left-id _ >=> sym (C.⋆-right-id _))
          (C.⋆-left-id _ >=> sym (C.⋆-right-id _))
        where
        module ab = Product (prod a b)

      ⋆-proof : {a b c : Obj C × Obj C} ->
                (f : C2 [ a , b ]) ->
                (g : C2 [ b , c ]) ->
                proj₁ (f ⋆⟨ C2 ⟩ g) ⊗₁ proj₂ (f ⋆⟨ C2 ⟩ g) ==
                (proj₁ f ⊗₁ proj₂ f) ⋆⟨ C ⟩ (proj₁ g ⊗₁ proj₂ g)
      ⋆-proof {a1 , a2} {b1 , b2} {c1 , c2} f@(f1 , f2) g@(g1 , g2) = c.unique p1 p2
        where
        module a = Product (prod a1 a2)
        module b = Product (prod b1 b2)
        module c = Product (prod c1 c2)
        p1 : (f1 ⊗₁ f2) ⋆⟨ C ⟩ (g1 ⊗₁ g2) ⋆⟨ C ⟩ c.π₁ == a.π₁ ⋆⟨ C ⟩ proj₁ (f ⋆⟨ C2 ⟩ g)
        p1 =
          C.⋆-assocⁱ >=>
          C.⋆-right c.π₁-reduce >=>
          sym C.⋆-assocⁱ >=>
          C.⋆-left b.π₁-reduce >=>
          C.⋆-assocⁱ

        p2 : (f1 ⊗₁ f2) ⋆⟨ C ⟩ (g1 ⊗₁ g2) ⋆⟨ C ⟩ c.π₂ == a.π₂ ⋆⟨ C ⟩ proj₂ (f ⋆⟨ C2 ⟩ g)
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
      { NT-obj = \c -> Product.π₂ (prod unit c)
      ; NT-mor = \f -> sym (Product.π₂-reduce (prod unit _))
      } ,
      niso

      where
      module _ (c : Obj C) where
        module p = Product (prod unit c)
        niso : isIso C p.π₂
        niso .isIso.inv = p.×⟨ term.mor , id C ⟩
        niso .isIso.sec = p.π₂-reduce
        niso .isIso.ret =
          sym (p.unique (term.unique₂ _ _)
                        (C.⋆-assocⁱ >=> C.⋆-right p.π₂-reduce >=> C.⋆-right-id _)) >=>
          (p.unique (C.⋆-left-id _) (C.⋆-left-id _))

    unitorʳ : NaturalIsomorphism (appʳ ⊗ unit) (idF C)
    unitorʳ = record
      { NT-obj = \c -> Product.π₁ (prod c unit)
      ; NT-mor = \f -> sym (Product.π₁-reduce (prod _ unit))
      } ,
      niso

      where
      module _ (c : Obj C) where
        module p = Product (prod c unit)
        niso : isIso C p.π₁
        niso .isIso.inv = p.×⟨ id C , term.mor ⟩
        niso .isIso.sec = p.π₁-reduce
        niso .isIso.ret =
          p.unique₂ (C.⋆-assocⁱ >=> C.⋆-right p.π₁-reduce >=>
                     C.⋆-right-id _ >=> sym (C.⋆-left-id _))
                    (term.unique₂ _ _)


    associator : NaturalIsomorphism (LeftBiasedDoubleApplicationFunctor ⊗)
                                    (RightBiasedDoubleApplicationFunctor ⊗)
    associator = record
      { NT-obj = nt-o
      ; NT-mor = nt-mor
      } ,
      is-niso
      where

      i0 : FinT 3
      i0 = inj-l tt
      i1 : FinT 3
      i1 = inj-r (inj-l tt)
      i2 : FinT 3
      i2 = inj-r (inj-r (inj-l tt))

      module _ (o : Obj C3) where
        private
          o0 = o i0
          o1 = o i1
          o2 = o i2

          module p01 = Product (prod o0 o1)
          module p12 = Product (prod o1 o2)
          module p0-12 = Product (prod o0 p12.obj)
          module p01-2 = Product (prod p01.obj o2)

        nt-o : C [ (o0 ⊗₀ o1) ⊗₀ o2 , o0 ⊗₀ (o1 ⊗₀ o2) ]
        nt-o = p0-12.×⟨ (p01-2.π₁ ⋆⟨ C ⟩ p01.π₁) ,
                        p12.×⟨ (p01-2.π₁ ⋆⟨ C ⟩ p01.π₂) , p01-2.π₂ ⟩ ⟩

        private
          nt-inv : C [ o0 ⊗₀ (o1 ⊗₀ o2) , (o0 ⊗₀ o1) ⊗₀ o2 ]
          nt-inv = p01-2.×⟨ p01.×⟨ p0-12.π₁ , p0-12.π₂ ⋆⟨ C ⟩ p12.π₁ ⟩ ,
                            p0-12.π₂ ⋆⟨ C ⟩ p12.π₂ ⟩

          nt-sec : nt-inv ⋆⟨ C ⟩ nt-o == id C
          nt-sec = p0-12.unique₂
            (C.⋆-assocⁱ >=>
             C.⋆-right p0-12.π₁-reduce >=>
             sym C.⋆-assocⁱ >=>
             C.⋆-left p01-2.π₁-reduce >=>
             p01.π₁-reduce >=>
             sym (C.⋆-left-id _))
            (C.⋆-assocⁱ >=>
             C.⋆-right p0-12.π₂-reduce >=>
             (p12.unique₂
               (C.⋆-assocⁱ >=>
                C.⋆-right p12.π₁-reduce >=>
                sym C.⋆-assocⁱ >=>
                C.⋆-left p01-2.π₁-reduce >=>
                p01.π₂-reduce)
               (C.⋆-assocⁱ >=>
                C.⋆-right p12.π₂-reduce >=>
                p01-2.π₂-reduce)) >=>
             sym (C.⋆-left-id _))

          nt-ret : nt-o ⋆⟨ C ⟩ nt-inv == id C
          nt-ret = p01-2.unique₂
            (C.⋆-assocⁱ >=>
             C.⋆-right p01-2.π₁-reduce >=>
             (p01.unique₂
               (C.⋆-assocⁱ >=>
                C.⋆-right p01.π₁-reduce >=>
                p0-12.π₁-reduce)
               (C.⋆-assocⁱ >=>
                C.⋆-right p01.π₂-reduce >=>
                sym C.⋆-assocⁱ >=>
                C.⋆-left p0-12.π₂-reduce >=>
                p12.π₁-reduce)) >=>
             sym (C.⋆-left-id _))
            (C.⋆-assocⁱ >=>
             C.⋆-right p01-2.π₂-reduce >=>
             sym C.⋆-assocⁱ >=>
             C.⋆-left p0-12.π₂-reduce >=>
             p12.π₂-reduce >=>
             sym (C.⋆-left-id _))

        abstract
          is-niso : isIso C nt-o
          is-niso = record { inv = nt-inv ; sec = nt-sec ; ret = nt-ret }

      module _ {x y : Obj C3} (f : C3 [ x , y ]) where
        x0 = x i0
        x1 = x i1
        x2 = x i2
        y0 = y i0
        y1 = y i1
        y2 = y i2
        f0 = f i0
        f1 = f i1
        f2 = f i2

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
