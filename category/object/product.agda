{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.product where

open import base
open import category.base
open import equality
open import hlevel
open import truncation

module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  record Product (a b : Obj C) : Type (ℓ-max ℓO ℓM) where
    field
      obj : Obj C
      π₁ : C [ obj , a ]
      π₂ : C [ obj , b ]

      universal : {c : Obj C} (f : C [ c , a ]) (g : C [ c , b ]) ->
                  ∃![ h ∈ C [ c , obj ] ] (h ⋆⟨ C ⟩ π₁ == f × h ⋆⟨ C ⟩ π₂ == g)

    ×⟨_,_⟩ : {c : Obj C} (f : C [ c , a ]) (g : C [ c , b ]) -> C [ c , obj ]
    ×⟨ f , g ⟩ = ∃!-val (universal f g)

    abstract
      unique : {c : Obj C} {f : C [ c , a ]} {g : C [ c , b ]} {h : C [ c , obj ]} ->
        h ⋆⟨ C ⟩ π₁ == f ->
        h ⋆⟨ C ⟩ π₂ == g ->
        ×⟨ f , g ⟩ == h
      unique {f = f} {g} {h} p1 p2 = ∃!-unique (universal f g) h (p1 , p2)

      unique₂ : {c : Obj C} {f : C [ c , obj ]} {g : C [ c , obj ]} ->
        f ⋆⟨ C ⟩ π₁ == g ⋆⟨ C ⟩ π₁ ->
        f ⋆⟨ C ⟩ π₂ == g ⋆⟨ C ⟩ π₂ ->
        f == g
      unique₂ p1 p2 = sym (unique p1 p2) >=> unique refl refl

      π₁-reduce : {c : Obj C} {f : C [ c , a ]} {g : C [ c , b ]} ->
                  ×⟨ f , g ⟩ ⋆⟨ C ⟩ π₁ == f
      π₁-reduce = proj₁ (∃!-prop (universal _ _))
      π₂-reduce : {c : Obj C} {f : C [ c , a ]} {g : C [ c , b ]} ->
                  ×⟨ f , g ⟩ ⋆⟨ C ⟩ π₂ == g
      π₂-reduce = proj₂ (∃!-prop (universal _ _))


module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} where
  open CategoryHelpers C

  module _ {a b : Obj C}  where
    _×⟨_,_⟩ : (p : Product C a b) {c : Obj C} (f : C [ c , a ]) (g : C [ c , b ]) ->
              C [ c , Product.obj p ]
    _×⟨_,_⟩ = Product.×⟨_,_⟩


  module _ {a b : Obj C} {p1 p2 : Product C a b} where
    product-path : (op : Product.obj p1 == Product.obj p2) ->
                   (PathP (\ i -> C [ op i , a ]) (Product.π₁ p1) (Product.π₁ p2)) ->
                   (PathP (\ i -> C [ op i , b ]) (Product.π₂ p1) (Product.π₂ p2)) ->
                   p1 == p2
    product-path op pp1 pp2 i .Product.obj = op i
    product-path op pp1 pp2 i .Product.π₁ = pp1 i
    product-path op pp1 pp2 i .Product.π₂ = pp2 i
    product-path op pp1 pp2 i .Product.universal f g =
      isProp->PathPᵉ
        (\i -> isProp-isContr {A = Σ[ h ∈ (C [ _ , op i ]) ]
                                     (h ⋆ pp1 i == f ×
                                      h ⋆ pp2 i == g)})
        (Product.universal p1 f g) (Product.universal p2 f g) i


  module _ {a b : Obj C} (p1 p2 : Product C a b) where
    private
      module p1 = Product p1
      module p2 = Product p2

    products->iso : CatIso C p1.obj p2.obj
    products->iso .CatIso.mor = p2.×⟨ p1.π₁ , p1.π₂ ⟩
    products->iso .CatIso.inv = p1.×⟨ p2.π₁ , p2.π₂ ⟩
    products->iso .CatIso.sec =
      cong fst (isContr->isProp (p2.universal p2.π₁ p2.π₂)
                                (_ , ans1 , ans2) (_ , ⋆-left-id , ⋆-left-id))
      where
      ans1 : p1.×⟨ p2.π₁ , p2.π₂ ⟩ ⋆ p2.×⟨ p1.π₁ , p1.π₂ ⟩ ⋆ p2.π₁ == p2.π₁
      ans1 =
        ⋆-assoc >=>
        ⋆-cong refl p2.π₁-reduce >=>
        p1.π₁-reduce

      ans2 : p1.×⟨ p2.π₁ , p2.π₂ ⟩ ⋆ p2.×⟨ p1.π₁ , p1.π₂ ⟩ ⋆ p2.π₂ == p2.π₂
      ans2 =
        ⋆-assoc >=>
        ⋆-cong refl p2.π₂-reduce >=>
        p1.π₂-reduce
    products->iso .CatIso.ret =
      cong fst (isContr->isProp (p1.universal p1.π₁ p1.π₂)
                                (_ , ans1 , ans2) (_ , ⋆-left-id , ⋆-left-id))
      where
      ans1 : p2.×⟨ p1.π₁ , p1.π₂ ⟩ ⋆ p1.×⟨ p2.π₁ , p2.π₂ ⟩ ⋆ p1.π₁ == p1.π₁
      ans1 =
        ⋆-assoc >=>
        ⋆-cong refl p1.π₁-reduce >=>
        p2.π₁-reduce

      ans2 : p2.×⟨ p1.π₁ , p1.π₂ ⟩ ⋆ p1.×⟨ p2.π₁ , p2.π₂ ⟩ ⋆ p1.π₂ == p1.π₂
      ans2 =
        ⋆-assoc >=>
        ⋆-cong refl p1.π₂-reduce >=>
        p2.π₂-reduce
