{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.product where

open import base
open import category.base
open import category.univalent
open import equality
open import equality.identity-system
open import hlevel
open import truncation

module _ {ℓO ℓM} (C : PreCategory ℓO ℓM) where
  isProduct : (a b : Obj C) (p : Obj C) (π₁ : C [ p , a ]) (π₂ : C [ p , b ]) -> Type _
  isProduct a b p π₁ π₂ =
    {c : Obj C} (f : C [ c , a ]) (g : C [ c , b ]) ->
       ∃![ h ∈ C [ c , p ] ] (h ⋆⟨ C ⟩ π₁ == f × h ⋆⟨ C ⟩ π₂ == g)

  isProp-isProduct : {a b : Obj C} {p : Obj C} {π₁ : C [ p , a ]} {π₂ : C [ p , b ]} ->
                     isProp (isProduct a b p π₁ π₂)
  isProp-isProduct = isPropΠⁱ (\_ -> isPropΠ2 (\_ _ -> isProp-isContr))

  record Product (a b : Obj C) : Type (ℓ-max ℓO ℓM) where
    field
      obj : Obj C
      π₁ : C [ obj , a ]
      π₂ : C [ obj , b ]
      universal : isProduct a b obj π₁ π₂

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

  hasProducts : Type (ℓ-max ℓO ℓM)
  hasProducts = ∀ a b -> Product a b

module ProductHelpers {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} {a b : Obj C}
                      (P : Product C a b) where
  open Product P
    using ( π₁ ; π₂ ; π₁-reduce ; π₂-reduce ; ×⟨_,_⟩ )
    renaming (unique₂ to prod-unique)
    public


module _ {ℓO ℓM} {C : PreCategory ℓO ℓM} where
  open CategoryHelpers C

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


    module _ (univ : isUnivalent' C) where
      private
        iso : CatIso C p1.obj p2.obj
        iso = products->iso

        p : Path (Obj C) p1.obj p2.obj
        p = isIdentitySystem.to-path univ iso

        pp : PathP (\i -> CatIso C p1.obj (p i)) (idCatIso C p1.obj) iso
        pp = isIdentitySystem.to-path-over univ iso

        pp-π₁ : PathP (\i -> C [ (p i) , a ]) p1.π₁ p2.π₁
        pp-π₁ = transP-mid (sym ⋆-left-id) (\i -> CatIso.inv (pp i) ⋆ p1.π₁) p1.π₁-reduce
        pp-π₂ : PathP (\i -> C [ (p i) , b ]) p1.π₂ p2.π₂
        pp-π₂ = transP-mid (sym ⋆-left-id) (\i -> CatIso.inv (pp i) ⋆ p1.π₂) p1.π₂-reduce

      opaque
        isProp-Product : p1 == p2
        isProp-Product = product-path p pp-π₁ pp-π₂
