{-# OPTIONS --cubical --safe --exact-split #-}

module category.iterated-product-eq where

open import base
open import category.base
open import category.adjunction
open import category.functor
open import category.term-product-eq
open import category.constructions.iterated-product
open import category.constructions.product
open import nat
open import additive-group
open import additive-group.instances.nat

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) (magic : Magic) where
  private
    PC : (n : Nat) -> PreCategory ℓO ℓM
    PC n = IteratedProductC C n
    PPC : (n m : Nat) -> PreCategory ℓO ℓM
    PPC n m = ProductCat (PC n) (PC m)

  split-PC : (n m : Nat) -> Functor (PC (n + m)) (PPC n m)
  split-PC =
    \n m -> record
      { obj = obj' n m
      ; mor = mor' n m
      ; id = \_ -> id' n m
      ; ⋆ = ⋆' n m
      }
    where
    obj' : (n m : Nat) -> Obj (PC (n + m)) -> Obj (PC n) × Obj (PC m)
    obj' zero m cs = (lift tt) , cs
    obj' (suc n) m (c , cs) =
      let (ns , ms) = obj' n m cs in
      (c , ns) , ms

    mor' : (n m : Nat) -> {o1 o2 : Obj (PC (n + m))} ->
           (PC (n + m)) [ o1 , o2 ] ->
           (PPC n m) [ obj' n m o1 , obj' n m o2 ]
    mor' zero m fm = lift tt , fm
    mor' (suc n) m (f , fs) =
      let (ns , ms) = mor' n m fs in
      (f , ns) , ms

    id' : (n m : Nat) -> {o : Obj (PC (n + m))} ->
          (mor' n m (idᵉ (PC (n + m)) o)) == (id (PC n) , id (PC m))
    id' zero m = refl
    id' (suc n) m =
      let rp = id' n m in
      \i -> (id C , proj₁ (rp i)) , proj₂ (rp i)

    ⋆' : (n m : Nat) {o1 o2 o3 : Obj (PC (n + m))}
         (f1 : PC (n + m) [ o1 , o2 ])
         (f2 : PC (n + m) [ o2 , o3 ]) ->
         mor' n m (f1 ⋆⟨ PC (n + m) ⟩ f2) ==
         mor' n m f1 ⋆⟨ PPC n m ⟩ mor' n m f2
    ⋆' zero m f1 f2 = refl
    ⋆' (suc n) m (f1 , fs1) (f2 , fs2) =
      let rp = ⋆' n m fs1 fs2 in
      \i -> (f1 ⋆⟨ C ⟩ f2 , (proj₁ (rp i))) , (proj₂ (rp i))
