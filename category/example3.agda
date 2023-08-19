{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.example3 where

open import additive-group
open import additive-group.instances.nat
open import base
open import category.adjunction
open import category.base
open import category.constructions.functor-cat
open import category.constructions.iterated-product
open import category.constructions.product
open import category.displayed
open import category.example2
open import category.functor
open import category.natural-transformation
open import category.monoidal.base
open import hlevel
open import nat

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) (M : MonoidalStr C) (magic : Magic) where
  open MonoidalStrHelpers M

  product-NT : {ℓOB ℓMB ℓOC ℓMC ℓOD ℓMD ℓOE ℓME : Level}
               {B : PreCategory ℓOB ℓMB}
               {C : PreCategory ℓOC ℓMC}
               {D : PreCategory ℓOD ℓMD}
               {E : PreCategory ℓOE ℓME}
               {f1 f2 : Functor B C}
               {f3 f4 : Functor D E} ->
               NaturalTransformation f1 f2 -> NaturalTransformation f3 f4 ->
               NaturalTransformation (product-functor f1 f3) (product-functor f2 f4)
  product-NT = magic


  PC : (n : Nat) -> PreCategory ℓO ℓM
  PC n = IteratedProductC C n

  FC : (n : Nat) -> PreCategory (ℓ-max ℓO ℓM) (ℓ-max ℓO ℓM)
  FC n = FunctorC (PC n) C

  C5 : PreCategory (ℓ-max ℓO ℓM) (ℓ-max ℓO ℓM)
  C5 = UnionC (isOfHLevelSuc 2 isSetNat) FC

  split-PC-Obj : (n m : Nat) -> Obj (PC (n + m)) -> Obj (PC n) × Obj (PC m)
  split-PC-Obj zero m cs = (lift tt) , cs
  split-PC-Obj (suc n) m (c , cs) =
    let (ns , ms) = split-PC-Obj n m cs in
    (c , ns) , ms

  split-PC-Mor : (n m : Nat) -> (o1 o2 : Obj (PC (n + m))) -> (PC (n + m)) [ o1 , o2 ] ->
                 ((PC n) [ proj₁ (split-PC-Obj n m o1) , proj₁ (split-PC-Obj n m o2) ] ×
                  (PC m) [ proj₂ (split-PC-Obj n m o1) , proj₂ (split-PC-Obj n m o2) ])
  split-PC-Mor = magic


  split-PC : (n m : Nat) -> Functor (PC (n + m)) (ProductCat (PC n) (PC m))
  split-PC = magic


  ▪₀' : (n m : Nat) -> Obj (FC n) -> Obj (FC m) -> Obj (FC (n + m))
  ▪₀' n m fn fm = (split-PC n m) ⋆F ((product-functor fn fm) ⋆F ⊗)

  --▪₁' : (n m : Nat) -> {a c : Obj (FC n)} {b d :
  --       C5 [ a , b ] -> C5 [ c , d ] -> C5 [ (a ▪₀ c) , (b ▪₀ d) ]
  --▪₁' {a , fa} {b , fb} {c , fc} {d , fd} (refl-=== , nt1) (refl-=== , nt2) =
  --  refl-=== , (split-PC a c) NT◀ ((product-NT nt1 nt2) NT▶ ⊗)


  _▪₀_ : Obj C5 -> Obj C5 -> Obj C5
  _▪₀_ (n , fn) (m , fm) = n + m , (▪₀' n m fn fm)

  _▪₁_ : {a b c d : Obj C5} ->
         C5 [ a , b ] -> C5 [ c , d ] -> C5 [ (a ▪₀ c) , (b ▪₀ d) ]
  _▪₁_ {a , fa} {b , fb} {c , fc} {d , fd} (refl-=== , nt1) (refl-=== , nt2) =
    refl-=== , (split-PC a c) NT◀ ((product-NT nt1 nt2) NT▶ ⊗)


  -- ▪-id' : {n : Nat} {a b : Obj (FC n)} {b : Obj (FC n)} ->
  --         (n , idᵉ (FC n) a) ▪₁ (idᵉ C5 b) == (idᵉ C5 (a ▪₀ b))
  -- ▪-id' = natural-transformation-path _ _ ?
