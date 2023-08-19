{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module tree-solver where

open import base
open import relation
open import list.base
open import sigma
open import truncation

private
  variable
    ℓ : Level
    A B : Type ℓ

data Tree {ℓ : Level} (A : Type ℓ) : Type ℓ where
  _▪_ : Tree A -> Tree A -> Tree A
  𝒾 : A -> Tree A
  ε : Tree A

normal-form : Tree A -> List A
normal-form ε = []
normal-form (𝒾 a) = [ a ]
normal-form (t1 ▪ t2) = normal-form t1 ++ normal-form t2

data isNormalForm {ℓ : Level} {A : Type ℓ} : (Tree A) -> (List A) -> Type (levelOf A) where
  _▪_ : {t1 t2 : Tree A} {l1 l2 : List A} -> 
        isNormalForm t1 l1 -> isNormalForm t2 l2 -> 
        isNormalForm (t1 ▪ t2) (l1 ++ l2)
  𝒾 : (a : A) -> isNormalForm (𝒾 a) [ a ]
  ε : isNormalForm ε []

∃!normal-form : (t : Tree A) -> ∃![ l ∈ List A ] (isNormalForm t l)
∃!normal-form t = 
  (normal-form t , isNF t) , (\ (l , nf-l) -> unique t l nf-l)
  where
  isNF : ∀ t -> isNormalForm t (normal-form t)
  isNF ε = ε
  isNF (𝒾 a) = (𝒾 a)
  isNF (t1 ▪ t2) = (isNF t1 ▪ isNF t2)

  unique : ∀ t l -> (nf-l : isNormalForm t l) -> (normal-form t , isNF t) == (l , nf-l)
  unique ε [] ε = refl
  unique (𝒾 a) (a :: []) (𝒾 a) = refl
  unique (t1 ▪ t2) _ (nf1 ▪ nf2) = 
    let r1 = unique t1 _ nf1 in
    let r2 = unique t2 _ nf2 in
    \i -> fst (r1 i) ++ fst (r2 i) , snd (r1 i) ▪ snd (r2 i)

record Zipper (A : Type ℓ) : Type ℓ where
  constructor zipper
  field
    left : List A
    center : Tree A
    right : List A


data ZipperRule {A : Type ℓ} : Zipper A -> Zipper A -> Type ℓ where
  left⇒ : {a : A} {l : List A} {c : Tree A} {r : List A} -> 
          ZipperRule (zipper (a :: l) c r) (zipper l ((𝒾 a) ▪ c) r)
  left⇐ : {a : A} {l : List A} {c : Tree A} {r : List A} -> 
          ZipperRule (zipper l ((𝒾 a) ▪ c) r) (zipper (a :: l) c r) 
  right⇐ : {a : A} {l : List A} {c : Tree A} {r : List A} -> 
           ZipperRule (zipper l c (a :: r)) (zipper l (c ▪ (𝒾 a)) r)
  right⇒ : {a : A} {l : List A} {c : Tree A} {r : List A} -> 
           ZipperRule (zipper l (c ▪ (𝒾 a)) r) (zipper l c (a :: r))
  left-ε⇒ : {l : List A} {c : Tree A} {r : List A} -> 
            ZipperRule (zipper l c r) (zipper l (ε ▪ c) r)
  left-ε⇐ : {l : List A} {c : Tree A} {r : List A} -> 
            ZipperRule (zipper l (ε ▪ c) r) (zipper l c r) 
  right-ε⇒ : {l : List A} {c : Tree A} {r : List A} -> 
             ZipperRule (zipper l c r) (zipper l (c ▪ ε) r)
  right-ε⇐ : {l : List A} {c : Tree A} {r : List A} -> 
             ZipperRule (zipper l (c ▪ ε) r) (zipper l c r)
  z-cong : {l : List A} {c1 c2 : Tree A} {r : List A} ->
           c1 == c2 ->
           ZipperRule (zipper l c1 r) (zipper l c2 r)
  



-- record isTreeCongruence (R : Rel (Tree A) ℓ) : Type (ℓ-max (levelOf A) ℓ) where
--   field
--     on-left : {t1 t2 : Tree A} -> R t1 t2 -> (t3 : Tree A) -> R (t1 ▪ t3) (t2 ▪ t3)
--     on-right : (t1 : Tree A) -> {t2 t3 : Tree A} -> R t2 t3 ->  R (t1 ▪ t2) (t1 ▪ t3)
-- 
-- record isAssociative (R : Rel (Tree A) ℓ) : Type (ℓ-max (levelOf A) ℓ) where
--   field
--     assoc-right : {t1 t2 t3 : Tree A} -> R ((t1 ▪ t2) ▪ t3) (t1 ▪ (t2 ▪ t3))
--     assoc-left : {t1 t2 t3 : Tree A} -> R (t1 ▪ (t2 ▪ t3)) ((t1 ▪ t2) ▪ t3)



-- module _ {ℓ : Level} {A : Type ℓ} (R : Rel A ℓ) 
--          (isAssoc : isAssociative R)
--          (isCong : isTreeCong R)
--   where




