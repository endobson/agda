{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module functions.telescope where

open import base
open import hlevel
open import list
open import fin-algebra


-- data Telescope (ℓ : Level) : Nat -> Type (ℓ-suc ℓ) where
--   telescope-base : Type ℓ -> Telescope ℓ zero
--   telescope-cons : {n : Nat} {A : Type ℓ} ->
--     (A -> Telescope ℓ n) -> Telescope ℓ (suc n)
-- 
-- -- tele* : Nat
-- 
-- 
-- telescope-map : {ℓ : Level} {n : Nat} -> (Type ℓ -> Type ℓ) -> Telescope ℓ n -> Telescope ℓ n
-- telescope-map f (telescope-base X) = (telescope-base (f X))
-- telescope-map f (telescope-cons Xs) = (telescope-cons (\a -> (telescope-map f (Xs a))))
-- 


private
  variable
    ℓ ℓA : Level

-- module _ 
--   {A : Type ℓ} 
--   {B : A -> Type ℓ} 
--   {C : (a : A) -> B a -> Type ℓ} where
--   isSetΠ2' : ((x : A) -> (y : B x) -> isSet (C x y)) -> isSet ((x : A) -> (y : B x) -> (C x y))
--   isSetΠ2' = 
--     isSetΠTele (telescope-cons (\x -> (telescope-cons (\y -> (telescope-base _)))))

Levels : Type₀
Levels = List Level

Levels-max : Levels -> Level
Levels-max [] = ℓ-zero
Levels-max (ℓ :: ℓs) = ℓ-max ℓ (Levels-max ℓs)


data Telescope : (Levels × Level) -> Agda.Primitive.Setω where
  telescope-base : Type ℓ -> Telescope ([] , ℓ)
  telescope-cons : {A : Type ℓA} {ℓs : Levels} ->
     (A -> Telescope (ℓs , ℓ)) -> Telescope (ℓA :: ℓs , ℓ)

telescope-map : {ℓs : Levels} {ℓ ℓ' : Level} -> (Type ℓ -> Type ℓ') -> 
                Telescope (ℓs , ℓ) -> Telescope (ℓs , ℓ')
telescope-map f (telescope-base X) = (telescope-base (f X))
telescope-map f (telescope-cons Xs) = (telescope-cons (\a -> (telescope-map f (Xs a))))

Telescope->Π : {ℓs : Levels} {ℓ : Level} -> Telescope (ℓs , ℓ) -> Type (ℓ-max (Levels-max ℓs) ℓ)
Telescope->Π (telescope-base X) = X
Telescope->Π (telescope-cons ts) = ∀ a -> (Telescope->Π (ts a))

isSetΠTele : 
  {ℓs : Levels} {ℓ : Level} (t : Telescope (ℓs , ℓ)) ->
  (Telescope->Π (telescope-map isSet t)) -> isSet (Telescope->Π t)
isSetΠTele (telescope-base _) h = h
isSetΠTele (telescope-cons ts) h = isSetΠ (\a -> isSetΠTele (ts a) (h a))

module _ where
  private
    variable
      A : Type ℓ
      B : A -> Type ℓ
      C : (a : A) -> (B a) -> Type ℓ
      D : (a : A) -> (b : B a) -> (C a b) -> Type ℓ
      E : (a : A) -> (b : B a) -> (c : (C a b)) -> (D a b c) -> Type ℓ
      F : (a : A) -> (b : B a) -> (c : (C a b)) -> (d : (D a b c)) -> (E a b c d) -> Type ℓ

  isSetΠ2' : ((x : A) -> (y : B x) -> isSet (C x y)) -> 
             isSet ((x : A) -> (y : B x) -> (C x y))
  isSetΠ2' = 
    isSetΠTele (telescope-cons (\x -> (telescope-cons (\y -> (telescope-base _)))))
