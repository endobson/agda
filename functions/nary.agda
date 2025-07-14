{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module functions.nary where

open import base
open import nat
open import fin-algebra




--  S₀ : Type (ℓ-suc ℓ)
--  S₀ = Type ℓ
--  S₁ : Type (ℓ-suc ℓ)
--  S₁ = A -> Type ℓ
--  S₂ : Type (ℓ-suc ℓ)
--  S₂ = (a : A) -> B a -> Type ℓ

-- (A :                                        Type ℓ)
-- (B : (a : A) ->                             Type ℓ)
-- (C : (a : A) -> (b : B a) ->                Type ℓ) 
-- (D : (a : A) -> (b : B a) -> (c : C a b) -> Type ℓ) 

-- T-args : FinT

module _ (ℓ : Level) where
  T₀ : Type (ℓ-suc ℓ)
  T₀ = Type ℓ

  T₁ : (A : T₀) -> Type (ℓ-suc ℓ)
  T₁ A = (a : A) -> Type ℓ

  T₂ : (A : T₀) -> (B : T₁ A) -> Type (ℓ-suc ℓ)
  T₂ A B = (a : A) -> (b : B a) -> Type ℓ

  T₃ : (A : T₀) -> (B : T₁ A) -> (C : T₂ A B) -> Type (ℓ-suc ℓ)
  T₃ A B C = (a : A) -> (b : B a) -> (c : C a b) -> Type ℓ

  S₀ : Top -> Type (ℓ-suc ℓ)
  S₀ _ = Type ℓ

  S₁ : Σ Top S₀ -> Type (ℓ-suc ℓ)
  S₁ (tt , A) = (a : A) -> Type ℓ

  S₂ : Σ (Σ Top S₀) S₁ -> Type (ℓ-suc ℓ)
  S₂ ((tt , A) , B) = (a : A) -> (b : B a) -> Type ℓ

  S₃ : Σ (Σ (Σ Top S₀) S₁) S₂ -> Type (ℓ-suc ℓ)
  S₃ (((tt , A) , B) , C) = (a : A) -> (b : B a) -> (c : C a b) -> Type ℓ

  Q₀ : (Σ Top S₀) -> Type ℓ
  Q₀ (tt , A) = A

  Q₁ : (Σ (Σ Top S₀) S₁) -> Type ℓ
  Q₁ (l@(tt , A) , B) = (Σ (Q₀ l) B) 

  Q₂ : Σ (Σ (Σ Top S₀) S₁) S₂ -> Type ℓ
  Q₂ (l@((tt , A) , B) , C) = Σ (Q₁ l) (\(a , b) -> C a b)

  Q₃ : Σ (Σ (Σ (Σ Top S₀) S₁) S₂) S₃ -> Type ℓ
  Q₃ (l@(((tt , A) , B) , C) , D) = Σ (Q₂ l) (\((a , b) , c) -> D a b c)

  app-SQ₀ : (r : Σ Top S₀) -> S₁ r -> Q₀ r -> Type ℓ
  app-SQ₀ _ B a = B a
  app-SQ₁ : (r : Σ (Σ Top S₀) S₁) -> S₂ r -> Q₁ r -> Type ℓ
  app-SQ₁ _ C (a , b) = C a b
  app-SQ₂ : (r : Σ (Σ (Σ Top S₀) S₁) S₂) -> S₃ r -> Q₂ r -> Type ℓ
  app-SQ₂ _ D ((a , b) , c) = D a b c


  -- Rₙ : Nat -> Type (ℓ-suc ℓ)
  -- Sₙ : (n : Nat) -> (Rₙ n) -> Type (ℓ-suc ℓ)

  -- Rₙ zero = Lift (ℓ-suc ℓ) Top
  -- Rₙ (suc n) = Σ (Rₙ n) (Sₙ n)
  -- Sₙ n r = ?




  

-- Args : (n : ℕ) (ℓ : Level) -> FinT n -> Type (ℓ-suc ℓ)
-- Args zero ℓ = Type ℓ



-- Arg : (n : ℕ) (ℓ : Level) (i : FinT n) -> Type (ℓ-suc ℓ)
-- Arg zero    ℓ ()
-- Arg (suc n) ℓ ()

-- Args : (n : ℕ) (ℓ : Level) -> Type (ℓ-suc ℓ)
-- Args n ℓ = (i : FinT n) -> Arg n i
-- 
-- 
-- Telescope : (n : ℕ) (ℓ : Level) -> Top -- (Args n ℓ) 
--             -> Type (ℓ-suc ℓ)
-- Telescope 0 ℓ _ = Type ℓ
-- Telescope 1 ℓ _ = Type ℓ


-- module _ (ℓ : Level) 
--   (A : Type ℓ)
--   (B : A -> Type ℓ)
--   (C : (a : A) -> B a -> Type ℓ) 
--   where
-- 
-- 
--   T₀ : S₀
--   T₀ = A
--   T₁ : S₁
--   T₁ = B
--   T₂ : S₂
--   T₂ = C
  

