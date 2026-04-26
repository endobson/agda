{-# OPTIONS --cubical --safe --exact-split #-}

module equality.square where

open import base
open import cubical
open import equality-path

private
  variable
    ℓ : Level
    A : Type ℓ

rotate-square-ABCD->CDAB :
  {a₀₀ : A} {a₀₁ : A} {a₀₋ : Path A a₀₀ a₀₁}
  {a₁₀ : A} {a₁₁ : A} {a₁₋ : Path A a₁₀ a₁₁}
  {a₋₀ : Path A a₀₀ a₁₀} {a₋₁ : Path A a₀₁ a₁₁} ->
  Square a₀₋ a₁₋ a₋₀ a₋₁ -> Square a₋₀ a₋₁ a₀₋ a₁₋
rotate-square-ABCD->CDAB s i j = s j i


module _ {ℓ : Level} {A : Type ℓ}
         {a₀₀ : A} {a₁₁ : A} {a₋ : a₀₀ == a₁₁}
         {a₁₀ : A} {a₁₋ : a₁₀ == a₁₁} {a₋₀ : a₀₀ == a₁₀}
         (s : Square a₋ a₁₋ a₋₀ refl) where
  rotate-square-ABCR->RBCA : Square refl a₁₋ a₋₀ a₋
  rotate-square-ABCR->RBCA i j =
    hcomp (\k -> \{ (i = i0) -> a₋ (j ∧ (~ k))
                  ; (i = i1) -> a₁₋ j
                  ; (j = i0) -> a₋₀ i
                  ; (j = i1) -> a₋ (i ∨ (~ k))
                  })
          (s i j)

  rotate-square-ABCR->CARB : Square a₋₀ a₋ refl a₁₋
  rotate-square-ABCR->CARB =
    rotate-square-ABCD->CDAB rotate-square-ABCR->RBCA


module _ {ℓ : Level} {A :  Type ℓ}
         {a₀ a₁ a₂ : A}
         {a₀₋ : Path A a₀ a₁}
         {a₋₀ : Path A a₀ a₂}
         {a₋₁ : Path A a₁ a₂}
         (s : Square a₀₋ refl a₋₀ a₋₁) where

  rotate-square-ARBC->ABRC : Square a₀₋ a₋₀ refl a₋₁
  rotate-square-ARBC->ABRC i j =
    hcomp (\k -> \{ (i = i0) -> a₀₋ j
                  ; (i = i1) -> a₋₀ (j ∨ ~ k)
                  ; (j = i0) -> a₋₀ (i ∧ ~ k)
                  ; (j = i1) -> a₋₁ i
                  })
          (s i j)

module _
  {a₀₀ a₀₁ a₁₀ a₁₁ a₂₀ a₂₁ : A}
  {p₀₋ : Path A a₀₀ a₀₁} {p₁₋ : Path A a₁₀ a₁₁}
  {p₋₀ : Path A a₀₀ a₁₀} {p₋₁ : Path A a₀₁ a₁₁}
  {q₂₋ : Path A a₂₀ a₂₁}
  {q₋₀ : Path A a₁₀ a₂₀} {q₋₁ : Path A a₁₁ a₂₁}
  where
  square-side-append : Square p₀₋ p₁₋ p₋₀ p₋₁ -> Square p₁₋ q₂₋ q₋₀ q₋₁ ->
                       Square p₀₋ q₂₋ (p₋₀ >=> q₋₀) (p₋₁ >=> q₋₁)
  square-side-append s1 s2 i j =
    hcomp (\k -> \{ (i = i0) -> s1 (~ k) j
                  ; (i = i1) -> s2 k j
                  })
          (p₁₋ j)

module _
  {a₀₀ a₀₁ a₁₀ c a₁₁ : A}
  {p₀₋ : Path A a₀₀ a₀₁} {p₁₋ : Path A a₁₀ c}
  {p₋₀ : Path A a₀₀ a₁₀} {p₋₁ : Path A a₀₁ c}
  {q₂₋ : Path A a₁₀ a₁₁} {q₋₂ : Path A a₀₁ a₁₁}
  where
  square-corner-append :
    Square p₀₋ p₁₋ p₋₀ p₋₁ -> Square (sym p₋₁) q₂₋ (sym p₁₋) q₋₂ ->
    Square p₀₋ q₂₋ p₋₀ q₋₂
  square-corner-append s1 s2 i j =
    hcomp (\k -> \{ (i = i0) -> s1 (~ k) (~ k ∨ j)
                  ; (i = i1) -> s2 k (k ∧ j)
                  ; (j = i0) -> s1 (~ k ∨ i) (~ k)
                  ; (j = i1) -> s2 (k ∧ i) k
                  })
      c

-- Shows that going one way around the square is the same as going the other way
module _ {ℓ : Level} {A :  Type ℓ}
         {a₀₀ : A} {a₀₁ : A} {a₁₀ : A} {a₁₁ : A}
         {a₀₋ : Path A a₀₀ a₀₁}
         {a₁₋ : Path A a₁₀ a₁₁}
         {a₋₀ : Path A a₀₀ a₁₀}
         {a₋₁ : Path A a₀₁ a₁₁}
         (s : Square a₀₋ a₁₋ a₋₀ a₋₁) where
  square-commutes : (a₀₋ >=> a₋₁) == (a₋₀ >=> a₁₋)
  square-commutes i j =
    hcomp (\k -> \{ (i = i0) -> (a₀₋ >=> (\l -> a₋₁ (l ∧ k))) j
                  ; (i = i1) -> ((\l -> a₋₀ (l ∨ ~ k)) >=> a₁₋) j
                  ; (j = i0) -> a₋₀ (i ∧ ~ k)
                  ; (j = i1) -> a₋₁ (i ∨ k)
                  })
          (s' i j)
   where
   s' : Square (a₀₋ >=> refl) (refl >=> a₁₋) a₋₀ a₋₁
   s' i j =
    hcomp (\k -> \{ (i = i0) -> compPath-refl-right a₀₋ (~ k) j
                  ; (i = i1) -> compPath-refl-left a₁₋ (~ k) j
                  ; (j = i0) -> a₋₀ i
                  ; (j = i1) -> a₋₁ i
                  })
          (s i j)


square-filler :
  {ℓ : Level} {A : Type ℓ} {w x y z : A}
  (p : x == w) (q : y == z) (r : x == y)
  -> Square p q r ((sym p) ∙∙ r ∙∙ q)
square-filler p q r = rotate-square-ABCD->CDAB (doubleCompPath-filler (sym p) r q)

-- Extract out the final side of a square.
-- Useful if the square was constructed using the filler.
square-final-side :
  {ℓ : Level} {A : Type ℓ} {w x y z : A}
  {p : x == w} {q : y == z} {r : x == y} {s : w == z}
  -> Square p q r s -> w == z
square-final-side {s = s} _ = s
