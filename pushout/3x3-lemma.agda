{-# OPTIONS --cubical --safe --exact-split #-}

module pushout.3x3-lemma where

open import base
open import cubical hiding (glue)
open import equality-path
open import pushout

import isomorphism

module _
  {ℓ₀₀ ℓ₀₂ ℓ₀₄ ℓ₂₀ ℓ₂₂ ℓ₂₄ ℓ₄₀ ℓ₄₂ ℓ₄₄ : Level}
  {A₀₀ : Type ℓ₀₀} {A₀₂ : Type ℓ₀₂} {A₀₄ : Type ℓ₀₄}
  {A₂₀ : Type ℓ₂₀} {A₂₂ : Type ℓ₂₂} {A₂₄ : Type ℓ₂₄}
  {A₄₀ : Type ℓ₄₀} {A₄₂ : Type ℓ₄₂} {A₄₄ : Type ℓ₄₄}
  (f₀₁ : A₀₂ -> A₀₀) (f₀₃ : A₀₂ -> A₀₄)
  (f₂₁ : A₂₂ -> A₂₀) (f₂₃ : A₂₂ -> A₂₄)
  (f₄₁ : A₄₂ -> A₄₀) (f₄₃ : A₄₂ -> A₄₄)
  (f₁₀ : A₂₀ -> A₀₀) (f₃₀ : A₂₀ -> A₄₀)
  (f₁₂ : A₂₂ -> A₀₂) (f₃₂ : A₂₂ -> A₄₂)
  (f₁₄ : A₂₄ -> A₀₄) (f₃₄ : A₂₄ -> A₄₄)
  (h₁₁ : ∀ x -> f₀₁ (f₁₂ x) == f₁₀ (f₂₁ x))
  (h₁₃ : ∀ x -> f₀₃ (f₁₂ x) == f₁₄ (f₂₃ x))
  (h₃₁ : ∀ x -> f₄₁ (f₃₂ x) == f₃₀ (f₂₁ x))
  (h₃₃ : ∀ x -> f₄₃ (f₃₂ x) == f₃₄ (f₂₃ x))

  -- A₀₀ <-f₀₁- A₀₂ -f₀₃-> A₀₄
  --  ∧          ∧          ∧
  -- f₁₀   h₁₁  f₁₂  h₁₃   f₁₄
  --  |          |          |
  -- A₂₀ <-f₂₁- A₂₂ -f₂₃-> A₂₄
  --  |          |          |
  -- f₃₀   h₃₁  f₃₂  h₃₃   f₃₄
  --  ∨          ∨          ∨
  -- A₀₀ <-f₄₁- A₄₂ -f₄₃-> A₄₄

  where
  module 3x3 where

    -- Pushout along the row functions
    R₀ : Type _
    R₀ = Pushout f₀₁ f₀₃
    R₂ : Type _
    R₂ = Pushout f₂₁ f₂₃
    R₄ : Type _
    R₄ = Pushout f₄₁ f₄₃

    private
      module _ (v : A₂₂) where
        r₁₁-post : Path R₀ (inj-l (f₀₁ (f₁₂ v))) (inj-l (f₁₀ (f₂₁ v)))
        r₁₁-post i = inj-l (h₁₁ v i)
        r₁₃-post : Path R₀ (inj-r (f₀₃ (f₁₂ v))) (inj-r (f₁₄ (f₂₃ v)))
        r₁₃-post i = inj-r (h₁₃ v i)
        r₃₁-post : Path R₄ (inj-l (f₄₁ (f₃₂ v))) (inj-l (f₃₀ (f₂₁ v)))
        r₃₁-post i = inj-l (h₃₁ v i)
        r₃₃-post : Path R₄ (inj-r (f₄₃ (f₃₂ v))) (inj-r (f₃₄ (f₂₃ v)))
        r₃₃-post i = inj-r (h₃₃ v i)

        r₁-square :
          PathP (\i -> Path R₀ (r₁₁-post i) (r₁₃-post i)) (glue (f₁₂ v)) _
        r₁-square = doubleCompPath-filler (sym r₁₁-post) (glue (f₁₂ v)) r₁₃-post
        r₃-square :
          PathP (\i -> Path R₄ (r₃₁-post i) (r₃₃-post i)) (glue (f₃₂ v)) _
        r₃-square = doubleCompPath-filler (sym r₃₁-post) (glue (f₃₂ v)) r₃₃-post

    r₁ : R₂ -> R₀
    r₁ = Pushout-rec (\v -> inj-l (f₁₀ v)) (\v -> inj-r (f₁₄ v))
                     (\v i -> r₁-square v i1 i)
    r₃ : R₂ -> R₄
    r₃ = Pushout-rec (\v -> inj-l (f₃₀ v)) (\v -> inj-r (f₃₄ v))
                     (\v i -> r₃-square v i1 i)

    R : Type _
    R = Pushout r₁ r₃

    -- Pushout along the column functions
    C₀ : Type _
    C₀ = Pushout f₁₀ f₃₀
    C₂ : Type _
    C₂ = Pushout f₁₂ f₃₂
    C₄ : Type _
    C₄ = Pushout f₁₄ f₃₄

    private
      module _ (v : A₂₂) where
        c₁₁-post : Path C₀ (inj-l (f₀₁ (f₁₂ v))) (inj-l (f₁₀ (f₂₁ v)))
        c₁₁-post i = inj-l (h₁₁ v i)
        c₁₃-post : Path C₄ (inj-l (f₀₃ (f₁₂ v))) (inj-l (f₁₄ (f₂₃ v)))
        c₁₃-post i = inj-l (h₁₃ v i)
        c₃₁-post : Path C₀ (inj-r (f₄₁ (f₃₂ v))) (inj-r (f₃₀ (f₂₁ v)))
        c₃₁-post i = inj-r (h₃₁ v i)
        c₃₃-post : Path C₄ (inj-r (f₄₃ (f₃₂ v))) (inj-r (f₃₄ (f₂₃ v)))
        c₃₃-post i = inj-r (h₃₃ v i)

        c₁-square :
          PathP (\i -> Path C₀ (c₁₁-post (~ i)) (c₃₁-post (~ i))) (glue (f₂₁ v)) _
        c₁-square = doubleCompPath-filler c₁₁-post (glue (f₂₁ v)) (sym c₃₁-post)
        c₃-square :
          PathP (\i -> Path C₄ (c₁₃-post (~ i)) (c₃₃-post (~ i))) (glue (f₂₃ v)) _
        c₃-square = doubleCompPath-filler c₁₃-post (glue (f₂₃ v)) (sym c₃₃-post)


    c₁ : C₂ -> C₀
    c₁ = Pushout-rec (\v -> inj-l (f₀₁ v)) (\v -> inj-r (f₄₁ v))
                     (\v i -> c₁-square v i1 i)

    c₃ : C₂ -> C₄
    c₃ = Pushout-rec (\v -> inj-l (f₀₃ v)) (\v -> inj-r (f₄₃ v))
                     (\v i -> c₃-square v i1 i)

    C : Type _
    C = Pushout c₁ c₃

    private
      fwd-l : R₀ -> C
      fwd-l (inj-l v) = inj-l (inj-l v)
      fwd-l (inj-r v) = inj-r (inj-l v)
      fwd-l (glue v i) = glue (inj-l v) i

      fwd-r : R₄ -> C
      fwd-r (inj-l v) = inj-l (inj-r v)
      fwd-r (inj-r v) = inj-r (inj-r v)
      fwd-r (glue v i) = glue (inj-r v) i

      fwd-filler : (v : A₂₂) (i j : I) (t : I) -> C
      fwd-filler v i j =
        hfill
          (\k -> (\{ (i = i0) -> inj-l (c₁-square v (~ k) j)
                   ; (i = i1) -> inj-r (c₃-square v (~ k) j)
                   ; (j = i0) -> fwd-l (r₁-square v k i)
                   ; (j = i1) -> fwd-r (r₃-square v k i)
                   }))
          (inS (glue (glue v j) i))

      fwd : R -> C
      fwd (inj-l v) = fwd-l v
      fwd (inj-r v) = fwd-r v
      fwd (glue (inj-l v) i) = inj-l (glue v i)
      fwd (glue (inj-r v) i) = inj-r (glue v i)
      fwd (glue (glue v i) j) = fwd-filler v i j i1

      fwd-glue-path : ∀ v i j -> fwd (glue (glue v i) j) == glue (glue v j) i
      fwd-glue-path v i j t = fwd-filler v i j (~ t)

      bkw-l : C₀ -> R
      bkw-l (inj-l v) = inj-l (inj-l v)
      bkw-l (inj-r v) = inj-r (inj-l v)
      bkw-l (glue v i) = glue (inj-l v) i

      bkw-r : C₄ -> R
      bkw-r (inj-l v) = inj-l (inj-r v)
      bkw-r (inj-r v) = inj-r (inj-r v)
      bkw-r (glue v i) = glue (inj-r v) i

      bkw-filler : (v : A₂₂) (i j : I) (t : I) -> R
      bkw-filler v i j =
        hfill
          (\k ->
            (\{ (i = i0) -> inj-l (r₁-square v (~ k) j)
              ; (i = i1) -> inj-r (r₃-square v (~ k) j)
              ; (j = i0) -> bkw-l (c₁-square v k i)
              ; (j = i1) -> bkw-r (c₃-square v k i)
              }))
          (inS (glue (glue v j) i))

      bkw : C -> R
      bkw (inj-l v) = bkw-l v
      bkw (inj-r v) = bkw-r v
      bkw (glue (inj-l v) i) = inj-l (glue v i)
      bkw (glue (inj-r v) i) = inj-r (glue v i)
      bkw (glue (glue v i) j) = bkw-filler v i j i1

      fb-l : ∀ v -> fwd (bkw-l v) == inj-l v
      fb-l (inj-l _) = refl
      fb-l (inj-r _) = refl
      fb-l (glue _ _) = refl

      fb-r : ∀ v -> fwd (bkw-r v) == inj-r v
      fb-r (inj-l _) = refl
      fb-r (inj-r _) = refl
      fb-r (glue _ _) = refl

      fb : ∀ x -> fwd (bkw x) == x
      fb (inj-l v) = fb-l v
      fb (inj-r v) = fb-r v
      fb (glue (inj-l v) i) = refl
      fb (glue (inj-r v) i) = refl
      fb x@(glue (glue v i) j) k =
        hcomp (\t ->
          (\{ (i = i0) -> fwd-l (r₁-square v (~ t) j)
            ; (i = i1) -> fwd-r (r₃-square v (~ t) j)
            ; (j = i0) -> fb-l (c₁-square v t i) k
            ; (j = i1) -> fb-r (c₃-square v t i) k
            ; (k = i0) -> fwd (bkw-filler v i j t)
            ; (k = i1) -> fwd-filler v j i (~ t)
            }))
          (fwd-filler v j i i1)

      bf-l : ∀ v -> bkw (fwd-l v) == inj-l v
      bf-l (inj-l _) = refl
      bf-l (inj-r _) = refl
      bf-l (glue _ _) = refl

      bf-r : ∀ v -> bkw (fwd-r v) == inj-r v
      bf-r (inj-l _) = refl
      bf-r (inj-r _) = refl
      bf-r (glue _ _) = refl

      bf : ∀ x -> bkw (fwd x) == x
      bf (inj-l v) = bf-l v
      bf (inj-r v) = bf-r v
      bf (glue (inj-l v) i) = refl
      bf (glue (inj-r v) i) = refl
      bf x@(glue (glue v i) j) k =
        hcomp (\t ->
          (\{ (i = i0) -> bkw-l (c₁-square v (~ t) j)
            ; (i = i1) -> bkw-r (c₃-square v (~ t) j)
            ; (j = i0) -> bf-l (r₁-square v t i) k
            ; (j = i1) -> bf-r (r₃-square v t i) k
            ; (k = i0) -> bkw (fwd-filler v i j t)
            ; (k = i1) -> bkw-filler v j i (~ t)
            }))
          (bkw-filler v j i i1)

    iso : isomorphism.Iso R C
    iso = isomorphism.iso fwd bkw fb bf
