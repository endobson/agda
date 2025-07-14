{-# OPTIONS --cubical --safe --exact-split #-}

module equality.dependent-path where

open import base
open import cubical
open import equality-path
open import equality.square


module _ {ℓA ℓB : Level} {A : Type ℓA} (B : A -> Type ℓB) where

  module _
    {a₁ a₂ a₃ a₄ : A}
    {b₁ : B a₁}
    {b₂ : B a₂}
    {b₃ : B a₃}
    {b₄ : B a₄}
    {ap₁ : a₁ == a₂} (bp₁ : PathP (\i -> B (ap₁ i)) b₁ b₂)
    {ap₂ : a₂ == a₃} (bp₂ : PathP (\i -> B (ap₂ i)) b₂ b₃)
    {ap₃ : a₃ == a₄} (bp₃ : PathP (\i -> B (ap₃ i)) b₃ b₄)
    where
    private
      ap : a₁ == a₄
      ap = ap₁ ∙∙ ap₂ ∙∙ ap₃
      asq : Square (sym ap₁) ap₃ ap₂ (ap₁ ∙∙ ap₂ ∙∙ ap₃)
      asq = ▪ᵀ (doubleCompPath-filler _ _ _)

    ∙∙dep : PathP (\i -> B (ap i)) b₁ b₄
    ∙∙dep i =
      comp (\k -> B (asq i k))
           (\k -> \{ (i = i0) -> bp₁ (~ k)
                   ; (i = i1) -> bp₃ k
                   })
        (bp₂ i)

    ∙∙dep-filler : SquareP (\i j -> B (asq i j)) (symP bp₁) bp₃ bp₂ ∙∙dep
    ∙∙dep-filler i j =
      fill (\k -> B (asq i k))
           (\k -> \{ (i = i0) -> bp₁ (~ k)
                   ; (i = i1) -> bp₃ k
                   })
        (inS (bp₂ i)) j

-- module _ {ℓ : Level} {A : Type ℓ} {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : A}
--   {p₀ : a₀ == b₀} {q₀ : b₀ == c₀} {r₀ : c₀ == d₀}
--   {p₁ : a₁ == b₁} {q₁ : b₁ == c₁} {r₁ : c₁ == d₁}
--   {a : a₀ == a₁} {b : b₀ == b₁} {c : c₀ == c₁} {d : d₀ == d₁}
--   (s₁ : Square a b p₀ p₁)
--   (s₂ : Square b c q₀ q₁)
--   (s₃ : Square c d r₀ r₁)
--   where
--
--   ▪h-filler : SquareP (\i j -> (doubleCompPath-filler p₀ q₀ r₀ j i) ==
--                                (doubleCompPath-filler p₁ q₁ r₁ j i))
--                (symP s₁) s₃ s₂ (s₁ ▪h s₂ ▪h s₃)
--   ▪h-filler k = ?

module _ {ℓ : Level} {A : Type ℓ} {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : A}
  {p₀ : a₀ == b₀} {q₀ : b₀ == c₀} {r₀ : c₀ == d₀}
  {p₁ : a₁ == b₁} {q₁ : b₁ == c₁} {r₁ : c₁ == d₁}
  {a : a₀ == a₁} {b : b₀ == b₁} {c : c₀ == c₁} {d : d₀ == d₁}
  (s₁ : Square p₀ p₁ a b)
  (s₂ : Square q₀ q₁ b c)
  (s₃ : Square r₀ r₁ c d)
  where

  -- ▪v-filler : SquareP (\i j -> (doubleCompPath-filler p₀ q₀ r₀ i j) ==
  --                              (doubleCompPath-filler p₁ q₁ r₁ i j))
  --              (▪ᵀ s₂) ((▪ᵀ s₂)  (symP (▪ᵀ s₁)) (▪ᵀ s₃)
  -- ▪v-filler k = ?



module _
  {ℓA : Level} {A : Type ℓA}
  {★A a₁ a₂ a₃ a₄ : A}
  {b₁ : ★A == a₁}
  {b₂ : ★A == a₂}
  {b₃ : ★A == a₃}
  {b₄ : ★A == a₄}
  {ap₁ : a₁ == a₂} (bp₁ : PathP (\i -> ★A == (ap₁ i)) b₁ b₂)
  {ap₂ : a₂ == a₃} (bp₂ : PathP (\i -> ★A == (ap₂ i)) b₂ b₃)
  {ap₃ : a₃ == a₄} (bp₃ : PathP (\i -> ★A == (ap₃ i)) b₃ b₄)
  where
  private
    dep-bp : Square b₁ b₄ refl (ap₁ ∙∙ ap₂ ∙∙ ap₃)
    dep-bp = ∙∙dep (\a -> ★A == a) bp₁ bp₂ bp₃

    dep-bp-filler :
       PathP (\k -> Square (\j -> bp₁ (~ k) j) (\j -> bp₃ k j)
                           (reflᵉ ★A) (doubleCompPath-filler ap₁ ap₂ ap₃ k))
             bp₂ dep-bp
    dep-bp-filler k i j = ∙∙dep-filler (\a -> ★A == a) bp₁ bp₂ bp₃ i k j



    dep-bp' : Square b₁ b₄ refl (ap₁ ∙∙ ap₂ ∙∙ ap₃)
    dep-bp' i j =
      hcomp (\k -> \{ (i = i0) -> bp₁ (~ k) j
                    ; (i = i1) -> bp₃ k j
                    ; (j = i0) -> ★A
                    ; (j = i1) -> doubleCompPath-filler ap₁ ap₂ ap₃ k i
                    })
        (bp₂ i j)

    dep-bp'-filler :
     PathP (\k -> Square (\j -> bp₁ (~ k) j) (\j -> bp₃ k j) refl
                         (\i -> doubleCompPath-filler ap₁ ap₂ ap₃ k i))
           bp₂ dep-bp'
    dep-bp'-filler k i j =
      hfill (\k -> \{ (i = i0) -> bp₁ (~ k) j
                    ; (i = i1) -> bp₃ k j
                    ; (j = i0) -> ★A
                    ; (j = i1) -> doubleCompPath-filler ap₁ ap₂ ap₃ k i
                    })
        (inS (bp₂ i j)) k

    dep-bp'-path : dep-bp == dep-bp'
    dep-bp'-path = transP-sym (symP dep-bp-filler) dep-bp'-filler

  ▪dep : Square b₁ b₄ refl (ap₁ ∙∙ ap₂ ∙∙ ap₃)
  ▪dep = dep-bp'

  ▪dep-path : ▪dep == ∙∙dep (\a -> ★A == a) bp₁ bp₂ bp₃
  ▪dep-path = sym dep-bp'-path


  transport-▪dep :
    {ℓf : Level} (f : (a : A) -> ★A == a -> Type ℓf)
    (magic : Magic)
    {x₀ : f a₁ b₁} ->
    transport (\i -> f ((ap₁ ∙∙ ap₂ ∙∙ ap₃) i) (▪dep i)) x₀ ==
    transport (\i -> f (ap₃ i) (bp₃ i))
      (transport (\i -> f (ap₂ i) (bp₂ i))
        (transport (\i -> f (ap₁ i) (bp₁ i)) x₀))
  transport-▪dep f magic = magic
















module _ {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : A -> Type ℓB} {C : Type ℓC}
         (f : (a : A) -> (b : B a) -> C)
  where

  module _
    {a₁ a₂ a₃ a₄ : A}
    {b₁ : B a₁}
    {b₂ : B a₂}
    {b₃ : B a₃}
    {b₄ : B a₄}
    (ap₁ : a₁ == a₂) (bp₁ : PathP (\i -> B (ap₁ i)) b₁ b₂)
    (ap₂ : a₂ == a₃) (bp₂ : PathP (\i -> B (ap₂ i)) b₂ b₃)
    (ap₃ : a₃ == a₄) (bp₃ : PathP (\i -> B (ap₃ i)) b₃ b₄)
    where
    private
      ap : a₁ == a₄
      ap = ap₁ ∙∙ ap₂ ∙∙ ap₃
      asq : Square (sym ap₁) ap₃ ap₂ (ap₁ ∙∙ ap₂ ∙∙ ap₃)
      asq = ▪ᵀ (doubleCompPath-filler _ _ _)

      bp : PathP (\i -> B (ap i)) b₁ b₄
      bp = ∙∙dep B bp₁ bp₂ bp₃


    cong2-dep-∙∙ : cong2-dep f ap bp ==
                   (cong2-dep f ap₁ bp₁) ∙∙
                   (cong2-dep f ap₂ bp₂) ∙∙
                   (cong2-dep f ap₃ bp₃)
    cong2-dep-∙∙ k i =
      hcomp (\j -> \{ (i = i0) -> f (ap₁ (~ j)) (bp₁ (~ j))
                    ; (i = i1) -> f (ap₃ j) (bp₃ j)
                    ; (k = i0) -> f (hfill (\j -> \{ (i = i0) -> ap₁ (~ j)
                                                   ; (i = i1) -> ap₃ j
                                                   })
                                           (inS (ap₂ i)) j)
                                    (fill (\j -> B (asq i j))
                                          (\j -> \{ (i = i0) -> bp₁ (~ j)
                                                  ; (i = i1) -> bp₃ j
                                                  })
                                          (inS (bp₂ i)) j)
                    ; (k = i1) -> (hfill
                                     (\j -> \{ (i = i0) -> f (ap₁ (~ j)) (bp₁ (~ j))
                                             ; (i = i1) -> f (ap₃ j) (bp₃ j)
                                             })
                                     (inS (f (ap₂ i) (bp₂ i))) j)
                    })
        (f (ap₂ i) (bp₂ i))
