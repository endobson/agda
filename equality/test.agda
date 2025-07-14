{-# OPTIONS --cubical --safe --exact-split #-}

module equality.test where

open import base
open import cubical
open import equality-path

module _ {ℓA1 ℓA2 : Level} {A1 : Type ℓA1} {A2 : Type ℓA2} (f : A1 -> A2) where
  cong-∙∙' : {w x y z : A1} (p₁ : w == x) (p₂ : x == y) (p₃ : y == z) ->
       cong f (p₁ ∙∙ p₂ ∙∙ p₃) == cong f p₁ ∙∙ cong f p₂ ∙∙ cong f p₃
  cong-∙∙' p₁ p₂ p₃ k i =
    hcomp (\j -> \{ (i = i0) -> f (p₁ (~ j))
                  ; (i = i1) -> f (p₃ j)
                  ; (k = i0) -> f (hfill (\j -> \{ (i = i0) -> p₁ (~ j)
                                                 ; (i = i1) -> p₃ j
                                                 })
                                         (inS (p₂ i)) j)
                  ; (k = i1) -> hfill (\j -> \{ (i = i0) -> f (p₁ (~ j))
                                              ; (i = i1) -> f (p₃ j)
                                              }) (inS (f (p₂ i))) j
                  })
      (f (p₂ i))


-- module _ {ℓA1 ℓA2 : Level} {A1 : Type ℓA1} {A2 : Type ℓA2} (f : A1 -> A2) where
--   cong-doubleCompPath-filler : {w x y z : A1} (p₁ : w == x) (p₂ : x == y) (p₃ : y == z) ->
--     PathP (\i -> Square (cong f p₂) (cong-∙∙' f p₁ p₂ p₃ i)
--                         (cong f (sym p₁)) (cong f p₃))
--           (\i j -> f (doubleCompPath-filler p₁ p₂ p₃ i j))
--           (doubleCompPath-filler (cong f p₁) (cong f p₂) (cong f p₃))
--   cong-doubleCompPath-filler p₁ p₂ p₃ k j i =
--     hfill (\j -> \{ (i = i0) -> f (p₁ (~ j))
--                   ; (i = i1) -> f (p₃ j)
--                   ; (k = i0) -> f (hfill (\j -> \{ (i = i0) -> p₁ (~ j)
--                                                  ; (i = i1) -> p₃ j
--                                                  })
--                                          (inS (p₂ i)) j)
--                   ; (k = i1) -> hfill (\j -> \{ (i = i0) -> f (p₁ (~ j))
--                                               ; (i = i1) -> f (p₃ j)
--                                               }) (inS (f (p₂ i))) j
--                   })
--       (inS (f (p₂ i))) j



  -- cong-∙∙'-filler : {w x y z : A1} (p₁ : w == x) (p₂ : x == y) (p₃ : y == z) ->
  --   ?
  -- cong-∙∙'-filler p₁ p₂ p₃ k i j =
  --   hcomp (\j -> \{ (i = i0) -> f (p₁ (~ j))
  --                 ; (i = i1) -> f (p₃ j)
  --                 ; (k = i0) -> f (hfill (\j -> \{ (i = i0) -> p₁ (~ j)
  --                                                ; (i = i1) -> p₃ j
  --                                                })
  --                                        (inS (p₂ i)) j)
  --                 ; (k = i1) -> hfill (\j -> \{ (i = i0) -> f (p₁ (~ j))
  --                                             ; (i = i1) -> f (p₃ j)
  --                                             }) (inS (f (p₂ i))) j
  --                 })
  --     (f (p₂ i)) j
