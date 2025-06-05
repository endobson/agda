{-# OPTIONS --cubical --safe --exact-split #-}

module equality.square2 where


open import base
open import cubical
open import equality-path
open import equality.square


module _ {ℓ : Level} {A : I -> I -> Type ℓ}
         {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
         {a₀₋ : PathP (\i -> A i0 i) a₀₀ a₀₁}
         {a₁₋ : PathP (\i -> A i1 i) a₁₀ a₁₁}
         {a₋₀ : PathP (\i -> A i i0) a₀₀ a₁₀}
         {a₋₁ : PathP (\i -> A i i1) a₀₁ a₁₁}
  where
  ▪ᵀ : SquareP A a₀₋ a₁₋ a₋₀ a₋₁ -> SquareP (\i j -> A j i) a₋₀ a₋₁ a₀₋ a₁₋
  ▪ᵀ s i j = s j i

module _ {ℓ : Level} {A : Type ℓ} {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : A}
  {p₀ : a₀ == b₀} {q₀ : b₀ == c₀} {r₀ : c₀ == d₀}
  {p₁ : a₁ == b₁} {q₁ : b₁ == c₁} {r₁ : c₁ == d₁}
  {a : a₀ == a₁} {b : b₀ == b₁} {c : c₀ == c₁} {d : d₀ == d₁}
  (s₁ : Square p₀ p₁ a b)
  (s₂ : Square q₀ q₁ b c)
  (s₃ : Square r₀ r₁ c d)
  where

  _▪v_▪v_ : Square (p₀ ∙∙ q₀ ∙∙ r₀) (p₁ ∙∙ q₁ ∙∙ r₁) a d
  _▪v_▪v_ i = (s₁ i) ∙∙ (s₂ i) ∙∙ (s₃ i)


module _ {ℓ : Level} {A : Type ℓ} {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : A}
  {p₀ : a₀ == b₀} {q₀ : b₀ == c₀} {r₀ : c₀ == d₀}
  {p₁ : a₁ == b₁} {q₁ : b₁ == c₁} {r₁ : c₁ == d₁}
  {a : a₀ == a₁} {b : b₀ == b₁} {c : c₀ == c₁} {d : d₀ == d₁}
  (s₁ : Square a b p₀ p₁)
  (s₂ : Square b c q₀ q₁)
  (s₃ : Square c d r₀ r₁)
  where

  _▪h_▪h_ : Square a d (p₀ ∙∙ q₀ ∙∙ r₀) (p₁ ∙∙ q₁ ∙∙ r₁)
  _▪h_▪h_ = ▪ᵀ ((▪ᵀ s₁) ▪v (▪ᵀ s₂) ▪v (▪ᵀ s₃))


module _ {ℓ : Level} {A : Type ℓ} {a b c d : A}
  (p1 : a == b) (p2 : c == d) (p3 : a == c) (p4 : b == d)
  where
  opaque
    compPaths->Square :
       (p1 >=> p4) == (p3 >=> p2) ->
       Square p1 p2 p3 p4
    compPaths->Square q = ▪ᵀ cs2'
      where
      s₁ : Square p1 (p1 >=> p4) refl p4
      s₁ i j =
        hcomp (\k -> \{ (i = i0) -> p1 (j ∨ (~ k))
                      ; (i = i1) -> square-filler (sym p1) p4 refl j k
                      ; (j = i0) -> p1 (~ k)
                      ; (j = i1) -> p4 (i ∧ k)
                      })
          b
      s₂ : Square (p1 >=> p4) (p3 >=> p2) refl refl
      s₂ = q

      s₃ : Square (p3 >=> p2) p2 p3 refl
      s₃ i j =
        hcomp (\k -> \{ (i = i0) -> square-filler (sym p3) p2 refl j k -- p1 (j ∨ (~ k))
                      ; (i = i1) -> p2 (j ∧ k)
                      ; (j = i0) -> p3 (i ∨ ~ k)
                      ; (j = i1) -> p2 k
                      })
          c

      cs : Square p1 p2 (refl >=> p3) (p4 >=> refl)
      cs = s₁ ▪h s₂ ▪h s₃

      cs' : Square (refl >=> p3) (p4 >=> refl) p1 p2
      cs' i j = cs j i


      cs2' : Square p3 p4 p1 p2
      cs2' = transP-mid (sym (compPath-refl-left p3)) cs' (compPath-refl-right p4)
