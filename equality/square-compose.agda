{-# OPTIONS --cubical --safe --exact-split #-}

module equality.square-compose where


open import base
open import pointed.base
open import cubical
open import equality-path
open import equality.square
open import base
open import funext
open import isomorphism
open import sigma

open import additive-group
open import additive-group.instances.nat
open import cubical
open import equality-path
open import equality.square
open import equality.path-composition-equivalence
open import connected
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import truncation.generic
open import truncation.generic.map
open import equivalence.base
open import equivalence
-- open import univalence
open import connected.wedge


module _ {ℓ : Level} {A : Type ℓ} where
  ▪comp :
    {a₀₀ a₀₁ a₁₀ a₁₁ b₀₀ b₀₁ b₁₀ b₁₁ : A}
    {a₋₀ : a₀₀ == a₁₀}
    {a₋₁ : a₀₁ == a₁₁}
    {a₀₋ : a₀₀ == a₀₁}
    {a₁₋ : a₁₀ == a₁₁}
    {b₋₀ : b₀₀ == b₁₀}
    {b₋₁ : b₀₁ == b₁₁}
    {b₀₋ : b₀₀ == b₀₁}
    {b₁₋ : b₁₀ == b₁₁}
    {ab₀₀ : a₀₀ == b₀₀}
    {ab₀₁ : a₀₁ == b₀₁}
    {ab₁₀ : a₁₀ == b₁₀}
    {ab₁₁ : a₁₁ == b₁₁}
    (base : Square a₀₋ a₁₋ a₋₀ a₋₁) ->
    (west : Square b₀₋ a₀₋ (sym ab₀₀) (sym ab₀₁)) ->
    (east : Square a₁₋ b₁₋ ab₁₀ ab₁₁) ->
    (south : Square (sym ab₀₀) (sym ab₁₀) b₋₀ a₋₀) ->
    (north : Square ab₀₁ ab₁₁ a₋₁ b₋₁) ->
    Square b₀₋ b₁₋ b₋₀ b₋₁
  ▪comp base west east south north x y =
    hcomp (\z -> \{ (x = i0) -> west (~ z) y
                  ; (x = i1) -> east z y
                  ; (y = i0) -> south x (~ z)
                  ; (y = i1) -> north x z
                  })
          (base x y)


  ▪comp-filler :
    {a₀₀ a₀₁ a₁₀ a₁₁ b₀₀ b₀₁ b₁₀ b₁₁ : A}
    {a₋₀ : a₀₀ == a₁₀}
    {a₋₁ : a₀₁ == a₁₁}
    {a₀₋ : a₀₀ == a₀₁}
    {a₁₋ : a₁₀ == a₁₁}
    {b₋₀ : b₀₀ == b₁₀}
    {b₋₁ : b₀₁ == b₁₁}
    {b₀₋ : b₀₀ == b₀₁}
    {b₁₋ : b₁₀ == b₁₁}
    {ab₀₀ : a₀₀ == b₀₀}
    {ab₀₁ : a₀₁ == b₀₁}
    {ab₁₀ : a₁₀ == b₁₀}
    {ab₁₁ : a₁₁ == b₁₁}
    (base : Square a₀₋ a₁₋ a₋₀ a₋₁) ->
    (west : Square b₀₋ a₀₋ (sym ab₀₀) (sym ab₀₁)) ->
    (east : Square a₁₋ b₁₋ ab₁₀ ab₁₁) ->
    (south : Square (sym ab₀₀) (sym ab₁₀) b₋₀ a₋₀) ->
    (north : Square ab₀₁ ab₁₁ a₋₁ b₋₁) ->
    PathP (\z -> Square (\y -> west (~ z) y)
                        (\y -> east z y)
                        (\x -> south x (~ z))
                        (\x -> north x z))
      base
      (▪comp base west east south north) -- b₀₋ b₁₋ b₋₀ b₋₁
  ▪comp-filler base west east south north z x y =
    (hfill (\z -> \{ (x = i0) -> west (~ z) y
                   ; (x = i1) -> east z y
                   ; (y = i0) -> south x (~ z)
                   ; (y = i1) -> north x z
                   })
           (inS (base x y)) z)



  module _
    {a₀₀ a₀₁ a₁₀ a₁₁ : A}
    {a₋₀ : a₀₀ == a₁₀}
    {a₋₁ : a₀₁ == a₁₁}
    {a₀₋ : a₀₀ == a₀₁}
    {a₁₋ : a₁₀ == a₁₁}
    (base : Square a₀₋ a₁₋ a₋₀ a₋₁)
    where

    ▪comp-refl : ▪comp base refl refl (\_ -> refl) (\_ -> refl) == base
    ▪comp-refl z x y =
      hfill (\z -> \{ (x = i0) -> base x y
                    ; (x = i1) -> base x y
                    ; (y = i0) -> base x y
                    ; (y = i1) -> base x y
                    })
            (inS (base x y)) (~ z)


  module _
    {a₀₀ a₀₁ a₁₀ a₁₁ b₀₀ b₀₁ b₁₀ b₁₁ : A}
    {a₋₀ : a₀₀ == a₁₀}
    {a₋₁ : a₀₁ == a₁₁}
    {a₀₋ : a₀₀ == a₀₁}
    {a₁₋ : a₁₀ == a₁₁}
    {b₋₀ : b₀₀ == b₁₀}
    {b₋₁ : b₀₁ == b₁₁}
    {b₀₋ : b₀₀ == b₀₁}
    {b₁₋ : b₁₀ == b₁₁}
    {ab₀₀ : a₀₀ == b₀₀}
    {ab₀₁ : a₀₁ == b₀₁}
    {ab₁₀ : a₁₀ == b₁₀}
    {ab₁₁ : a₁₁ == b₁₁}
    (west : Square b₀₋ a₀₋ (sym ab₀₀) (sym ab₀₁))
    (east : Square a₁₋ b₁₋ ab₁₀ ab₁₁)
    (south : Square (sym ab₀₀) (sym ab₁₀) b₋₀ a₋₀)
    (north : Square ab₀₁ ab₁₁ a₋₁ b₋₁)
    where

    isEquiv-▪comp : isEquiv (\base -> ▪comp base west east south north)
    isEquiv-▪comp = isoToIsEquiv (iso for back fb bf)
      where
      for : Square a₀₋ a₁₋ a₋₀ a₋₁ -> Square b₀₋ b₁₋ b₋₀ b₋₁
      for base = ▪comp base west east south north
      back : Square b₀₋ b₁₋ b₋₀ b₋₁ -> Square a₀₋ a₁₋ a₋₀ a₋₁
      back top = ▪comp top (symP west) (symP east) (\i j -> south i (~ j)) (\i j -> north i (~ j))


      bf : ∀ base -> back (for base) == base
      bf base = reduce ∙∙ (▪comp-refl _) ∙∙ (▪comp-refl base)
        where
        reduce : back (for base) == (▪comp (▪comp base refl refl _ _) refl refl _ _)
        reduce k = part2
         where
         part1 : _
         part1 = ▪comp base (\i j -> west (i ∨ k) j)
                            (\i j -> east (i ∧ ~ k) j)
                            (\i j -> south i (j ∨ k))
                            (\i j -> north i (j ∧ ~ k))

         part2 : _
         part2 = ▪comp part1 (\i j -> west (~ i ∨ k) j)
                             (\i j -> east (~ i ∧ ~ k) j)
                             (\i j -> south i (~ j ∨ k))
                             (\i j -> north i (~ j ∧ ~ k))


      fb : ∀ top -> for (back top) == top
      fb top = reduce ∙∙ (▪comp-refl _) ∙∙ (▪comp-refl top)
        where
        reduce : for (back top) == (▪comp (▪comp top refl refl _ _) refl refl _ _)
        reduce k = part2
         where
         part1 : _
         part1 = ▪comp top (\i j -> west (~ i ∧ ~ k) j)
                           (\i j -> east (~ i ∨ k) j)
                           (\i j -> south i (~ j ∧ ~ k))
                           (\i j -> north i (~ j ∨ k))
         part2 : _
         part2 = ▪comp part1 (\i j -> west (i ∧ ~ k) j)
                             (\i j -> east (i ∨ k) j)
                             (\i j -> south i (j ∧ ~ k))
                             (\i j -> north i (j ∨ k))


module _ {ℓ : Level} {A : Type ℓ} {a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ : A}
  {p₀ : a₀ == b₀} {q₀ : b₀ == c₀} {r₀ : c₀ == d₀}
  {p₁ : a₁ == b₁} {q₁ : b₁ == c₁} {r₁ : c₁ == d₁}
  {a : a₀ == a₁} {b : b₀ == b₁} {c : c₀ == c₁} {d : d₀ == d₁}
  (s₁ : Square p₀ p₁ a b)
  (s₂ : Square q₀ q₁ b c)
  (s₃ : Square r₀ r₁ c d)
  where


 ▪v-filler : PathP (\k -> Square (doubleCompPath-filler p₀ q₀ r₀ k)
                                 (doubleCompPath-filler p₁ q₁ r₁ k)
                                 (\i -> s₁ i (~ k))
                                 (\i -> s₃ i k))
                   s₂ (s₁ ▪v s₂ ▪v s₃)
 ▪v-filler k i j = doubleCompPath-filler (s₁ i) (s₂ i) (s₃ i) k j


 ▪v=▪comp : s₁ ▪v s₂ ▪v s₃ ==
            ▪comp s₂
                 (symP (doubleCompPath-filler p₀ q₀ r₀))
                 (doubleCompPath-filler p₁ q₁ r₁)
                 s₁ s₃
 ▪v=▪comp =
   transP-sym
     (symP (▪v-filler))
     (▪comp-filler s₂
                   (symP (doubleCompPath-filler p₀ q₀ r₀))
                   (doubleCompPath-filler p₁ q₁ r₁)
                   s₁ s₃)




module _ {ℓ : Level} {A : Type ℓ} {N S : A} (q : N == S)
  where

  module case₁ (p₁ p₂ : N == S) (base : Square q (sym p₂) p₁ (sym p₂)) where
    w : Square q q refl refl
    w = refl

    e₁ : Square (sym p₂) refl refl p₂
    e₁ x y = p₂ (~ y ∨ x)
    s₁ : Square refl refl p₁ p₁
    s₁ x y = p₁ x
    n₁ : Square refl p₂ (sym p₂) refl
    n₁ x y = p₂ (y ∨ ~ x)

    e₂ : Square refl p₁ (sym p₁) refl
    e₂ x y = p₁ (y ∨ ~ x)
    s₂ : Square refl p₁ refl p₁
    s₂ x y = p₁ (x ∧ y)
    n₂ : Square (reflᵉ S) refl refl refl
    n₂ = refl


    step₁ : Square q refl p₁ refl
    step₁ = ▪comp base w e₁ s₁ n₁
    step₂ : Square q p₁ refl refl
    step₂ = ▪comp step₁ w e₂ s₂ n₂





  module case₂ (p₁ p₂ : N == S) (base : Square q (sym p₁) p₁ (sym p₂)) where
    w : Square q q refl refl
    w = refl

    e₁ : Square (sym p₁) refl (sym p₁) refl
    e₁ x y = p₁ (~ y ∧ ~ x)
    s₁ : Square refl p₁ refl p₁
    s₁ x y = p₁ (x ∧ y)
    n₁ : Square refl refl (sym p₂) (sym p₂)
    n₁ x y = p₂ (~ x)

    e₂ : Square refl p₂ refl p₂
    e₂ x y = p₂ (x ∧ y)
    s₂ : Square (reflᵉ N) refl refl refl
    s₂ = refl
    n₂ : Square refl p₂ (sym p₂) refl
    n₂ x y = p₂ (y ∨ ~ x)

    step₁ : Square q refl refl (sym p₂)
    step₁ = ▪comp base w e₁ s₁ n₁
    step₂ : Square q p₂ refl refl
    step₂ = ▪comp step₁ w e₂ s₂ n₂


  module cases (p : N == S) (base : Square q (sym p) p (sym p)) where
    private
      module c₁ = case₁ p p base
      module c₂ = case₂ p p base

    w : c₁.w == c₂.w
    w = refl
    n₁ : PathP (\i -> Square refl (\j -> p (~ i ∧ j)) (sym p) (\j -> p (~ i ∨ ~ j))) c₁.n₁ c₂.n₁
    n₁ z x y = p ((y ∧ ~ z) ∨ (~ x))
    s₁ : PathP (\i -> Square refl (\j -> p (~ i ∨ j)) (\j -> p (~ i ∧ j)) p) c₁.s₁ c₂.s₁
    s₁ z x y = p ((y ∨ ~ z) ∧ x)
    n₂ : PathP (\i -> Square refl (\j -> p (~ i ∨ j)) (\j -> p (~ i ∨ (~ j))) refl) c₁.n₂ c₂.n₂
    n₂ z x y = p ((y ∨ ~ x) ∨ ~ z)
    s₂ : PathP (\i -> Square refl (\j -> p (~ i ∧ j)) refl (\j -> p (~ i ∧ j))) c₁.s₂ c₂.s₂
    s₂ z x y = p ((x ∧ y) ∧ ~ z)


    e₁ : PathP (\i -> Square (sym p) (reflᵉ (p (~ i))) (\j -> p (~ i ∨ ~ j)) (\j -> p (~ i ∧ j))) c₁.e₁ c₂.e₁
    e₁ z x y =
      hcomp (\k -> \{ (z = i0) -> p ((~ y ∨ x) ∧ k)
                    ; (z = i1) -> p ((~ y ∧ ~ x) ∧ k)
                    ; (x = i0) -> p (~ y ∧ k)
                    ; (x = i1) -> p (~ z ∧ k)
                    ; (y = i0) -> p ((~ z ∨ ~ x) ∧ k)
                    ; (y = i1) -> p ((~ z ∧ x) ∧ k)
                    })
        N

    e₂ : PathP (\i -> Square (reflᵉ (p (~ i))) p (\j -> p (~ i ∧ ~ j)) (\j -> p (~ i ∨ j))) c₁.e₂ c₂.e₂
    e₂ z x y = e₁ z (~ x) (~ y)


    step₁ : PathP (\i -> Square q refl (\j -> p (~ i ∧ j)) (\j -> p (~ i ∨ ~ j))) c₁.step₁ c₂.step₁
    step₁ i = ▪comp base (w i) (e₁ i) (s₁ i) (n₁ i)
    step₂ : c₁.step₂ == c₂.step₂
    step₂ i = ▪comp (step₁ i) (w i) (e₂ i) (s₂ i) (n₂ i)
