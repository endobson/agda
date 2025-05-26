{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import cubical
open import hit-int
open import nat using (ℕ)
open import equality-path
open import functions
open import cubical
open import equivalence
open import univalence
open import isomorphism

module spheres where

data S1 : Type₀ where
  base : S1
  loop : base == base

ΩS1 : Type₀
ΩS1 = base == base


-- A circle of Types
-- The base point is the integers, and looping is add1

add1Equiv : ℤ ≃ ℤ
add1Equiv = (isoToEquiv (iso add1 sub1 add1-sub1 sub1-add1))

helix : S1 -> Type₀
helix base = ℤ
helix (loop i) = ua add1Equiv i


encode : ∀ pt -> base == pt -> helix pt
encode pt path = substᵉ helix path (int 0)

ΩS1->ℤ : ΩS1 -> ℤ
ΩS1->ℤ = encode base

ℕ->ΩS1 : ℕ -> ΩS1
ℕ->ΩS1 zero = refl
ℕ->ΩS1 (suc n) = (ℕ->ΩS1 n) >=> loop

loopsℕ : ℕ -> ΩS1
loopsℕ = ℕ->ΩS1

private
  loops-commute : ∀ n -> loopsℕ n >=> loop == loop >=> loopsℕ n
  loops-commute zero = compPath-refl-left loop >=> sym (compPath-refl-right loop)
  loops-commute (suc n) =
    cong (_>=> loop) (loops-commute n) >=>
    compPath-assoc loop (loopsℕ n) loop


ℤ->ΩS1 : ℤ -> ΩS1
ℤ->ΩS1 (nonneg x) = loopsℕ x
ℤ->ΩS1 (nonpos x) = sym (loopsℕ x)
ℤ->ΩS1 (same-zero i) = refl

winding-loopsℕ⁺ : ∀ n -> ΩS1->ℤ (loopsℕ n) == nonneg n
winding-loopsℕ⁺ zero = refl
winding-loopsℕ⁺ (suc n) = cong add1 (winding-loopsℕ⁺ n)

winding-loopsℕ⁻ : ∀ n -> ΩS1->ℤ (sym (loopsℕ n)) == nonpos n
winding-loopsℕ⁻ zero = same-zero
winding-loopsℕ⁻ (suc n) = sym (reorder n) >=> cong sub1 (winding-loopsℕ⁻ n)
  where
  reorder : (n : ℕ) -> ΩS1->ℤ (sym (loop >=> (loopsℕ n))) == ΩS1->ℤ (sym (loopsℕ n >=> loop))
  reorder n i = ΩS1->ℤ (sym (loops-commute n (~ i)))


ℤ->ΩS1->ℤ : ∀ z -> (ΩS1->ℤ (ℤ->ΩS1 z)) == z
ℤ->ΩS1->ℤ (nonneg x) = winding-loopsℕ⁺ x
ℤ->ΩS1->ℤ (nonpos x) = winding-loopsℕ⁻ x
ℤ->ΩS1->ℤ (same-zero i) j = same-zero (i ∧ j)


decodeSquareℕ : (n : ℕ) -> PathP (\i -> base == loop i) (ℕ->ΩS1 n) (ℕ->ΩS1 (suc n))
decodeSquareℕ n = transP-right step1 step3
  where
  step1 : (ℕ->ΩS1 n) == ((ℕ->ΩS1 n) >=> refl)
  step1 = sym (compPath-refl-right (ℕ->ΩS1 n))

  step2 : PathP (\i -> base == loop i) refl loop
  step2 i j = loop (i ∧ j)

  step3 : PathP (\i -> base == loop i) ((ℕ->ΩS1 n) >=> refl) ((ℕ->ΩS1 n) >=> loop)
  step3 i = (ℕ->ΩS1 n) >=> step2 i

decodeSquareℕ2 : (n : ℕ) -> PathP (\i -> base == loop i) (sym (ℕ->ΩS1 (suc n))) (sym (ℕ->ΩS1 n))
decodeSquareℕ2 n = transP-mid step3 step4 step1
  where
  step1 : (sym (ℕ->ΩS1 n) >=> refl) == sym (ℕ->ΩS1 n)
  step1 = (compPath-refl-right (sym (ℕ->ΩS1 n)))

  step2 : PathP (\i -> base == loop i) (sym loop) refl
  step2 i j = loop (i ∨ (~ j))

  step3 : ((sym loop) >=> sym (ℕ->ΩS1 n)) == (sym (loopsℕ n) >=> sym loop)
  step3 = cong sym (loops-commute n)

  step4 : PathP (\i -> base == loop i) (sym (loopsℕ n) >=> sym loop) (sym (loopsℕ n) >=> refl)
  step4 i = sym (loopsℕ n) >=> step2 i


decodeSquare : (n : ℤ) -> PathP (\i -> base == loop i) (ℤ->ΩS1 (sub1 n)) (ℤ->ΩS1 n)
decodeSquare (nonneg (suc x)) = decodeSquareℕ x
decodeSquare (nonneg 0) = decodeSquareℕ2 0
decodeSquare (same-zero i) = decodeSquareℕ2 0
decodeSquare (nonpos x) = decodeSquareℕ2 x



-- decodeSquare n i j = hfill (\ k -> \{ (i = i0) -> ?
--                                     }) (inS ?) i

decode : ∀ pt -> helix pt -> base == pt
decode base z = ℤ->ΩS1 z
decode (loop i) y = ans
  where
  y' : Glue ℤ (\{ (i = i0) -> (ℤ , add1Equiv) ; (i = i1) -> (ℤ , idEquiv ℤ) })
  y' = y

  n : ℤ
  n = unglue (i ∨ ~ i) y


  s : PathP (\i -> base == loop i) (ℤ->ΩS1 (sub1 n)) (ℤ->ΩS1 n)
  s = decodeSquare n

  si : base == loop i
  si = decodeSquare n i

  ans : base == (loop i)
  ans j = hcomp (λ k → λ { (i = i0) → ℤ->ΩS1 (sub1-add1 y k) j
                         ; (i = i1) → ℤ->ΩS1 y j
                         ; (j = i0) → base
                         ; (j = i1) → loop i })
                (decodeSquare n i j)

decode-encode : ∀ pt -> (path : base == pt) -> decode pt (encode pt path) == path
decode-encode pt = J (\pt path -> decode pt (encode pt path) == path) (\_ -> refl)

ΩS1->ℤ->ΩS1 : ∀ p -> ℤ->ΩS1 (ΩS1->ℤ p) == p
ΩS1->ℤ->ΩS1 = decode-encode base

ΩS1≃ℤ : ΩS1 ≃ ℤ
ΩS1≃ℤ = isoToEquiv (iso ΩS1->ℤ ℤ->ΩS1 ℤ->ΩS1->ℤ ΩS1->ℤ->ΩS1)


--
--
-- square-s1-ex1 : Square refl loop refl refl
-- square-s1-ex1 = ?


-- loop!=refl : loop != refl
-- loop!=refl = ?

-- -- Embed Top into S1
-- private
--   -- Top↪S1 : Top ↪ S1
--   -- Top↪S1 = f , isEmbed-f
--   --   where
--   --   f : Top -> S1
--   --   f tt = base
--
--   --   isEmbed-f : isEmbedding f
--   --   isEmbed-f tt tt .equiv-proof path = fib , ?
--   --     where
--   --     fib : fiber (cong f) path
--   --     fib = refl , ?
--
--
--   ¬Top↪S1 : ¬ (Top ↪ S1)
--   ¬Top↪S1 (f , isEmbed-f) = ?
--     where
--     contr : isContr (fiber (cong f) refl)
--     contr = isEmbed-f tt tt .equiv-proof refl


