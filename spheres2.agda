{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import cubical
open import hit-int renaming (Int to ℤ)
open import nat using (ℕ)
open import equality-path
open import functions
open import functions.embedding
open import cubical
open import equivalence
open import univalence
open import isomorphism
open import truncation
open import hlevel

module spheres2 where

data S1 : Type₀ where
  base : S1
  loop : base == base

ΩS1 : Type₀
ΩS1 = base == base

loopsℕ : ℕ -> ΩS1
loopsℕ zero = refl
loopsℕ (suc n) = loop >=> loopsℕ n

loopsℤ : ℤ -> ΩS1
loopsℤ (nonneg n) = loopsℕ n
loopsℤ (nonpos n) = sym (loopsℕ n)
loopsℤ (same-zero i) = refl

loopsℕ-commute : ∀ n -> loop >=> loopsℕ n == loopsℕ n >=> loop
loopsℕ-commute zero i = (\j -> loop (~ i ∧ j)) >=> (\j -> loop (~ i ∨ j))
loopsℕ-commute (suc n) =
  cong (loop >=>_) (loopsℕ-commute n) >=>
       sym (compPath-assoc loop (loopsℕ n) loop)

add1Equiv : ℤ ≃ ℤ
add1Equiv = (isoToEquiv (iso add1 sub1 add1-sub1 sub1-add1))

helix : S1 -> Type₀
helix base = ℤ
helix (loop i) = ua add1Equiv i

winding-number' : (pt : S1) -> base == pt -> helix pt
winding-number' pt path = transport (cong helix path) (nonneg 0)

winding-number : ΩS1 -> ℤ
winding-number = winding-number' base

winding-number-loopsℕ⁺ : ∀ n -> winding-number (loopsℕ n) == (nonneg n)
winding-number-loopsℕ⁺ zero = refl
winding-number-loopsℕ⁺ (suc n) =
  cong winding-number (loopsℕ-commute n) >=>
  cong add1 (winding-number-loopsℕ⁺ n)

winding-number-loopsℕ⁻ : ∀ n -> winding-number (sym (loopsℕ n)) == (nonpos n)
winding-number-loopsℕ⁻ zero = same-zero
winding-number-loopsℕ⁻ (suc n) = cong sub1 (winding-number-loopsℕ⁻ n)


winding-number-loopsℤ : ∀ x -> winding-number (loopsℤ x) == x
winding-number-loopsℤ (nonneg n) = winding-number-loopsℕ⁺ n
winding-number-loopsℤ (nonpos n) = winding-number-loopsℕ⁻ n
winding-number-loopsℤ (same-zero i) j = same-zero (i ∧ j)


base-s : (z : ℤ) -> PathP (\i -> base == loop i) (loopsℤ (sub1 z)) (loopsℤ z)
base-s (nonneg 0) = base-s (nonpos 0)
base-s (same-zero i) = base-s (nonpos 0)
base-s (nonneg (suc n)) =
  transP-mid (sym (compPath-refl-right (loopsℕ n)))
             ans
             (sym (loopsℕ-commute n))
  where
  ans : PathP (\i -> base == loop i) (loopsℕ n >=> refl) (loopsℕ n >=> loop)
  ans i = loopsℕ n >=> (\j -> loop (j ∧ i))
base-s (nonpos n) = transP-left ans' (compPath-refl-right (sym (loopsℕ n)))
  where
  ans' : PathP (\i -> base == loop i) (sym (loopsℕ n) >=> sym loop) (sym (loopsℕ n) >=> refl)
  ans' i = sym (loopsℕ n) >=> (\j -> loop (~ j ∨ i))


sub-ans : (i : I) (z : helix (loop i)) ->
          Sub (base == loop i) (i ∨ ~ i) (\{ (i = i0) -> loopsℤ z
                                           ; (i = i1) -> loopsℤ z })
sub-ans i z = inS top-s
  where
  check-z : Glue ℤ (\{ (i = i0) -> (ℤ , add1Equiv) ; (i = i1) -> (ℤ , idEquiv ℤ) })
  check-z = z

  z' : ℤ
  z' = unglue (i ∨ ~ i) z

  top-s : base == loop i
  top-s j = hcomp (\k -> \{ (j = i0) -> base
                          ; (j = i1) -> loop i
                          ; (i = i0) -> loopsℤ (sub1-add1 z k) j
                          ; (i = i1) -> loopsℤ z' j
                          })
                  (base-s z' i j)


decode : (pt : S1) -> helix pt -> base == pt
decode base z = loopsℤ z
decode (loop i) z = outS (sub-ans i z)


loopsℤ-winding-number : ∀ p -> loopsℤ (winding-number p) == p
loopsℤ-winding-number = apJ base
  where
  apJ : ∀ pt path -> decode pt (winding-number' pt path) == path
  apJ pt = J (\pt path -> decode pt (winding-number' pt path) == path) refl


ΩS1≃ℤ : ΩS1 ≃ ℤ
ΩS1≃ℤ = isoToEquiv (iso winding-number loopsℤ winding-number-loopsℤ loopsℤ-winding-number)

Connected-S1 : ∀ pt -> ∥ base == pt ∥
Connected-S1 base = ∣ loop ∣
Connected-S1 (loop i) = ans i
  where
  ans : PathP (\i -> ∥ base == loop i ∥) (∣ loop ∣) (∣ loop ∣)
  ans = isProp->PathP (\i -> squash)

Injective-Top->S1 : Σ[ f ∈ (Top -> S1) ] (Injective f)
Injective-Top->S1 = (\_ -> base) , (\_ -> refl)

¬Top↪S1 : ¬ (Top ↪ S1)
¬Top↪S1 (f , isEmbed-f) = unsquash isPropBot (∥-map handle (Connected-S1 pt))
  where
  pt = f tt
  propFibers : hasPropFibers f
  propFibers = eqFun isEmbedding-eq-hasPropFibers isEmbed-f

  handle : base == pt -> Bot
  handle p = transport (cong Zeroℤ ans5) tt
    where

    fib1 : fiber f pt
    fib1 = tt , sym p ∙∙ refl ∙∙ p
    fib2 : fiber f pt
    fib2 = tt , sym p ∙∙ loop ∙∙ p

    ans1 : (sym p ∙∙ refl ∙∙ p) == (sym p ∙∙ loop ∙∙ p)
    ans1 = cong snd (propFibers pt fib1 fib2)

    ans2 : (p ∙∙ (sym p ∙∙ refl ∙∙ p) ∙∙ sym p) == (p ∙∙ (sym p ∙∙ loop ∙∙ p) ∙∙ sym p)
    ans2 i = p ∙∙ ans1 i ∙∙ sym p

    ans3 : ∀ {path : ΩS1} -> (p ∙∙ (sym p ∙∙ path ∙∙ p) ∙∙ sym p) ==
                             (refl ∙∙ (refl ∙∙ path ∙∙ refl) ∙∙ refl)
    ans3 {path} i = (q ∙∙ (r ∙∙ path ∙∙ q) ∙∙ r)
      where
      q : Path S1 base (p (~ i))
      q j = p (~ i ∧ j)

      r : Path S1 (p (~ i)) base
      r j = p (~ i ∧ ~ j)

    shrink : ∀ {path : ΩS1} -> (refl ∙∙ path ∙∙ refl) == path
    shrink {path} = sym (doubleCompPath-filler refl path refl)

    shrink2 : ∀ {path : ΩS1} -> (p ∙∙ (sym p ∙∙ path ∙∙ p) ∙∙ sym p) == path
    shrink2 = ans3 >=> shrink >=> shrink

    ans4 : refl == loop
    ans4 = sym shrink2 >=> ans2 >=> shrink2

    ans5 : nonneg 0 == nonneg 1
    ans5 = cong winding-number ans4

    Zeroℤ : ℤ -> Type₀
    Zeroℤ (nonneg zero) = Top
    Zeroℤ (nonneg (suc _)) = Bot
    Zeroℤ (nonpos zero) = Top
    Zeroℤ (nonpos (suc _)) = Bot
    Zeroℤ (same-zero i) = Top







