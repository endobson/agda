{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.short-sequence where

open import base
open import functions
open import equivalence
open import equality.fundamental
open import equivalence.2of3
open import equality-path
open import cubical
open import pointed.base
open import isomorphism
open import pullback


record ShortSequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    F∙ E∙ B∙ : Type∙ ℓ
    f : F∙ ->∙ E∙
    g : E∙ ->∙ B∙
    commutes : f >∙> g == const->∙

  F E B : Type ℓ
  F = ⟨ F∙ ⟩
  E = ⟨ E∙ ⟩
  B = ⟨ B∙ ⟩

  ★B : B
  ★B = snd B∙


  -- TODO figure out better name
  α : ∀ (e : E) -> fiber (app∙ f) e -> (app∙ g e == ★B)
  α e (v , p) = cong (app∙ g) (sym p) >=> (\i -> app∙ (commutes i) v)

  cone : Cone (\(_ : Top) -> ★B) (app∙ g) F
  cone = (\_ -> tt) , (app∙ f) , (\i -> app∙ (commutes (~ i)))


isShortFiberSequence : {ℓ : Level} -> ShortSequence ℓ -> Type ℓ
isShortFiberSequence s = isPullbackCone {g = app∙ s.g} s.cone
  where
  module s = ShortSequence s

isInfiniteExactSequence : {ℓ : Level} -> ShortSequence ℓ -> Type ℓ
isInfiniteExactSequence s = ∀ (e : s.E) -> isEquiv (s.α e)
  where
  module s = ShortSequence s


module _ {ℓ : Level} (s : ShortSequence ℓ) (magic : Magic) where
  private
    module s = ShortSequence s

    T1 : Type ℓ
    T1 = s.F

    T2 : Type ℓ
    T2 = Pullback (\(_ : Top) -> s.★B) (app∙ s.g)

    T4 : Type ℓ
    T4 = Σ[ z ∈ s.E ] (app∙ s.g z == s.★B)

    T2≃T4 : T2 ≃ T4
    T2≃T4 = isoToEquiv (iso fwd bkw (\_ -> refl) (\_ -> refl))
      where
      fwd : T2 -> T4 
      fwd (tt , z , p) = z , sym p
      bkw : T4 -> T2 
      bkw (z , p) = (tt , z , sym p)

    T3 : Type ℓ
    T3 = Σ[ e ∈ s.E ] (fiber (app∙ s.f) e)

    T1≃T3 : T1 ≃ T3
    T1≃T3 = isoToEquiv (iso fwd bkw fb bf)
      where
      fwd : T1 -> T3
      fwd f = (app∙ s.f f , f , refl)
      bkw : T3 -> T1
      bkw (_ , f , _) = f
      fb : ∀ x -> fwd (bkw x) == x
      fb (_ , f , p) i = (p i , f , (\j -> p (i ∧ j)))
      bf : ∀ x -> bkw (fwd x) == x
      bf _ = refl

    T3->T4 : T3 -> T4
    T3->T4 (e , fib) = e , (s.α e fib)

    T1->T2 : T1 -> T2
    T1->T2 = gap {g = app∙ s.g} s.cone

    path-T1->T4 : (eqFun T2≃T4 ∘ T1->T2) == (T3->T4 ∘ eqFun T1≃T3)
    path-T1->T4 i v = (app∙ s.f v , compPath-refl-left (\j -> app∙ (s.commutes j) v) (~ i))

  isShortFiberSequence->isInfiniteExactSequence :
    isShortFiberSequence s -> isInfiniteExactSequence s
  isShortFiberSequence->isInfiniteExactSequence short = isEq-α
    where
    isEq-T1->T4₁ : isEquiv (eqFun T2≃T4 ∘ T1->T2)
    isEq-T1->T4₁ = isEquiv-2of3₃ (snd T2≃T4) short 
    isEq-T1->T4₂ : isEquiv (T3->T4 ∘ eqFun T1≃T3)
    isEq-T1->T4₂ = subst isEquiv path-T1->T4 isEq-T1->T4₁

    isEq-T3->T4 : isEquiv T3->T4
    isEq-T3->T4 = isEquiv-2of3₁ (snd T1≃T3) isEq-T1->T4₂

    isEq-α : ∀ e -> isEquiv (s.α e)
    isEq-α = eqInv (isEquivFamily-eq s.α) isEq-T3->T4

  isInfiniteExactSequence->isShortFiberSequence :
    isInfiniteExactSequence s -> isShortFiberSequence s
  isInfiniteExactSequence->isShortFiberSequence exact =
    isEquiv-2of3₂ (snd T2≃T4) isEq-T1->T4₂
    where
    isEq-T3->T4 : isEquiv T3->T4
    isEq-T3->T4 = eqFun (isEquivFamily-eq s.α) exact

    isEq-T1->T4₁ : isEquiv (T3->T4 ∘ eqFun T1≃T3)
    isEq-T1->T4₁ = isEquiv-2of3₃ isEq-T3->T4 (snd T1≃T3)
    isEq-T1->T4₂ : isEquiv (eqFun T2≃T4 ∘ T1->T2)
    isEq-T1->T4₂ = subst isEquiv (sym path-T1->T4) isEq-T1->T4₁
