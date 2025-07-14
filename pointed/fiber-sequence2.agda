{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.fiber-sequence2 where

open import base
open import cubical
open import equivalence
open import equality-path
open import pointed.base
open import truncation
open import functions

kernel∙ : {ℓA ℓB : Level} {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} -> (A∙ ->∙ B∙) -> Type∙ (ℓ-max ℓA ℓB)
kernel∙ {A∙ = (A , ★A)} {B∙ = (B , ★B)} (->∙-cons f p) = fiber f ★B , (★A , p)

kernel∙-inc : {ℓA ℓB : Level} {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} -> (f : A∙ ->∙ B∙) ->
              (kernel∙ f) ->∙ A∙
kernel∙-inc f = ->∙-cons fst refl

const∙ : {ℓA ℓB : Level} (A∙ : Type∙ ℓA) (B∙ : Type∙ ℓB) -> (A∙ ->∙ B∙)
const∙ A∙ (B , ★B) = ->∙-cons (\_ -> _) refl

private
  module _ {ℓ : Level} {A∙@(A , ★A) : Type∙ ℓ} {B∙@(B , ★B) : Type∙ ℓ} (f∙ : A∙ ->∙ B∙) (magic : Magic) where
    isConst : {C∙ : Type∙ ℓ} -> (C∙ ->∙ A∙) -> Type ℓ
    isConst g∙ = ∀ c -> app∙ f∙ (app∙ g∙ c) == ★B

    isConstComp : {C∙ : Type∙ ℓ} -> (C∙ ->∙ A∙) -> Type ℓ
    isConstComp {C∙} g∙ = g∙ >∙> f∙ == const∙ C∙ B∙


    record isPullback∙ {C∙ : Type∙ ℓ} (g∙ : C∙ ->∙ A∙) : Type (ℓ-suc ℓ) where
      field
        const : isConstComp g∙
        universal :
          {D∙ : Type∙ ℓ} -> (h∙ : D∙ ->∙ A∙) ->
          isConstComp h∙ ->
          ∃![ e∙ ∈ (D∙ ->∙ C∙) ] (h∙ == e∙ >∙> g∙)

{-
    isPullback∙-kernel∙-inc : isPullback∙ (kernel∙-inc f∙)
    isPullback∙-kernel∙-inc = record
      { const = const-comp
      ; universal = u
      }
      where
      const-comp : isConstComp (kernel∙-inc f∙)
      const-comp i =
        ->∙-cons
          (\ ((v , p) : fiber (app∙ f∙) ★B) -> p i)
          (ans i)
        where
        ans : PathP (\j -> ->∙-path f∙ j == ★B) (refl >=> ->∙-path f∙) refl
        ans =
          transP-right (compPath-refl-left _) (\j k -> ->∙-path f∙ (j ∨ k))

      u : {D∙ : Type∙ ℓ} -> (h∙ : D∙ ->∙ A∙) ->
       isConstComp h∙ ->
       ∃![ e∙ ∈ (D∙ ->∙ kernel∙ f∙) ] (h∙ == e∙ >∙> (kernel∙-inc f∙))
      u {D∙ = (D , ★D)} h∙ const-h∙ = (->∙-cons e ep , magic) , magic
        where
        e : D -> fiber (app∙ f∙) ★B
        e d = app∙ h∙ d , \i -> app∙ (const-h∙ i) d
        ep : e ★D == (★A , ->∙-path f∙)
        ep i = ->∙-path h∙ i , magic
-}




record LeftLongFiberSequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Ty∙ : Nat -> Type∙ ℓ
    f∙ : (n : Nat) -> (Ty∙ (suc n) ->∙ Ty∙ n)
    -- kernel-paths : (n : Nat) -> (Ty∙ (suc (suc n)) , f∙ (suc n)) == (kernel∙ (f∙ n) , kernel∙-inc (f∙ n))

  Ty : Nat -> Type ℓ
  Ty n = ⟨ Ty∙ n ⟩
  ★ⁿ : (n : Nat) -> Ty n
  ★ⁿ n = snd (Ty∙ n)
  f : (n : Nat) -> Ty (suc n) -> Ty n
  f n = app∙ (f∙ n)


module _ {ℓ : Level} (s₁ s₂ : LeftLongFiberSequence ℓ) where
  private
    module s₁ = LeftLongFiberSequence s₁
    module s₂ = LeftLongFiberSequence s₂

{-
  same-sequence :
    (pT₀ : s₁.Ty∙ 0 == s₂.Ty∙ 0) ->
    (pT₁ : s₁.Ty∙ 1 == s₂.Ty∙ 1) ->
    (pf₀ : PathP (\i -> pT₁ i ->∙ pT₀ i) (s₁.f∙ 0) (s₂.f∙ 0)) ->
    s₁ == s₂
  same-sequence pT₀ pT₁ pf₀ = ?
    where

    pk₀ : kernel∙ (s₁.f∙ 0) == kernel∙ (s₂.f∙ 0)
    pk₀ i = kernel∙ (pf₀ i)

    -- pT₂ : s₁.Ty∙ 2 == s₂.Ty∙ 2
    -- pT₂ = s₁.kernel-paths 0 ∙∙ pk₀ ∙∙ sym (s₂.kernel-paths 0)
-}

