{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.pushout where

open import base
open import pointed.base
open import pushout
open import equality-path
open import equivalence
open import isomorphism

module _ {ℓB ℓC : Level} (B∙@(B , ★B) : Type∙ ℓB) (C∙@(C , ★C) : Type∙ ℓC) where
  Join∙ : Type∙ (ℓ-max ℓB ℓC)
  Join∙ = Join B C , (inj-l ★B)

module _ {ℓB ℓC : Level} ((B , ★B) : Type∙ ℓB) ((C , ★C) : Type∙ ℓC) where
  Wedge : Type (ℓ-max ℓB ℓC)
  Wedge = Pushout {A = Top} (\_ -> ★B) (\_ -> ★C)
  Wedge∙ : Type∙ (ℓ-max ℓB ℓC)
  Wedge∙ = Wedge , inj-l ★B

module _ {ℓB ℓC : Level} (B∙@(B , ★B) : Type∙ ℓB) (C∙@(C , ★C) : Type∙ ℓC) where
  Wedge->×ᵉ : Wedge B∙ C∙ -> B × C
  Wedge->×ᵉ (inj-l b) = b , ★C
  Wedge->×ᵉ (inj-r c) = ★B , c
  Wedge->×ᵉ (glue tt i) = ★B , ★C

module _ {ℓB ℓC : Level} {B∙@(B , ★B) : Type∙ ℓB} {C∙@(C , ★C) : Type∙ ℓC} where
  Wedge->× : Wedge B∙ C∙ -> B × C
  Wedge->× = Wedge->×ᵉ B∙ C∙

module _ {ℓB ℓC : Level} (B∙@(B , ★B) : Type∙ ℓB) (C∙@(C , ★C) : Type∙ ℓC) where
  Smash : Type (ℓ-max ℓB ℓC)
  Smash = Pushout {A = Wedge B∙ C∙} (\_ -> tt) Wedge->×
  Smash∙ : Type∙ (ℓ-max ℓB ℓC)
  Smash∙ = Smash , inj-r (★B , ★C)


module _ {ℓB₁ ℓB₂ ℓC₁ ℓC₂ : Level}
         {B₁ : Type∙ ℓB₁} {B₂ : Type∙ ℓB₂} {C₁ : Type∙ ℓC₁} {C₂ : Type∙ ℓC₂} where

  Join∙-eq∙ : (B₁ ≃∙ B₂) -> (C₁ ≃∙ C₂) -> (Join∙ B₁ C₁) ≃∙ (Join∙ B₂ C₂)
  Join∙-eq∙ ((fB , eB) , pB) ((fC , eC) , pC) =
    isoToEquiv (iso for back fb bf) , cong inj-l pB
    where
    for : ⟨ Join∙ B₁ C₁ ⟩ -> ⟨ Join∙ B₂ C₂ ⟩
    for (inj-l b) = inj-l (fB b)
    for (inj-r c) = inj-r (fC c)
    for (glue (b , c) i) = glue (fB b , fC c) i

    back : ⟨ Join∙ B₂ C₂ ⟩ -> ⟨ Join∙ B₁ C₁ ⟩
    back (inj-l b) = inj-l (isEqInv eB b)
    back (inj-r c) = inj-r (isEqInv eC c)
    back (glue (b , c) i) = glue (isEqInv eB b , isEqInv eC c) i

    fb : ∀ x -> for (back x) == x
    fb (inj-l b) = cong inj-l (isEqSec eB b)
    fb (inj-r c) = cong inj-r (isEqSec eC c)
    fb (glue (b , c) i) j = glue (isEqSec eB b j , isEqSec eC c j) i
    bf : ∀ x -> back (for x) == x
    bf (inj-l b) = cong inj-l (isEqRet eB b)
    bf (inj-r c) = cong inj-r (isEqRet eC c)
    bf (glue (b , c) i) j = glue (isEqRet eB b j , isEqRet eC c j) i
