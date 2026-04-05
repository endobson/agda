{-# OPTIONS --cubical --safe --exact-split #-}

module category2.set where

open import base
open import category2.base
open import hlevel.base
open import hlevel.pi
open import hlevel.htype
open import hlevel
open import hlevel.isomorphism
open import isomorphism

module _ {ℓ : Level} (hS₁@(D₁ , isSet₁) hS₂@(D₂ , isSet₂) : hSet ℓ) where
  record hSet→ : Type ℓ where
    constructor [_]
    field
      f : D₁ -> D₂

module _ {ℓ : Level} {hS₁@(D₁ , isSet₁) hS₂@(D₂ , isSet₂) : hSet ℓ} where
  opaque
    isSet-hSet→ : isSet (hSet→ hS₁ hS₂)
    isSet-hSet→ = iso-isSet (iso [_] hSet→.f (\_ -> refl) (\_ -> refl))
                            (isSetΠ \_ -> isSet₂)



module _ {ℓ : Level}  where
  instance
    hSet-CategoryStr : CategoryStr (hSet→ {ℓ = ℓ})
    hSet-CategoryStr = record
      { id = [ (\x -> x) ]
      ; _⋆_ = \{ [ f ] [ g ] -> [ (\x -> g (f x)) ] }
      ; ⋆-left-idᵉ = \_ -> refl
      ; ⋆-right-idᵉ = \_ -> refl
      ; ⋆-assocᵉ = \_ _ _ -> refl
      ; isSet-Mor = isSet-hSet→
      }

module _ (ℓ : Level) where
  hSetC : Category (ℓ-suc ℓ) ℓ
  hSetC = Category▪ hSet-CategoryStr


lift-hSet-Functor : {ℓ₁ : Level} (ℓ₂ : Level) -> Functor (hSetC ℓ₁) (hSetC (ℓ-max ℓ₁ ℓ₂))
lift-hSet-Functor {ℓ₁} ℓ₂ = record
  { obj = lift-hSet
  ; mor = lift-hSet→
  ; preserves-idᵉ = \_ -> refl
  ; preserves-⋆ᵉ = \_ _ -> refl
  }
  where
  lift-hSet : hSet ℓ₁ -> hSet (ℓ-max ℓ₁ ℓ₂)
  lift-hSet (T , h) = Lift ℓ₂ T , isSet-Lift h

  lift-hSet→ : {s₁ s₂ : hSet ℓ₁} -> hSet→ s₁ s₂ -> hSet→ (lift-hSet s₁) (lift-hSet s₂)
  lift-hSet→ [ f ] = [ (\ (lift e) -> lift (f e)) ]
