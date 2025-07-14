{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.freudenthal4-eq where




open import base
open import pointed.base
open import cubical
open import equality-path
open import equality.square
open import equality.dependent-path
open import base
open import funext
open import functions.embedding
open import isomorphism
open import sigma
open import univalence

open import additive-group
open import order
open import functions
open import nat.order
open import order.instances.nat
open import additive-group.instances.nat
open import cubical
open import equality-path
open import equality.square
open import equality.square-compose
open import equality.square-compose2
open import equality.path-composition-equivalence
open import connected
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import truncation.generic
open import truncation.generic.path
open import truncation.generic.map
open import equivalence.base
open import equivalence
open import connected.wedge
open import connected.reduce

open import pointed.suspension


module _ {ℓ : Level} {A : Type ℓ} where
  transport=compPath : {a₁ a₂ a₃ : A} -> (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) ->
    transport (\i -> a₁ == p₂ i) p₁ == p₁ >=> p₂
  transport=compPath {a₁} {a₂} {a₃} p₁ p₂ i =
    transp (\j -> a₁ == p₂ (i ∨ j)) i ((compPath-filler p₁ p₂) i)



module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  ΩΣf : A -> ⟨ Ω (Susp∙ A∙) ⟩
  ΩΣf a = meridian a >=> sym (meridian ★A)


module freudenthal {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) {n : Nat} (cA : isConnectedₙ n A) (magic : Magic) where

  module _ (a : A) (q : Path (Susp A) north south) where

    path-for : (meridian a >=> sym (meridian ★A)) == q >=> sym (meridian ★A) ->
               (meridian a == q)
    path-for sq =
      ▪comp sq
            (\i j -> compPath-filler (meridian a) (sym (meridian ★A)) i j)
            (\i j -> compPath-filler q (sym (meridian ★A)) (~ i) j)
            (\i j -> north)
            (\i j -> meridian ★A j)


    path-eq : ((meridian a >=> sym (meridian ★A)) == q >=> sym (meridian ★A)) ≃
              (meridian a == q)
    path-eq = path-for , isEquiv-▪comp _ _ _ _
