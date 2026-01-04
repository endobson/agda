{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.initial.base where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality-path
open import nat
open import semiring
open import semiring.instances.nat.base

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         (S : Semiring ACM) where
  private
    instance
      IS = S

  record ℕ->SemiringStr : Type ℓD where

    field
      f : ℕ -> D
      fʰ : Semiringʰ f

module _ {ℓD : Level} (D : Type ℓD) {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}} where
  ℕ->Semiring-Op : Type ℓD
  ℕ->Semiring-Op = ℕ->SemiringStr S

module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}
         {{S : Semiring ACM}} where
  ℕ->SemiringStr-cons : {f : ℕ -> D} -> Semiringʰ f -> ℕ->Semiring-Op D
  ℕ->SemiringStr-cons {f} fʰ = record { f = f ; fʰ = fʰ }

  ℕ->SemiringStr-cons' :
    (f : ℕ -> D) ->
    f 0# == 0# -> f 1# == 1# -> (∀ x y -> f (x + y) == f x + f y) ->
    ℕ->Semiring-Op D
  ℕ->SemiringStr-cons' f preserves-0# preserves-1# preserves-+ =
    ℕ->SemiringStr-cons (record
      { +ʰ = record
        { preserves-ε = preserves-0#
        ; preserves-∙ = preserves-+
        }
      ; *ʰ = record
        { preserves-ε = preserves-1#
        ; preserves-∙ = preserves-*
        }
      })
    where
    opaque
      preserves-* : ∀ x y -> f (x * y) == f x * f y
      preserves-* zero y = preserves-0# >=> sym *-left-zero >=> *-left (sym preserves-0#)
      preserves-* (suc x) y =
        preserves-+ y (x * y) >=>
        +-cong (sym *-left-one >=> *-left (sym preserves-1#)) (preserves-* x y) >=>
        sym *-distrib-+-right >=>
        *-left (sym (preserves-+ 1 x))
