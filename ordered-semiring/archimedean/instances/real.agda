{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-semiring.archimedean.instances.real where

open import additive-group
open import base
open import equality
open import nat
open import order
open import order.instances.rational
open import order.instances.real
open import ordered-semiring
open import ordered-semiring.archimedean
open import ordered-semiring.archimedean.instances.rational
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import nat.order
open import real
open import real.arithmetic.rational
open import real.order
open import real.rational
open import ring.implementations.real
open import ring.implementations.rational
open import semiring
open import semiring.initial
open import truncation

private
  prop : ArchimedeanPropertyⁱ ℝ
  prop {a} {b} 0<a 0<b = ∥-bind2 handle (Real.Inhabited-U a) (Real.isUpperOpen-L b 0# (ℝ<->L 0<b))
    where
    handle : Σ[ a' ∈ ℚ ] (Real.U a a') -> Σ[ b' ∈ ℚ ] (0# < b' × Real.L b b') ->
             ∃[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))
    handle (a' , aU-a') (b' , (0<b' , bL-b')) = ∥-map handle2 (archimedean-property 0<a' 0<b')
      where
      0<a' : 0# < a'
      0<a' = U->ℚ< (trans-ℝ<-U 0<a aU-a')
      handle2 : Σ[ n ∈ ℕ ] (a' < (ℕ->Semiring n * b')) -> Σ[ n ∈ ℕ ] (a < (ℕ->Semiring n * b))
      handle2 (n , a'<nb') =
        n ,
        trans-<-=
          (trans-<-≤
            (trans-< (U->ℝ< aU-a')
                     (trans-<-= (ℚ->ℝ-preserves-< (trans-<-= a'<nb' (*-left (ℕ->Semiring-ℚ-path n))))
                                ℚ->ℝ-preserves-*))
            (*₁-preserves-≤ (ℚ->ℝ-preserves-≤ (ℕ->ℚ-preserves-≤ 0 n zero-≤))
                            (weaken-< (L->ℝ< bL-b'))))
          (*-left (sym (ℕ->Semiring-ℝ-path n)))

abstract
  instance
    ArchimedeanSemring-ℝ : ArchimedeanSemiringⁱ ℝ
    ArchimedeanSemring-ℝ = record { prop = prop }
