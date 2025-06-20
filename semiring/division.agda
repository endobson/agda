{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.division where

open import additive-group
open import base
open import order
open import order.instances.nat
open import equality-path
open import hlevel
open import semiring
open import semiring.exponentiation
open import truncation

module _ {ℓ : Level} {D : Type ℓ} {ACM : AdditiveCommMonoid D}
         {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM

  _div'_ : D -> D -> Type ℓ
  a div' b = Σ[ c ∈ D ] (c * a == b)

  _div_ : D -> D -> Type ℓ
  a div b = ∃[ c ∈ D ] (c * a == b)


  isPropDiv : {a b : D} -> isProp (a div b)
  isPropDiv = squash


  div-trans : {d m n : D} -> d div m -> m div n -> d div n
  div-trans {d} = ∥-map2
    (\ (a , a*d=m) (b , b*m=n) ->
       (b * a) , (*-assoc >=> (*-right a*d=m) >=> b*m=n))

  div-reflᵉ : (d : D) -> d div d
  div-reflᵉ _ = ∣ 1# , *-left-one ∣

  div-refl : {d : D} -> d div d
  div-refl = ∣ 1# , *-left-one ∣

  div-one : {n : D} -> (1# div n)
  div-one {n} = ∣ n , *-right-one ∣

  div-zero : {n : D} -> (n div 0#)
  div-zero = ∣ 0# , *-left-zero ∣

  private
    div'-linear : {d a b : D} -> d div' a -> d div' b -> {m n : D} -> d div' (m * a + n * b)
    div'-linear {d} {a} {b} (d-div-a , pa) (d-div-b , pb) {m} {n} =
      (m * d-div-a + n * d-div-b) ,
      (*-distrib-+-right >=>
       +-cong (*-assoc >=> *-right pa) (*-assoc >=> *-right pb))

  div-linear : {d a b : D} -> d div a -> d div b -> {m n : D} -> d div (m * a + n * b)
  div-linear d%a d%b = ∥-map2 (\d%a d%b -> div'-linear d%a d%b) d%a d%b

  div-+ : {d n1 n2 : D} -> d div n1 -> d div n2 -> d div (n1 + n2)
  div-+ {d} d%n1 d%n2 = subst (d div_) (+-cong *-left-one *-left-one) (div-linear d%n1 d%n2)

  div-*ˡ : {d n : D} -> d div n -> (a : D) -> d div (a * n)
  div-*ˡ d%n a = ∥-map (\ (b , p) -> a * b , *-assoc >=> (cong (a *_) p)) d%n
  div-*ʳ : {d n : D} -> d div n -> (a : D) -> d div (n * a)
  div-*ʳ {d} d%n a = subst (d div_) *-commute (div-*ˡ d%n a)

  div-* : {d₁ d₂ n₁ n₂ : D} -> d₁ div n₁ -> d₂ div n₂ -> (d₁ * d₂) div (n₁ * n₂)
  div-* {d₁} {d₂} {n₁} {n₂} =
    ∥-map2 (\ (a₁ , p₁) (a₂ , p₂) -> a₁ * a₂ , *-swap >=> *-cong p₁ p₂)

  div-^ℕ : {k1 k2 : Nat} {d : D} -> k1 ≤ k2 -> (d ^ℕ k1) div (d ^ℕ k2)
  div-^ℕ {k1} {k2} {d} (i , path) = ∣ d ^ℕ i , path' ∣
    where
    path' : (d ^ℕ i) * (d ^ℕ k1) == (d ^ℕ k2)
    path' = sym (^ℕ-distrib-+-left i k1) >=> (cong (d ^ℕ_) path)
