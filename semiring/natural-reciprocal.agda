{-# OPTIONS --cubical --safe --exact-split #-}

module semiring.natural-reciprocal where

open import additive-group
open import base
open import equality-path
open import functions
open import hlevel.base
open import nat
open import semiring
open import semiring.initial
open import sigma.base
open import truncation


module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D}
         {S : Semiring ACM} (Inc : ℕ->SemiringStr S) where
  private
    instance
      IACM = ACM
      IS = S
      I-Inc = Inc

  record 1/ℕ-Str : Type ℓD where
    field
      f : Nat⁺ -> D
      path : ∀ (n⁺@(n , _) : Nat⁺) -> (ℕ->Semiring n) * f n⁺ == 1#

module _ {ℓD : Level} (D : Type ℓD) {ACM : AdditiveCommMonoid D}
         {{_ : Semiring ACM}} {{Inc : ℕ->Semiring-Op D}} where
  1/ℕ-Op : Type ℓD
  1/ℕ-Op = 1/ℕ-Str Inc



module _ {ℓD : Level} {D : Type ℓD} {{ACM : AdditiveCommMonoid D}}
         {{_ : Semiring ACM}}
         {{_ : ℕ->Semiring-Op D}}
         {{O : 1/ℕ-Op D}}
         where

  1/ℕ : Nat⁺ -> D
  1/ℕ = 1/ℕ-Str.f O
  ℕ-1/ℕ-path : ∀ (n⁺@(n , _) : Nat⁺) -> (ℕ->Semiring n) * 1/ℕ n⁺ == 1#
  ℕ-1/ℕ-path = 1/ℕ-Str.path O

  1/ℕ-ℕ-path : ∀ (n⁺@(n , _) : Nat⁺) -> 1/ℕ n⁺ * (ℕ->Semiring n) == 1#
  1/ℕ-ℕ-path n⁺ = *-commute >=> (1/ℕ-Str.path O n⁺)

  ∃!1/ℕ : (n : Nat⁺) -> ∃![ d ∈ D ] (ℕ->Semiring ⟨ n ⟩ * d == 1#)
  ∃!1/ℕ n = (1/ℕ n , ℕ-1/ℕ-path n) , isProp-path _
    where
    opaque
      isProp-path : isProp (Σ[ d ∈ D ] (ℕ->Semiring ⟨ n ⟩ * d == 1#))
      isProp-path (d1 , p1) (d2 , p2) =
        ΣProp-path (AdditiveCommMonoid.isSet-Domain ACM  _ _) p
        where
        p : d1 == d2
        p = sym (*-left-one) >=>
            (cong (_* d1) (sym p2 >=> *-commute)) >=>
            *-assoc >=> *-commute >=>
            (cong (_* d2) p1) >=> *-left-one

  1/2 : D
  1/2 = 1/ℕ 2⁺

  opaque
    1/1-path : 1/ℕ 1⁺ == 1#
    1/1-path = sym *-left-one >=>
               *-left (sym ℕ->Semiring-preserves-1#) >=>
               ℕ-1/ℕ-path 1⁺

    +-/2-path : {x : D} -> (x * 1/2) + (x * 1/2) == x
    +-/2-path =
      sym 2*-path >=>
      *-commute >=> *-assoc >=>
      *-right (*-right (sym ℕ->Semiring-preserves-2#) >=> 1/ℕ-ℕ-path 2⁺) >=>
      *-right-one

    2/2-path : 2# * 1/2 == 1#
    2/2-path =
      *-left (sym ℕ->Semiring-preserves-2#) >=>
      ℕ-1/ℕ-path 2⁺

    +-1/2-path : 1/2 + 1/2 == 1#
    +-1/2-path = sym 2*-path >=> 2/2-path

    1/ℕ-distrib-* : (a b : Nat⁺) -> 1/ℕ ( a *⁺ b ) == 1/ℕ a * 1/ℕ b
    1/ℕ-distrib-* a b = ∃!-unique (∃!1/ℕ (a *⁺ b)) (1/ℕ a * 1/ℕ b) path
      where
      path : ℕ->Semiring (⟨ a *⁺ b ⟩) * (1/ℕ a * 1/ℕ b) == 1#
      path = *-left (Semiringʰ.preserves-* ℕ->Semiringʰ ⟨ a ⟩ ⟨ b ⟩) >=>
             *-swap >=>
             *-cong (ℕ-1/ℕ-path a) (ℕ-1/ℕ-path b) >=>
             *-right-one

module _ {ℓD₁ ℓD₂ : Level} {D₁ : Type ℓD₁} {D₂ : Type ℓD₂}
         {{ACM₁ : AdditiveCommMonoid D₁}} {{S₁ : Semiring ACM₁}}
         {{_ : ℕ->Semiring-Op D₁}}
         {{_ : 1/ℕ-Op D₁}}
         {{ACM₂ : AdditiveCommMonoid D₂}} {{S₂ : Semiring ACM₂}}
         {{_ : ℕ->Semiring-Op D₂}}
         {{_ : 1/ℕ-Op D₂}}
         where
  Semiringʰ-preserves-1/ℕ : {f : D₁ -> D₂} ->
    Semiringʰ f -> (n : Nat⁺) -> f (1/ℕ n) == 1/ℕ n
  Semiringʰ-preserves-1/ℕ {f} h n@(n' , _) = sym (∃!-unique (∃!1/ℕ n) (f (1/ℕ n)) path2)
    where
    path1 : ℕ->Semiring == f ∘ ℕ->Semiring
    path1 = ∃!-unique ∃!ℕ->Semiring (f ∘ ℕ->Semiring) (Semiringʰ-∘ h (∃!-prop ∃!ℕ->Semiring))
    path2 : ℕ->Semiring n' * (f (1/ℕ n)) == 1#
    path2 = *-left (\i -> path1 i n') >=>
            sym (Semiringʰ.preserves-* h _ _) >=>
            cong f (∃!-prop (∃!1/ℕ n)) >=>
            (Semiringʰ.preserves-1# h)
