{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.dirichlet.indicator where

open import additive-group
open import base
open import chapter2.dirichlet
open import chapter2.divisors
open import chapter2.indicator
open import chapter2.mobius
open import commutative-monoid
open import div
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.small
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.partition
open import finset
open import finset.detachable
open import finset.instances
open import finset.instances.boolean
open import functions
open import funext
open import nat
open import order
open import relation
open import semiring
open import semiring.instances.nat
open import sigma.base
open import subset

{-

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    module ACM = AdditiveCommMonoid ACM
    CM = ACM.comm-monoid
    module CM = CommMonoid CM
    instance
      IACM = ACM


  ⊗-left-id : {f : Nat⁺ -> D} -> Ind ⊗ f == f
  ⊗-left-id {f} = funExt paths
    where
    paths : (n : Nat⁺) -> (Ind ⊗ f) n == f n
    paths n =
      ⊗-eval >=>
      finiteMerge-detachable CM D1 Det-D1 g >=>
      cong2 _+_ p1 p2 >=>
      +-right-zero
      where

      instance
        FinSetStr-Divisor : FinSetStr (Divisor n)
        FinSetStr-Divisor = record { isFin = snd (FinSet-Divisor n) }

      D1 : Subtype (Divisor n) ℓ-zero
      D1 d = (⟨ d ⟩ == 1) , isSetNat _ _

      Det-D1 : Detachable D1
      Det-D1 d = (decide-nat (fst d) 1)

      open FinSetStr-DetachableInstances D1 Det-D1

      g : Divisor n -> D
      g d = Ind (divisor->nat⁺ n d) * f (divisor->nat⁺' n d)

      D1' : Type₀
      D1' = Σ[ d ∈ (Divisor n) ] (⟨ d ⟩ == 1)

      ¬D1' : Type₀
      ¬D1' = Σ[ d ∈ (Divisor n) ] (⟨ d ⟩ != 1)

      g₁ : D1' -> D
      g₁ (d , _) = g d

      g₂ : ¬D1' -> D
      g₂ (d , _) = g d

      isContr-D1' : isContr D1'
      isContr-D1' =
        ((1 , ⟨ n ⟩ , *-right-one)  , refl) ,
        (\d2 -> ΣProp-path (isSetNat _ _) (ΣProp-path (isPropDiv' n) (sym (snd d2))))

      p1 : finiteMerge CM g₁ == f n
      p1 = finiteMerge-isContr CM isContr-D1' g₁ >=>
           *-right (cong f (ΣProp-path isPropPos' refl)) >=>
           *-left-one

      p2'-paths : (d : ¬D1') -> g₂ d == 0#
      p2'-paths ((zero , 0|n) , ¬1) = bot-elim (div'-pos->pos 0|n (snd n))
      p2'-paths ((suc zero , _) , ¬1) = bot-elim (¬1 refl)
      p2'-paths ((suc (suc _) , _) , _) = *-left-zero

      p2 : finiteMerge CM g₂ == 0#
      p2 = finiteMerge-ε CM p2'-paths
-}
