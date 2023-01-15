{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.dirichlet.indicator where

open import additive-group
open import base
open import commutative-monoid
open import chapter2.dirichlet
open import chapter2.divisors
open import chapter2.mobius
open import chapter2.indicator
open import equality
open import equivalence
open import funext
open import functions
open import finset.instances
open import finset.instances.boolean
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import nat
open import order
open import fin
open import div
open import semiring
open import relation
open import semiring.instances.nat
open import subset
open import sigma.base
open import finite-commutative-monoid.partition

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
      finiteMerge-binary-partition CM (FinSet-Divisor n) partition g >=>
      cong2 _+_ p1 p2 >=>
      +-right-zero
      where

      D1 : Subtype (Divisor n) ℓ-zero
      D1 d = (⟨ d ⟩ == 1) , isSetNat _ _

      partition : BinaryPartition (Divisor n) ℓ-zero ℓ-zero
      partition = Detachable->BinaryPartition D1 (\d -> (decide-nat (fst d) 1))

      g : Divisor n -> D
      g d = Ind (divisor->nat⁺ n d) * f (divisor->nat⁺' n d)

      D1' : Type₀
      D1' = Σ[ d ∈ (Divisor n) ] (⟨ d ⟩ == 1)

      ¬D1' : Type₀
      ¬D1' = Σ[ d ∈ (Divisor n) ] (⟨ d ⟩ != 1)

      isContr-D1' : isContr D1'
      isContr-D1' =
        ((1 , ⟨ n ⟩ , *-right-one)  , refl) ,
        (\d2 -> ΣProp-path (isSetNat _ _) (ΣProp-path (isPropDiv' n) (sym (snd d2))))

      p1 : finiteMergeᵉ CM (D1' , _) (g ∘ fst) == f n
      p1 = finiteMerge-isContr CM {{FB = _}} isContr-D1' (g ∘ fst) >=>
           *-right (cong f (ΣProp-path isPropPos' refl)) >=>
           *-left-one

      p2' : Path (¬D1' -> D) (g ∘ fst) (\_ -> 0#)
      p2' = funExt p2'-paths
        where
        p2'-paths : (d : ¬D1') -> (g (fst d)) == 0#
        p2'-paths ((zero , 0|n) , ¬1) = bot-elim (div'-pos->pos 0|n (snd n))
        p2'-paths ((suc zero , _) , ¬1) = bot-elim (¬1 refl)
        p2'-paths ((suc (suc _) , _) , _) = *-left-zero

      p2 : finiteMergeᵉ CM (¬D1' , _) (g ∘ fst) == 0#
      p2 = cong (finiteMergeᵉ CM (¬D1' , _)) p2' >=>
           finiteMerge-ε CM {{FB = _}}
