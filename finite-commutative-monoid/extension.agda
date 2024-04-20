{-# OPTIONS --cubical --safe --exact-split #-}

module finite-commutative-monoid.extension where

open import base
open import commutative-monoid
open import cubical
open import equality
open import equivalence.base
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.partition
open import finset
open import finset.detachable
open import finset.search
open import functions
open import functions.embedding
open import funext
open import hlevel
open import isomorphism
open import relation
open import subset
open import truncation

module _ {ℓD : Level} {D : Type ℓD} (CM : CommMonoid D) where
  open CommMonoid CM

  record isεExtension {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
                       (f : A -> D) (g : B -> D) : Type (ℓ-max* 3 ℓA ℓB ℓD) where
    field
      inc : A -> B
      isEmbed : isEmbedding inc
      agree : ∀ a -> f a == g (inc a)
      ε-others : ∀ b -> ¬ (fiber inc b) -> g b == ε

  module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
           {{FSA : FinSetStr A}} {{FSB : FinSetStr B}}
           {f : A -> D} {g : B -> D} where

    module _ (isExt : isεExtension f g) where
      private
        module isExt = isεExtension isExt
        h = isExt.inc

        ext-iso : Iso A (Σ B (fiber h))
        ext-iso .Iso.fun a = (h a) , a , refl
        ext-iso .Iso.inv (b , a , p) = a
        ext-iso .Iso.leftInv _ = refl
        ext-iso .Iso.rightInv (b , a , p) i = p i , a , (\j -> p (i ∧ j))

        isPropFib : ∀ b -> isProp (fiber h b)
        isPropFib = eqFun isEmbedding-eq-hasPropFibers isExt.isEmbed

        S : Subtype B _
        S = \b -> fiber h b , isPropFib b
        DetS : Detachable S
        DetS b = unsquash (isPropDec (isPropFib b)) ans2
          where
          P : Pred A _
          P a = h a == b

          DecP : Decidable P
          DecP a = isFinSet->Discrete isFinSetⁱ (h a) b

          ans1 : (∃ A P) ⊎ (∀ a -> ¬ (P a))
          ans1 = finite-search-dec (A , isFinSetⁱ) DecP

          ans2 : ∥ Dec (fiber h b) ∥
          ans2 = case ans1 of
            \{ (inj-l p) -> ∥-map yes p
             ; (inj-r ¬p) -> ∣ no (\(a , path) -> ¬p a path) ∣
             }

        open FinSetStr-DetachableInstances S DetS

        g₁ : Σ B (fiber h) -> D
        g₁ = g ∘ fst
        g₂ : Σ B (¬ ∘ fiber h) -> D
        g₂ = g ∘ fst

      opaque
        finiteMerge-extension : finiteMerge CM f == finiteMerge CM g
        finiteMerge-extension = step1 >=> sym ∙-right-ε >=> ∙-right (sym step2) >=> sym step3
          where
          step1 : finiteMerge CM f == finiteMerge CM g₁
          step1 = cong (finiteMerge CM) (funExt isExt.agree) >=>
                  sym (finiteMerge-convert-iso CM ext-iso g₁)
          step2 : finiteMerge CM g₂ == ε
          step2 = finiteMerge-ε CM (\ (b , ¬fib) -> isExt.ε-others b ¬fib)
          step3 : finiteMerge CM g == finiteMerge CM g₁ ∙ finiteMerge CM g₂
          step3 = finiteMerge-detachable CM S DetS g
