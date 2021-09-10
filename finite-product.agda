{-# OPTIONS --cubical --safe --exact-split #-}

module finite-product where

open import base
open import cubical
open import equality
open import commutative-monoid
open import commutative-monoid.pi
open import functions
open import equivalence
open import isomorphism
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finsum
open import finset.instances
open import fin
open import semiring
open import maybe

private
  variable
    ℓ : Level
    A : Type ℓ


private
  module _ {ℓD : Level} {D : Type ℓD} {{S : Semiring D}} where
    finiteProductᵉ : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
    finiteProductᵉ = finiteMerge *-CommMonoid

module _ {ℓD : Level} {D : Type ℓD} {{S : Semiring D}} where
  private
    CM = *-CommMonoid

  finProductDep : (n : Nat) -> (f : (Fin n) -> D) -> D
  finProductDep = finMergeDep CM

  enumerationProduct : {n : Nat} -> (Fin n -> A) -> (A -> D) -> D
  enumerationProduct = enumerationMerge CM

  equivProduct : {n : Nat} -> (A ≃ Fin n) -> (A -> D)  -> D
  equivProduct = equivMerge CM

  abstract
    finiteProduct : {ℓ : Level} -> (s : FinSet ℓ) -> (⟨ s ⟩ -> D) -> D
    finiteProduct = finiteProductᵉ

    finiteProductᵉ-path : {ℓ : Level} -> {s : FinSet ℓ} -> {f : ⟨ s ⟩ -> D} ->
                          finiteProduct s f == finiteProductᵉ s f
    finiteProductᵉ-path = refl

    finiteProduct-eval : {ℓ : Level} (A : FinSet ℓ) {n : Nat}
                         -> (eq : (⟨ A ⟩ ≃ Fin n)) -> (f : ⟨ A ⟩ -> D)
                         -> finiteProduct A f == equivProduct eq f
    finiteProduct-eval = finiteMerge-eval CM

    finiteProduct-convert : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                            (eq : (⟨ B ⟩ ≃ ⟨ A ⟩) ) (f : ⟨ A ⟩ -> D)
                            -> finiteProduct A f == finiteProduct B (f ∘ (eqFun eq))
    finiteProduct-convert = finiteMerge-convert CM

    finiteProduct-convert-iso : {ℓ₁ ℓ₂ : Level} -> (A : FinSet ℓ₁) (B : FinSet ℓ₂)
                                (i : Iso ⟨ B ⟩ ⟨ A ⟩) (f : ⟨ A ⟩ -> D)
                                -> finiteProduct A f == finiteProduct B (f ∘ (Iso.fun i))
    finiteProduct-convert-iso = finiteMerge-convert-iso CM

    finiteProduct-Bot : (f : Bot -> D) -> finiteProduct FinSet-Bot f == 1#
    finiteProduct-Bot = finiteMerge-Bot CM

    finiteProduct-Top : (f : Top -> D) -> finiteProduct FinSet-Top f == f tt
    finiteProduct-Top = finiteMerge-Top CM

    finiteProduct-Maybe :
      (FB : FinSet ℓ) (f : Maybe ⟨ FB ⟩ -> D) ->
      finiteProduct (FinSet-Maybe FB) f ==
      (f nothing) * (finiteProduct FB (f ∘ just))
    finiteProduct-Maybe = finiteMerge-Maybe CM

    finiteProduct-⊎ :
      (FA : FinSet ℓ) (FB : FinSet ℓ) (f : (⟨ FA ⟩ ⊎ ⟨ FB ⟩) -> D) ->
      finiteProduct (FinSet-⊎ FA FB) f ==
      (finiteProduct FA (f ∘ inj-l)) * (finiteProduct FB (f ∘ inj-r))
    finiteProduct-⊎ FA FB = finiteMerge-⊎ CM (snd FA) (snd FB)

    finiteProduct-split :
      (FB : FinSet ℓ) {f g : ⟨ FB ⟩ -> D} ->
      finiteProduct FB (\b -> f b * g b) ==
      finiteProduct FB f * finiteProduct FB g
    finiteProduct-split FB = finiteMerge-split CM FB

    finiteProductʰ : (FB : FinSet ℓ) -> CommMonoidʰᵉ (CommMonoidStr-Π (\_ -> CM)) CM (finiteProduct FB)
    finiteProductʰ FB = finiteMergeʰ CM FB


module _ {ℓB ℓC : Level} {B : Type ℓB} {C : Type ℓC} {{SB : Semiring B}} {{SC : Semiring C}} where
  private
    module SB = Semiring SB
    module SC = Semiring SC
    CM-B = SB.*-CommMonoid
    CM-C = SC.*-CommMonoid

  abstract
    finiteProduct-homo-inject :
      (FA : FinSet ℓ) {f : B -> C} (fʰ : (CommMonoidʰᵉ CM-B CM-C f)) {g : ⟨ FA ⟩ -> B} ->
      finiteProduct FA (f ∘ g) == f (finiteProduct FA g)
    finiteProduct-homo-inject FA {f = f} fʰ =
      finiteProductᵉ-path >=>
      finiteMerge-homo-inject CM-C FA CM-B fʰ >=>
      cong f (sym finiteProductᵉ-path)
