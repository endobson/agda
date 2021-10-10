{-# OPTIONS --cubical --safe --exact-split #-}

module truncation where

open import base
open import equality
open import functions
open import hlevel
open import relation

private
  variable
    ℓ ℓ₀ ℓ₁ ℓ₂ : Level
    A B C D E : Type ℓ

data Squash (A : Type ℓ) : Type ℓ where
  ∣_∣ : A -> Squash A
  squash : (a b : Squash A) -> a == b

∥_∥ : Type ℓ -> Type ℓ
∥_∥ = Squash

unsquash : isProp A -> ∥ A ∥ -> A
unsquash h ∣ a ∣ = a
unsquash h (squash a b i) = h (unsquash h a) (unsquash h b) i

∥-map : (A -> B) -> ∥ A ∥ -> ∥ B ∥
∥-map f ∣ a ∣ = ∣ f a ∣
∥-map f (squash a1 a2 i) = (squash (∥-map f a1) (∥-map f a2) i)

∥-map2 : (A -> B -> C) -> ∥ A ∥ -> ∥ B ∥ -> ∥ C ∥
∥-map2 f ∣ a ∣ = ∥-map (f a)
∥-map2 f (squash a1 a2 i) b = (squash (∥-map2 f a1 b) (∥-map2 f a2 b) i)

∥-map3 : (A -> B -> C -> D) -> ∥ A ∥ -> ∥ B ∥ -> ∥ C ∥ -> ∥ D ∥
∥-map3 f ∣ a ∣ = ∥-map2 (f a)
∥-map3 f (squash a1 a2 i) b c = (squash (∥-map3 f a1 b c) (∥-map3 f a2 b c) i)

∥-map4 : (A -> B -> C -> D -> E) -> ∥ A ∥ -> ∥ B ∥ -> ∥ C ∥ -> ∥ D ∥ -> ∥ E ∥
∥-map4 f ∣ a ∣ = ∥-map3 (f a)
∥-map4 f (squash a1 a2 i) b c d = (squash (∥-map4 f a1 b c d) (∥-map4 f a2 b c d) i)

∥-bind : (A -> ∥ B ∥) -> ∥ A ∥ -> ∥ B ∥
∥-bind f ∣ a ∣ = f a
∥-bind f (squash a1 a2 i) = (squash (∥-bind f a1) (∥-bind f a2) i)

∥-bind2 : (A -> B -> ∥ C ∥) -> ∥ A ∥ -> ∥ B ∥ -> ∥ C ∥
∥-bind2 f a b = unsquash squash (∥-map2 f a b)

∥-bind3 : (A -> B -> C -> ∥ D ∥) -> ∥ A ∥ -> ∥ B ∥ -> ∥ C ∥ -> ∥ D ∥
∥-bind3 f a b c = unsquash squash (∥-map3 f a b c)

∥-bind4 : (A -> B -> C -> D -> ∥ E ∥) -> ∥ A ∥ -> ∥ B ∥ -> ∥ C ∥ -> ∥ D ∥ -> ∥ E ∥
∥-bind4 f a b c d = unsquash squash (∥-map4 f a b c d)


private
  module rec (BSet : isSet B) where
    ∥->Set       : (f : A -> B) (eq : 2-Constant f) -> ∥ A ∥ -> B
    ∥->SetHelper : (f : A -> B) (eq : 2-Constant f) (x y : ∥ A ∥) -> ∥->Set f eq x == ∥->Set f eq y

    ∥->Set f _  ∣ x ∣          = f x
    ∥->Set f eq (squash x y i) = ∥->SetHelper f eq x y i
    ∥->SetHelper f eq (squash x1 x2 i) y =
      isSet->Squareᵉ BSet
        (∥->SetHelper f eq x1 y)
        (∥->SetHelper f eq x2 y)
        (∥->SetHelper f eq x1 x2)
        refl
        i
    ∥->SetHelper f eq x@(∣ _ ∣) (squash y1 y2 i) =
      isSet->Squareᵉ BSet
        (∥->SetHelper f eq x y1)
        (∥->SetHelper f eq x y2)
        refl
        (∥->SetHelper f eq y1 y2)
        i
    ∥->SetHelper f eq ∣ x ∣ ∣ y ∣ = eq x y

open rec public using (∥->Set)

-- Mere existence

∃ : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃ A B = ∥ Σ A B ∥

infix 2 ∃-syntax

∃-syntax : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃-syntax = ∃

syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B

∃! : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃! A B = isContr (Σ A B)

∃!-syntax : (A : Type ℓ₀) -> (B : A -> Type ℓ₁) -> Type (ℓ-max ℓ₀ ℓ₁)
∃!-syntax = ∃!

syntax ∃!-syntax A (λ x → B) = ∃![ x ∈ A ] B

∃!-val : {A : Type ℓ₀} {B : A -> Type ℓ₁} -> ∃! A B -> A
∃!-val = fst ∘ fst

∃!-prop : {A : Type ℓ₀} {B : A -> Type ℓ₁} -> (p : ∃! A B) -> B (∃!-val p)
∃!-prop = snd ∘ fst


Inhabited : {A : Type ℓ₀} -> Pred A ℓ₁ -> Type (ℓ-max ℓ₀ ℓ₁)
Inhabited {A = A} P = ∃ A P

Comparison : Rel A ℓ -> Type _
Comparison {A = A} _~_ = (a b c : A) -> a ~ c -> ∥ (a ~ b) ⊎ (b ~ c) ∥

Dense : {ℓ ℓA : Level} {A : Type ℓA} -> Rel A ℓ -> Type (ℓ-max ℓA ℓ)
Dense {A = A} _<_ = {x y : A} -> x < y -> ∃[ z ∈ A ] (x < z × z < y)

HeteroConnex : REL A B ℓ₁ -> REL B A ℓ₂ -> Type _
HeteroConnex P Q = ∀ a b -> ∥ P a b ⊎ Q b a ∥

Connex : Rel A ℓ -> Type _
Connex _~_ = HeteroConnex _~_ _~_

TotalOrder : Rel A ℓ -> Type _
TotalOrder _≤_ = (Transitive _≤_ × Connex _≤_ × Antisymmetric _≤_)

module _ {_≤_ : Rel A ℓ} where
  private
    _≥_ : Rel A ℓ
    x ≥ y = y ≤ x
  flip-total-order : TotalOrder _≤_ -> TotalOrder _≥_
  flip-total-order (trans , connex , antisym) = (trans' , connex' , antisym')
    where
    trans' : Transitive _≥_
    trans' x y   = trans y x
    connex' : Connex _≥_
    connex' x y  = connex y x
    antisym' : Antisymmetric _≥_
    antisym' x y = antisym y x


Apartness : Rel A ℓ -> Type _
Apartness _#_ = (Irreflexive _#_ × Symmetric _#_ × Comparison _#_)

TightApartness : Rel A ℓ -> Type _
TightApartness _#_ = (Tight _#_ × Apartness _#_)
