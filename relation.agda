{-# OPTIONS --cubical --safe --exact-split #-}

module relation where

open import base

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B C : Type ℓ

-- Nullary Relations

data Dec (A : Type ℓ) : Type ℓ where
  yes :   A -> Dec A
  no  : ¬ A -> Dec A

Stable : Type ℓ -> Type ℓ
Stable A = (¬ (¬ A)) -> A

Dec->Stable : Dec A -> Stable A
Dec->Stable (yes a) ¬¬a = a
Dec->Stable (no ¬a) ¬¬a = bot-elim (¬¬a ¬a)

dec->⊎ : Dec A -> A ⊎ ¬ A
dec->⊎ (yes a) = inj-l a
dec->⊎ (no na) = inj-r na

Discrete : Type ℓ -> Type ℓ
Discrete A = (x y : A) -> Dec (x == y)

record Discrete' (A : Type ℓ) : Type ℓ where
  field
    f : Discrete A

-- Binary Relations

REL : (Type ℓ₁) -> (Type ℓ₂) -> (ℓ : Level) -> Type _
REL A B ℓ = A -> B -> Type ℓ

Rel : (Type ℓ₁) -> (ℓ : Level) -> Type _
Rel A ℓ = REL A A ℓ


Reflexive : Rel A ℓ -> Type _
Reflexive _~_ = ∀ {a} -> a ~ a

Irreflexive : Rel A ℓ -> Type _
Irreflexive _~_ = ∀ {a} -> ¬(a ~ a)

Symmetric : Rel A ℓ -> Type _
Symmetric _~_ = ∀ {a b} -> (a ~ b) -> (b ~ a)

Asymmetric : Rel A ℓ -> Type _
Asymmetric _~_ = ∀ {a b} -> (a ~ b) -> ¬ (b ~ a)

Antisymmetric : Rel A ℓ -> Type _
Antisymmetric _~_ = ∀ {a b} -> (a ~ b) -> (b ~ a) -> a == b

Transitive : Rel A ℓ -> Type _
Transitive _~_ = ∀ {a b c} -> (a ~ b) -> (b ~ c) -> (a ~ c)

HeteroConnex : REL A B ℓ₁ -> REL B A ℓ₂ -> Type _
HeteroConnex P Q = ∀ a b -> P a b ⊎ Q b a

Connex : Rel A ℓ -> Type _
Connex _~_ = HeteroConnex _~_ _~_

PartialOrder : Rel A ℓ -> Type _
PartialOrder _≤_ = (Transitive _≤_ × Reflexive _≤_ × Antisymmetric _≤_)

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

-- _⇒_ : REL A B ℓ₁ -> REL A B ℓ₂ -> Type _
-- P ⇒ Q = ∀ x y -> P x y -> Q x y
--
-- private
--   _on_ : (B -> B -> C) -> (A -> B) -> A -> A -> C
--   _*_ on f = (\ a b -> (f a) * (f b))
--
-- _=[_]⇒_ : Rel A ℓ₁ -> (A -> B) -> Rel B ℓ₂ -> Type _
-- P =[ f ]⇒ Q = P ⇒ (Q on f)
--
-- _Preserves_⇢_ : (A -> B) -> Rel A ℓ₁ -> Rel B ℓ₂ -> Type _
-- f Preserves P ⇢ Q = P =[ f ]⇒ Q

data Tri (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃) : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)) where
  tri< : (a  :   A) (¬b : ¬ B) (¬c : ¬ C) -> Tri A B C
  tri= : (¬a : ¬ A) (b  :   B) (¬c : ¬ C) -> Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) (c  :   C) -> Tri A B C

Trichotomous : Rel A ℓ₁ -> Type _
Trichotomous _<_ = ∀ x y -> Tri (x < y) (x == y) (y < x)


data WeakTri (A : Type ℓ₁) (B : Type ℓ₂) (C : Type ℓ₃) : Type (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃)) where
  weak-tri< : (a  :   A) (¬b : ¬ B) (¬c : ¬ C) -> WeakTri A B C
  weak-tri= :            (b  :   B)            -> WeakTri A B C
  weak-tri> : (¬a : ¬ A) (¬b : ¬ B) (c  :   C) -> WeakTri A B C

WeakTrichotomous : Rel A ℓ₁ -> Type _
WeakTrichotomous _<_ = ∀ x y -> WeakTri (x < y) (x == y) (y < x)



Decidable2 : Rel A ℓ -> Type _
Decidable2 _~_ = ∀ x y -> Dec (x ~ y)


-- Unary Relations

Pred :  Type ℓ₁ -> (ℓ₂ : Level) -> Type (ℓ-max ℓ₁ (ℓ-suc ℓ₂))
Pred A ℓ = A -> Type ℓ

∅ : Pred A _
∅ _ = Bot

U : Pred A _
U _ = Top

_⊆_ : Pred A ℓ₁ -> Pred A ℓ₂ -> Type _
P ⊆ Q = ∀ {a} -> P a -> Q a

_⊆'_ : Pred A ℓ₁ -> Pred A ℓ₂ -> Type _
P ⊆' Q = ∀ a -> P a -> Q a

_⇒_ : Pred A ℓ₁ -> Pred A ℓ₂ -> Pred A (ℓ-max ℓ₁ ℓ₂)
(P ⇒ Q) a = P a -> Q a

_∩_ : Pred A ℓ₁ -> Pred A ℓ₂ -> Pred A (ℓ-max ℓ₁ ℓ₂)
(P ∩ Q) a = P a × Q a

_∪_ : Pred A ℓ₁ -> Pred A ℓ₂ -> Pred A (ℓ-max ℓ₁ ℓ₂)
(P ∪ Q) a = P a ⊎ Q a


Comp : Pred A ℓ -> Pred A ℓ
Comp P x = ¬ (P x)

Decidable : Pred A ℓ -> Type _
Decidable P = ∀ x -> Dec (P x)


comp-dec : Dec A -> Dec (¬ A)
comp-dec (yes a) = no (\ na -> na a)
comp-dec (no na) = yes na

compDecidable : {P : Pred A ℓ} -> Decidable P -> Decidable (Comp P)
compDecidable {P = P} dec x = comp-dec (dec x)

Satisfiable : {A : Type ℓ₁} -> Pred A ℓ₂ -> Type (ℓ-max ℓ₁ ℓ₂)
Satisfiable {A = A} P = Σ A P

Universal : {A : Type ℓ₁} -> Pred A ℓ₂ -> Type (ℓ-max ℓ₁ ℓ₂)
Universal {A = A} P = (a : A) -> P a
