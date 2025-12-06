{-# OPTIONS --cubical --safe --exact-split #-}

module relation.closure where

open import base

private
  variable
    ℓ ℓ₁ ℓ₂ : Level

data ReflexiveClosure {A : Type ℓ₁} (r : Rel A ℓ₂) : Rel A (ℓ-max ℓ₁ ℓ₂) where
  closure-rel : {a b : A} -> r a b -> ReflexiveClosure r a b
  closure-refl : {a : A} -> ReflexiveClosure r a a

data TransitiveReflexiveClosure {A : Type ℓ₁} (r : Rel A ℓ₂) : Rel A (ℓ-max ℓ₁ ℓ₂) where
  closure-rel : {a b : A} -> r a b -> TransitiveReflexiveClosure r a b
  closure-refl : {a : A} -> TransitiveReflexiveClosure r a a
  closure-trans : {a b c : A} ->
              TransitiveReflexiveClosure r a b ->
              TransitiveReflexiveClosure r b c ->
              TransitiveReflexiveClosure r a c

data SymmetricClosure {A : Type ℓ₁} (r : Rel A ℓ₂) : Rel A (ℓ-max ℓ₁ ℓ₂) where
  closure-rel : {a b : A} -> r a b -> SymmetricClosure r a b
  closure-sym : {a b : A} -> SymmetricClosure r a b -> SymmetricClosure r b a

data SymmetricReflexiveClosure {A : Type ℓ₁} (r : Rel A ℓ₂) : Rel A (ℓ-max ℓ₁ ℓ₂) where
  closure-rel : {a b : A} -> r a b -> SymmetricReflexiveClosure r a b
  closure-refl : {a : A} -> SymmetricReflexiveClosure r a a
  closure-sym : {a b : A} -> SymmetricReflexiveClosure r a b -> SymmetricReflexiveClosure r b a

data SymmetricTransitiveReflexiveClosure {A : Type ℓ₁} (r : Rel A ℓ₂) : Rel A (ℓ-max ℓ₁ ℓ₂) where
  closure-rel : {a b : A} -> r a b -> SymmetricTransitiveReflexiveClosure r a b
  closure-refl : {a : A} -> SymmetricTransitiveReflexiveClosure r a a
  closure-sym : {a b : A} -> SymmetricTransitiveReflexiveClosure r a b
                       -> SymmetricTransitiveReflexiveClosure r b a
  closure-trans : {a b c : A} ->
               SymmetricTransitiveReflexiveClosure r a b ->
               SymmetricTransitiveReflexiveClosure r b c ->
               SymmetricTransitiveReflexiveClosure r a c
