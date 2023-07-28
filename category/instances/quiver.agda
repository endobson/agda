{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

open import base
open import boolean
open import category.base
open import category.instances.set
open import equality
open import hlevel
open import relation

module category.instances.quiver where

data WalkingQuiverObj : Type ℓ-zero where
  wq-vertices : WalkingQuiverObj
  wq-edges : WalkingQuiverObj

data WalkingQuiverMor : WalkingQuiverObj -> WalkingQuiverObj -> Type ℓ-zero where
  wq-id : (p : WalkingQuiverObj) -> WalkingQuiverMor p p
  wq-source : WalkingQuiverMor wq-edges wq-vertices
  wq-target : WalkingQuiverMor wq-edges wq-vertices

private
  WalkingQuiverMor->Bool : ∀ {s t} -> WalkingQuiverMor s t -> Boolean
  WalkingQuiverMor->Bool (wq-id _) = true
  WalkingQuiverMor->Bool wq-source = true
  WalkingQuiverMor->Bool wq-target = false

Discrete-WalkingQuiverMor : ∀ {s t} -> Discrete (WalkingQuiverMor s t)
Discrete-WalkingQuiverMor {wq-vertices} {wq-vertices} (wq-id _) (wq-id _) = yes refl
Discrete-WalkingQuiverMor {wq-edges} {wq-edges} (wq-id _) (wq-id _) = (yes refl)
Discrete-WalkingQuiverMor wq-source wq-target =
  no (\st -> true!=false (cong WalkingQuiverMor->Bool st))
Discrete-WalkingQuiverMor wq-source wq-source = yes refl
Discrete-WalkingQuiverMor wq-target wq-source =
  no (\ts -> true!=false (cong WalkingQuiverMor->Bool (sym ts)))
Discrete-WalkingQuiverMor wq-target wq-target = yes refl

isSet-WalkingQuiverMor : ∀ {s t} -> isSet (WalkingQuiverMor s t)
isSet-WalkingQuiverMor = Discrete->isSet Discrete-WalkingQuiverMor

WalkingQuiverCat : PreCategory ℓ-zero ℓ-zero
WalkingQuiverCat = record
  { Obj = WalkingQuiverObj
  ; Mor = WalkingQuiverMor
  ; id = wq-id _
  ; _⋆_ = wq-compose
  ; ⋆-left-id = wq-left-id
  ; ⋆-right-id = wq-right-id
  ; ⋆-assoc = wq-assoc
  ; isSet-Mor = isSet-WalkingQuiverMor
  }
  where

  wq-compose : {a b c : WalkingQuiverObj} -> 
               WalkingQuiverMor a b -> WalkingQuiverMor b c -> WalkingQuiverMor a c
  wq-compose (wq-id _) f = f
  wq-compose wq-source (wq-id _) = wq-source
  wq-compose wq-target (wq-id _) = wq-target

  wq-left-id : {s t : WalkingQuiverObj} -> (f : WalkingQuiverMor s t) -> wq-compose (wq-id _) f == f
  wq-left-id _ = refl

  wq-right-id : {s t : WalkingQuiverObj} -> (f : WalkingQuiverMor s t) -> wq-compose f (wq-id _) == f
  wq-right-id (wq-id _) = refl
  wq-right-id wq-source = refl
  wq-right-id wq-target = refl

  wq-assoc : {s t u v : WalkingQuiverObj} -> 
             (f : WalkingQuiverMor s t) -> 
             (g : WalkingQuiverMor t u) -> 
             (h : WalkingQuiverMor u v) -> 
             wq-compose (wq-compose f g) h == wq-compose f (wq-compose g h)
  wq-assoc (wq-id _) _         _ = refl
  wq-assoc wq-source (wq-id _) _ = refl
  wq-assoc wq-target (wq-id _) _ = refl

Quiv : {ℓo ℓm : Level} -> (C : PreCategory ℓo ℓm) -> Type (ℓ-max ℓo ℓm)
Quiv C = Functor WalkingQuiverCat C

Quiver : (ℓ : Level) -> Type (ℓ-suc ℓ)
Quiver ℓ = Quiv (SetC ℓ)

