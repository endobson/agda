{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

open import base
open import boolean
open import category.base
open import category.functor
open import category.instances.set
open import discrete
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

ΣQuiver : {ℓ : Level} -> (V : hSet ℓ) -> (E : ⟨ V ⟩ -> ⟨ V ⟩ -> hSet ℓ) -> Quiver ℓ
ΣQuiver V E .Functor.obj wq-vertices = V
ΣQuiver V E .Functor.obj wq-edges =
  (Σ[ v1 ∈ ⟨ V ⟩ ] Σ[ v2 ∈ ⟨ V ⟩ ] ⟨ E v1 v2 ⟩) ,
  isSetΣ (snd V) (\v1 -> isSetΣ (snd V) (\v2 -> (snd (E v1 v2))))
ΣQuiver V E .Functor.mor (wq-id _) = set-function (\x -> x)
ΣQuiver V E .Functor.mor wq-source = set-function (\ (s , t , e) -> s)
ΣQuiver V E .Functor.mor wq-target = set-function (\ (s , t , e) -> t)
ΣQuiver V E .Functor.id _ = refl
ΣQuiver V E .Functor.⋆ (wq-id _) _         = refl
ΣQuiver V E .Functor.⋆ wq-source (wq-id _) = refl
ΣQuiver V E .Functor.⋆ wq-target (wq-id _) = refl

cons-Quiver : {ℓ : Level} -> (V : hSet ℓ) -> (E : hSet ℓ) -> (s t : ⟨ E ⟩ -> ⟨ V ⟩) -> Quiver ℓ
cons-Quiver V E s t .Functor.obj wq-vertices = V
cons-Quiver V E s t .Functor.obj wq-edges = E
cons-Quiver V E s t .Functor.mor (wq-id _) = set-function (\x -> x)
cons-Quiver V E s t .Functor.mor wq-source = set-function s
cons-Quiver V E s t .Functor.mor wq-target = set-function t
cons-Quiver V E s t .Functor.id _ = refl
cons-Quiver V E s t .Functor.⋆ (wq-id _) _         = refl
cons-Quiver V E s t .Functor.⋆ wq-source (wq-id _) = refl
cons-Quiver V E s t .Functor.⋆ wq-target (wq-id _) = refl
