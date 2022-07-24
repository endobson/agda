{-# OPTIONS --cubical --safe --exact-split --guardedness #-}

module chain where

open import base
open import boolean
open import maybe
open import equality
open import functions
open import relation
open import sigma
open import truncation

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A : Type ℓ

BitStream : Type₀
BitStream = Nat -> Boolean

isCoNat : Pred BitStream ℓ-zero
isCoNat s = (∀ n -> (s n) == true -> (s (suc n) == true))

isCoNat' : Pred BitStream ℓ-zero
isCoNat' s = (∀ n -> (s (suc n)) == false -> (s n == false))

isCoNat->isCoNat' : (s : BitStream) -> isCoNat s -> isCoNat' s
isCoNat->isCoNat' s cnat n ssn=f = handle (s n) refl
  where
  handle : (b : Boolean) -> s n == b -> s n == false
  handle true p = bot-elim (true!=false (sym (cnat n p) >=> ssn=f))
  handle false p = p

CoNat : Type₀
CoNat = Σ BitStream isCoNat

co-zero : CoNat
co-zero = (\_ -> true) , (\_ _ -> refl)

co-infinity : CoNat
co-infinity = (\_ -> false) , (\_ f=t -> bot-elim (true!=false (sym f=t)))

co-suc : CoNat -> CoNat
co-suc (f , p) = f' , p'
  where
  f' : Nat -> Boolean
  f' zero = false
  f' (suc x) = f x

  p' : isCoNat f'
  p' zero f=t = bot-elim (true!=false (sym f=t))
  p' (suc n) = p n


co-pred : CoNat -> CoNat
co-pred (f , p) = f ∘ suc , \ n path -> p (suc n) path

nat<co-nat : Nat -> CoNat -> Type₀
nat<co-nat n (f , _) = f n == false

isFiniteCoNat : Pred CoNat ℓ-zero
isFiniteCoNat (f , _) = ∃[ n ∈ Nat ] (f n == true)

CoList : Type ℓ -> Type ℓ
CoList A = Σ[ b ∈ CoNat ] (∀ n -> nat<co-nat n b -> A)

ValidIndex : CoList A -> Nat -> Type _
ValidIndex (b , _) i = nat<co-nat i b

colist-length : CoList A -> CoNat
colist-length (b , f) = b

isFiniteCoList : Pred (CoList A) ℓ-zero
isFiniteCoList c = isFiniteCoNat (colist-length c)

colist-index : (c : CoList A) -> (n : Nat) -> ValidIndex c n -> A
colist-index (_ , f) n i = f n i

colist-cons : A -> CoList A -> CoList A
colist-cons {A = A} a (b , f) = b' , f'
  where
  b' = co-suc b
  f' : (n : Nat) -> nat<co-nat n b' -> A
  f' zero _ = a
  f' (suc n) i = f n i


colist-rest : CoList A -> CoList A
colist-rest {A = A} (b , f) = b' , f'
  where
  b' = co-pred b
  f' : (n : Nat) -> nat<co-nat n b' -> A
  f' n lt = f (suc n) lt


isAscChain : Rel A ℓ₁ -> Pred (CoList A) _
isAscChain R c = (n : Nat) -> (i1 : ValidIndex c n) -> (i2 : ValidIndex c (suc n)) ->
                              (R (colist-index c n i1) (colist-index c (suc n) i2))

isDescChain : Rel A ℓ₁ -> Pred (CoList A) _
isDescChain R c = (n : Nat) -> (i1 : ValidIndex c n) -> (i2 : ValidIndex c (suc n)) ->
                               (R (colist-index c (suc n) i2) (colist-index c n i1))
                          
isDescChain-colist-rest :
  (R : Rel A ℓ₁) -> (c : CoList A) -> isDescChain R c -> isDescChain R (colist-rest c)
isDescChain-colist-rest R c desc n = desc (suc n)

DescChainCondition : Rel A ℓ₁ -> Type _
DescChainCondition R = ∀ c -> isDescChain R c -> isFiniteCoList c


NonEmptyCoList : A -> Pred (CoList A) _
NonEmptyCoList x c = Σ[ i ∈ ValidIndex c zero ] (colist-index c zero i == x)


isFiniteCoList-colist-rest : (c : CoList A) -> isFiniteCoList (colist-rest c) -> isFiniteCoList c
isFiniteCoList-colist-rest c = ∥-map handle
  where
  handle : Σ[ n ∈ Nat ] (⟨ ⟨ colist-rest c ⟩ ⟩ n == true) ->
           Σ[ n ∈ Nat ] (⟨ ⟨ c ⟩ ⟩ n == true)
  handle (n , path) = (suc n , path)


WF->DCC : (R : Rel A ℓ₁) -> (∀ a -> Acc R a) -> DescChainCondition R
WF->DCC {A = A} R acc-f c@(b , f) desc = handle (⟨ b ⟩ zero) refl
  where
  handle : (v0 : Boolean) -> (⟨ b ⟩ zero == v0) -> isFiniteCoList c
  handle true bz=t = ∣ zero , bz=t ∣
  handle false bz=f = Acc->DCC (f zero bz=f) (acc-f (f zero bz=f)) c (bz=f , refl) desc
    where
    Acc->DCC : (a : A) -> Acc R a -> (c : CoList A) -> NonEmptyCoList a c -> 
                isDescChain R c -> isFiniteCoList c
    Acc->DCC a (acc acc-f) c@(b , f) (iz , fz=a) desc = handle2 (⟨ b ⟩ (suc zero)) refl 
      where
      handle2 : (v1 : Boolean) -> (⟨ b ⟩ (suc zero) == v1) -> isFiniteCoList c
      handle2 true bo=t = ∣ suc zero , bo=t ∣
      handle2 false bo=f = isFiniteCoList-colist-rest c rec
        where
        acc2 = acc-f (f (suc zero) bo=f) (subst2 R refl fz=a (desc zero iz bo=f))
        c2 = colist-rest c
        rec : isFiniteCoList c2
        rec = Acc->DCC (colist-index c (suc zero) bo=f) acc2 c2 
                       (bo=f , refl)
                       (isDescChain-colist-rest R c desc)
