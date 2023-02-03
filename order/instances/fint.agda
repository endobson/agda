{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.fint where

open import base
open import fin-algebra
open import functions
open import hlevel.base
open import order
open import relation
open import sum
open import truncation

data FinT< : {n : Nat} -> (FinT n) -> (FinT n) -> Type ℓ-zero where
  finT<-lr : {n : Nat} {j : FinT n}   ->              FinT< (inj-l tt) (inj-r j)
  finT<-rr : {n : Nat} {i j : FinT n} -> FinT< i j -> FinT< (inj-r i) (inj-r j)

private
  abstract
    isProp-FinT< : {n : Nat} {i j : FinT n} -> isProp (FinT< i j)
    isProp-FinT< finT<-lr finT<-lr = refl
    isProp-FinT< (finT<-rr lt1) (finT<-rr lt2) i =
      finT<-rr (isProp-FinT< lt1 lt2 i)


    irrefl-FinT< : {n : Nat} -> Irreflexive (FinT< {n})
    irrefl-FinT< (finT<-rr lt) = irrefl-FinT< lt

    trans-FinT< : {n : Nat} -> Transitive (FinT< {n})
    trans-FinT< (finT<-lr) (finT<-rr _) = finT<-lr
    trans-FinT< (finT<-rr lt1) (finT<-rr lt2) = finT<-rr (trans-FinT< lt1 lt2)

    connected-FinT< : {n : Nat} -> Connected (FinT< {n})
    connected-FinT< {suc n} {inj-l _} {inj-l _} _ _ = refl
    connected-FinT< {suc n} {inj-l _} {inj-r _} f _ = bot-elim (f finT<-lr)
    connected-FinT< {suc n} {inj-r _} {inj-l _} _ g = bot-elim (g finT<-lr)
    connected-FinT< {suc n} {inj-r _} {inj-r _} f g i =
      inj-r (connected-FinT< (f ∘ finT<-rr) (g ∘ finT<-rr) i)

    comparison-FinT< : {n : Nat} -> Comparison (FinT< {n})
    comparison-FinT< {suc n} _         (inj-l b) _         (finT<-lr)    = ∣ inj-r finT<-lr ∣
    comparison-FinT< {suc n} _         (inj-r b) _         (finT<-lr)    = ∣ inj-l finT<-lr ∣
    comparison-FinT< {suc n} _         (inj-l b) _         (finT<-rr _)  = ∣ inj-r finT<-lr ∣
    comparison-FinT< {suc n} (inj-r a) (inj-r b) (inj-r c) (finT<-rr a<c) =
      ∥-map (⊎-map finT<-rr finT<-rr) (comparison-FinT< a b c a<c)

instance
  LinearOrderStr-FinT : {n : Nat} -> LinearOrderStr (FinT n) ℓ-zero
  LinearOrderStr-FinT {n} = record
    { _<_ = FinT<
    ; isProp-< = isProp-FinT<
    ; irrefl-< = irrefl-FinT<
    ; trans-< = trans-FinT<
    ; connected-< = connected-FinT<
    ; comparison-< = comparison-FinT<
    }
