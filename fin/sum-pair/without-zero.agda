{-# OPTIONS --cubical --safe --exact-split #-}

module fin.sum-pair.without-zero where

open import base
open import equality
open import fin.sum-pair
open import hlevel
open import isomorphism
open import nat
open import sigma.base
open import without-point

fin-pair+-suc₁' : {n : Nat} -> FinPair+ n -> WithoutPoint (FinPair+ (suc n)) fin-pair+-zero₁
fin-pair+-suc₁' p = fin-pair+-suc₁ p , \ q -> zero-suc-absurd (cong FinPair+.i (sym q))

fin-pair+-suc₁-Iso : {n : Nat} -> Iso (FinPair+ n) (WithoutPoint (FinPair+ (suc n)) fin-pair+-zero₁)
fin-pair+-suc₁-Iso {n} .Iso.fun = fin-pair+-suc₁'
fin-pair+-suc₁-Iso {n} .Iso.inv (fin-pair+ zero j p , ¬path) =
  bot-elim (¬path (FinPair+-path refl p))
fin-pair+-suc₁-Iso {n} .Iso.inv (fin-pair+ (suc i) j p , _) =
  (fin-pair+ i j (cong pred p))
fin-pair+-suc₁-Iso {n} .Iso.rightInv (fin-pair+ zero j p , ¬path) =
  bot-elim (¬path (FinPair+-path refl p))
fin-pair+-suc₁-Iso {n} .Iso.rightInv (fin-pair+ (suc i) j p , _) =
  WithoutPoint-path (FinPair+-path refl refl)
fin-pair+-suc₁-Iso {n} .Iso.leftInv (fin-pair+ i j p) = FinPair+-path refl refl
