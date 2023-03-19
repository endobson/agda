{-# OPTIONS --cubical --safe --exact-split #-}

module sequence.permutation where

open import base
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid.maximum
open import finset.instances
open import finset.search
open import functions
open import hlevel
open import isomorphism
open import nat
open import order
open import order.instances.nat
open import order.minmax.instances.nat
open import relation
open import sequence
open import truncation
open import univalence

permute-seq : {ℓ : Level} {A : Type ℓ} -> Iso ℕ ℕ -> Sequence A -> Sequence A
permute-seq p s = s ∘ (Iso.fun p)

private
  isRawLowWaterMark : Iso ℕ ℕ -> ℕ -> Pred ℕ ℓ-zero
  isRawLowWaterMark p i j = ∀ k -> j ≤ k -> i ≤ (Iso.fun p k)

  isRawLowWaterMark' : Iso ℕ ℕ -> ℕ -> Pred ℕ ℓ-zero
  isRawLowWaterMark' p i j = ∀ k -> (Iso.fun p k) < i -> k < j

isLowWaterMark : Iso ℕ ℕ -> ℕ -> Pred ℕ ℓ-zero
isLowWaterMark p i j = isRawLowWaterMark p i j × isRawLowWaterMark' p i j

private
  isProp-isRawLowWaterMark : (p : Iso ℕ ℕ) (i j : ℕ) -> isProp (isRawLowWaterMark p i j)
  isProp-isRawLowWaterMark _ _ _ = (isPropΠ2 (\_ _ -> isProp-≤))

abstract
  isProp-isLowWaterMark : (p : Iso ℕ ℕ) (i j : ℕ) -> isProp (isLowWaterMark p i j)
  isProp-isLowWaterMark _ _ _ =
    isProp× (isPropΠ2 (\_ _ -> isProp-≤)) (isPropΠ2 (\_ _ -> isProp-≤))

private
  RawLowWaterMark-eq : (p : Iso ℕ ℕ) (i j : ℕ) -> isRawLowWaterMark p i j ≃ isLowWaterMark p i j
  RawLowWaterMark-eq p i j =
    (isoToEquiv (isProp->iso expand proj₁ (isProp-isRawLowWaterMark p i j)
                                          (isProp-isLowWaterMark p i j)))
    where
    expand : isRawLowWaterMark p i j -> isLowWaterMark p i j
    expand f = f , g
      where
      g : ∀ k -> (Iso.fun p k) < i -> k < j
      g k pk<i = stable-< (\k≮j -> convert-≤ (f k (convert-≮ k≮j)) pk<i)

private
  Decidable-isRawLowWaterMark : (p : Iso ℕ ℕ) (i : ℕ) -> Decidable (isRawLowWaterMark p i)
  Decidable-isRawLowWaterMark p i j = handle ansP
    where
    P : Pred (Fin i) ℓ-zero
    P (k , k<i) = j ≤ Iso.inv p k

    dec-P : Decidable P
    dec-P _ = decide-≤ _ _

    ansP : (Inhabited P) ⊎ (Universal (Comp P))
    ansP = finite-search-dec (FinSet-Fin i) dec-P

    handle : (Inhabited P) ⊎ (Universal (Comp P)) -> Dec (isRawLowWaterMark p i j)
    handle (inj-l ∃p) = unsquash (isPropDec (isProp-isRawLowWaterMark p i j))
                                 (∥-map handle2 ∃p)
      where
      handle2 : Σ (Fin i) P -> Dec (isRawLowWaterMark p i j)
      handle2 ((k , k<i) , j≤k') =
        no (\f -> irrefl-< (trans-<-≤ k<i (trans-≤-= (f k' j≤k') (Iso.rightInv p k))))
        where
        k' = Iso.inv p k
    handle (inj-r ∀¬p) = yes (\ k j≤k -> f k j≤k (split-< _ _))
      where
      f : ∀ k -> j ≤ k -> (Iso.fun p k < i) ⊎ (i ≤ Iso.fun p k) -> i ≤ (Iso.fun p k)
      f k j≤k (inj-r i≤k') = i≤k'
      f k j≤k (inj-l k'<i) = bot-elim (∀¬p (_ , k'<i) (trans-≤-= j≤k (sym (Iso.leftInv p k))))

abstract
  Decidable-isLowWaterMark : (p : Iso ℕ ℕ) (i : ℕ) -> Decidable (isLowWaterMark p i)
  Decidable-isLowWaterMark p i j =
    subst Dec (ua (RawLowWaterMark-eq p i j)) (Decidable-isRawLowWaterMark p i j)

  find-LowWaterMark : (p : Iso ℕ ℕ) -> (i : ℕ) -> Σ ℕ (isLowWaterMark p i)
  find-LowWaterMark p i = suc m , eqFun (RawLowWaterMark-eq p i (suc m)) (\j m<j -> g m<j (split-< _ _))
    where
    p' : Fin i -> ℕ
    p' (k , _) = Iso.inv p k
    m : ℕ
    m = finiteMax p'
    f : {k : ℕ} -> (k < i) -> Iso.inv p k ≤ m
    f {k} k<i = finiteMax-≤ p' (k , k<i)

    g : {j : ℕ} -> m < j -> (Iso.fun p j < i ⊎ i ≤ Iso.fun p j) -> i ≤ Iso.fun p j
    g m<j (inj-r i≤pj) = i≤pj
    g m<j (inj-l pj<i) =
      bot-elim (irrefl-< (trans-≤-< (trans-=-≤ (sym (Iso.leftInv p _)) (f pj<i)) m<j))
