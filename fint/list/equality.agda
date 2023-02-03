{-# OPTIONS --cubical --safe --exact-split #-}

module fint.list.equality where

open import base
open import equality
open import fin-algebra
open import fint.list
open import fint.same-index
open import functions
open import funext
open import nat
open import sum


abstract
  element-paths->fin-list-path :
    {ℓ : Level} {A : Type ℓ} {n1 n2  : Nat} {f1 : FinT n1 -> A} {f2 : FinT n2 -> A} ->
    n1 == n2 ->
    (∀ (i : FinT n1) (j : FinT n2) -> SameIndex i j -> f1 i == f2 j) ->
    Path (FinList A) (n1 , f1) (n2 , f2)
  element-paths->fin-list-path {A = A} {n1} {n2} {f1} {f2} np fp =
    rec _ _ _ _ np fp
    where
    rec : (n1 n2 : Nat) (f1 : FinT n1 -> A) (f2 : FinT n2 -> A) ->
          n1 == n2 ->
          (∀ (i : FinT n1) (j : FinT n2) -> SameIndex i j -> f1 i == f2 j) ->
          Path (FinList A) (n1 , f1) (n2 , f2)
    rec zero zero f1 f2 _ _ = \i -> zero , f1=f2 i
      where
      f1=f2 : f1 == f2
      f1=f2 = funExt (\())
    rec (suc n1) (suc n2) f1 f2 np fp = ans
      where
      fp' : (i : FinT n1) (j : FinT n2) -> SameIndex i j -> f1 (inj-r i) == f2 (inj-r j)
      fp' i j s = fp (inj-r i) (inj-r j) s

      rec-ans : Path (FinList A) (n1 , (f1 ∘ inj-r)) (n2 , (f2 ∘ inj-r))
      rec-ans = rec n1 n2 (f1 ∘ inj-r) (f2 ∘ inj-r) (cong pred np) fp'

      elem-p : Path A (f1 (inj-l tt)) (f2 (inj-l tt))
      elem-p = fp _ _ tt

      ans' : Path (FinList A) (suc n1 , either (f1 ∘ inj-l) (f1 ∘ inj-r))
                              (suc n2 , either (f2 ∘ inj-l) (f2 ∘ inj-r))
      ans' i = suc (fst (rec-ans i)) , either (\tt -> elem-p i) (snd (rec-ans i))

      expand : {n : Nat} -> (f : FinT (suc n) -> A) -> f == either (f ∘ inj-l) (f ∘ inj-r)
      expand f = funExt (\{ (inj-l _) -> refl ; (inj-r _) -> refl })

      ans : Path (FinList A) (suc n1 , f1) (suc n2 , f2)
      ans = (\i -> suc n1 , (expand f1 i)) >=> ans' >=> (\i -> (suc n2 , (expand f2 (~ i))))
    rec zero (suc i) f1 f2 np _ = zero-suc-absurd np
    rec (suc i) zero f1 f2 np _ = zero-suc-absurd (sym np)

  element-paths->vector-path :
    {ℓ : Level} {A : Type ℓ} {n1 n2  : Nat} {f1 : FinT n1 -> A} {f2 : FinT n2 -> A} ->
    (np : n1 == n2) ->
    (∀ (i : FinT n1) (j : FinT n2) -> SameIndex i j -> f1 i == f2 j) ->
    PathP (\i -> FinT (np i) -> A) f1 f2
  element-paths->vector-path {A = A} {n1} {n2} {f1} {f2} np ep =
    subst (\np -> PathP (\i -> FinT (np i) -> A) f1 f2) np'=np fp'
    where
    lp : Path (FinList A) (n1 , f1) (n2 , f2)
    lp = element-paths->fin-list-path np ep

    np' : n1 == n2
    np' i = fst (lp i)

    np'=np : np' == np
    np'=np = isSetNat _ _ _ _

    fp' : PathP (\i -> FinT (np' i) -> A) f1 f2
    fp' i = snd (lp i)
