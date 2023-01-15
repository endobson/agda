{-# OPTIONS --cubical --safe --exact-split #-}

module new-permutation where

open import base
open import equality
open import equivalence
open import fin
open import fin.functions
open import functions
open import isomorphism
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import pigeonhole
open import relation
open import sigma.base

open Iso

Perm : Nat -> Type₀
Perm n = Auto (Fin n)

-- Identity permutation
idPerm : {n : Nat} -> Perm n
idPerm = id-iso

-- Permutation that holds 'zero-fin' constant and acts like the shifted argument otherwise

module _ where
  private
    suc-fin-f : {n : Nat} -> (Fin n -> Fin n) -> (Fin (suc n) -> Fin (suc n))
    suc-fin-f f (zero  , lt) = (zero , lt)
    suc-fin-f f (suc i , lt) = (suc-fin ∘ f) (i , pred-≤ lt)

    abstract
      suc-fin-f-compose-path : {n : Nat} (f : Fin n -> Fin n) ->
        (suc-fin-f f ∘ suc-fin) == (suc-fin ∘ f)
      suc-fin-f-compose-path f k (i , p) = path k
        where
        lemma : (suc (Fin.i (f (i , pred-≤ (suc-≤ p))))) == suc (Fin.i (f (i , p)))
        lemma k = (suc (Fin.i (f (i , isProp-≤ (pred-≤ (suc-≤ p)) p k))))

        path : (suc-fin-f f ∘ suc-fin) (i , p) == (suc-fin ∘ f) (i , p)
        path = fin-i-path lemma

      suc-fin-f-double-compose-path : {n : Nat} (f : Fin n -> Fin n) (g : Fin n -> Fin n) ->
        (suc-fin-f f ∘ suc-fin-f g ∘ suc-fin) == (suc-fin ∘ f ∘ g)
      suc-fin-f-double-compose-path f g =
        cong (suc-fin-f f ∘_) (suc-fin-f-compose-path g)
        >=> cong (_∘ g) (suc-fin-f-compose-path f)

      fin-fun-eq-split-zero : {ℓ : Level} {A : Type ℓ} {n : Nat} {f g : Fin (suc n) -> A}
                              -> (f zero-fin) == (g zero-fin)
                              -> (f ∘ suc-fin) == (g ∘ suc-fin)
                              -> f == g
      fin-fun-eq-split-zero {f = f} {g = g} zp sp i (zero , p) =
        ((cong f path) ∙∙ zp ∙∙ (cong g (sym path))) i
        where
        path : (zero , p) == zero-fin
        path = fin-i-path refl
      fin-fun-eq-split-zero {f = f} {g = g} zp sp i (suc j , p) =
        ((cong f path) ∙∙ (\i -> sp i (j , (pred-≤ p))) ∙∙ (cong g (sym path))) i

        where
        path : (suc j , p) == suc-fin (j , (pred-≤ p))
        path = fin-i-path refl

      sucPerm-rightInv : {n : Nat} (φ : Perm n)
                         -> suc-fin-f (φ .fun) ∘ suc-fin-f (φ .inv) == idfun (Fin (suc n))
      sucPerm-rightInv φ = fin-fun-eq-split-zero refl lemma
        where
        lemma : suc-fin-f (φ .fun) ∘ suc-fin-f (φ .inv) ∘ suc-fin == suc-fin
        lemma = (suc-fin-f-double-compose-path (φ .fun) (φ .inv))
                >=> (cong (suc-fin ∘_) (\i a -> φ .rightInv a i))
      sucPerm-leftInv : {n : Nat} (φ : Perm n)
                         -> suc-fin-f (φ .inv) ∘ suc-fin-f (φ .fun) == idfun (Fin (suc n))
      sucPerm-leftInv φ = fin-fun-eq-split-zero refl lemma
        where
        lemma : suc-fin-f (φ .inv) ∘ suc-fin-f (φ .fun) ∘ suc-fin == suc-fin
        lemma = (suc-fin-f-double-compose-path (φ .inv) (φ .fun))
                >=> (cong (suc-fin ∘_) (\i a -> φ .leftInv a i))

  sucPerm : {n : Nat} -> Perm n -> Perm (suc n)
  sucPerm φ .fun = suc-fin-f (φ .fun)
  sucPerm φ .inv = suc-fin-f (φ .inv)
  sucPerm φ .rightInv s i = sucPerm-rightInv φ i s
  sucPerm φ .leftInv  s i = sucPerm-leftInv φ i s


-- Append two permutations

module _ {m n : Nat} where
  private
    abstract
      embed-inc : Fin m -> Fin (m +' n)
      embed-inc (i , p) = (i , lemma)
        where
        lemma : i < (m +' n)
        lemma = trans-<-≤ p (transport (\k -> (+'-commute {m} {0} k) ≤ (m +' n))
                                       (+-left-≤⁺ m zero-≤))

      embed-suc : Fin n -> Fin (m +' n)
      embed-suc (i , p) = m +' i , (+₁-preserves-< p)

    -- Exposed so that the final proof can use it
    SplitFin : Fin (m +' n) -> Type₀
    SplitFin i = (Σ[ j ∈ Fin m ] (embed-inc j) == i) ⊎
                 (Σ[ j ∈ Fin n ] (embed-suc j) == i)

    abstract
      embed-inc-injective : {i j : Fin m} -> embed-inc i == embed-inc j -> i == j
      embed-inc-injective p = fin-i-path (cong Fin.i p)

      embed-suc-injective : {i j : Fin n} -> embed-suc i == embed-suc j -> i == j
      embed-suc-injective p = fin-i-path (+'-left-injective (cong Fin.i p))

      embed-inc!=embed-suc : {i : Fin m} {j : Fin n} -> embed-inc i != embed-suc j
      embed-inc!=embed-suc {i , lt-i} {j , _} p = zero-≮ lt'
        where
        lt : (j +' m) < m
        lt = transport (\k -> (cong Fin.i p >=> +'-commute {m} {j}) k < m) lt-i
        lt' : j < 0
        lt' = (+-right-≤⁻ m) lt


      split-fin : (i : Fin (m +' n)) -> SplitFin i
      split-fin (i , p) with (split-< i m)
      ... | (inj-l i<m)          = inj-l ((i , i<m) , fin-i-path refl)
      ... | (inj-r (j , j+m==i)) = inj-r (res , fin-i-path (+'-commute {m} {j} >=> j+m==i))
        where
        res : Fin n
        res = (j , lemma)
          where
          m+j<m+n : (m +' j) < (m +' n)
          m+j<m+n = transport (\k -> (sym j+m==i >=> +'-commute {j} {m}) k < (m +' n)) p
          lemma : j < n
          lemma = +₁-reflects-< m+j<m+n

      join-fin-f : (Fin m -> Fin m) -> (Fin n -> Fin n)
                    -> Fin (m +' n) -> Fin (m +' n)
      join-fin-f f g i with (split-fin i)
      ... | (inj-l (j , _)) = embed-inc (f j)
      ... | (inj-r (j , _)) = embed-suc (g j)

      join-fin-f-embed-inc :
        (f : Fin m -> Fin m) ->
        (g : Fin n -> Fin n) ->
        (i : Fin m) ->
        join-fin-f f g (embed-inc i) == embed-inc (f i)
      join-fin-f-embed-inc f g (i , p) with split-fin (embed-inc (i , p))
      ... | (inj-l (_ , jp)) = cong (embed-inc ∘ f) (embed-inc-injective jp)
      ... | (inj-r (_ , jp)) = bot-elim (embed-inc!=embed-suc (sym jp))

      join-fin-f-embed-suc :
        (f : Fin m -> Fin m) ->
        (g : Fin n -> Fin n) ->
        (i : Fin n) ->
        join-fin-f f g (embed-suc i) == embed-suc (g i)
      join-fin-f-embed-suc f g (i , p) with split-fin (embed-suc (i , p))
      ... | (inj-l (_ , jp)) = bot-elim (embed-inc!=embed-suc jp)
      ... | (inj-r (_ , jp)) = cong (embed-suc ∘ g) (embed-suc-injective jp)

      module _ (f1 : Fin m -> Fin m) (g1 : Fin n -> Fin n)
               (f2 : Fin m -> Fin m) (g2 : Fin n -> Fin n) where
        join-fin-f-embed-inc-2 : {j : Fin m} ->
          (join-fin-f f1 g1 ∘ join-fin-f f2 g2 ∘ embed-inc) j == (embed-inc ∘ f1 ∘ f2) j
        join-fin-f-embed-inc-2 {j} =
          (cong (join-fin-f f1 g1) (join-fin-f-embed-inc f2 g2 j))
          >=> join-fin-f-embed-inc f1 g1 (f2 j)

        join-fin-f-embed-suc-2 : {j : Fin n} ->
          (join-fin-f f1 g1 ∘ join-fin-f f2 g2 ∘ embed-suc) j == (embed-suc ∘ g1 ∘ g2) j
        join-fin-f-embed-suc-2 {j} =
          (cong (join-fin-f f1 g1) (join-fin-f-embed-suc f2 g2 j))
          >=> join-fin-f-embed-suc f1 g1 (g2 j)

        join-fin-f-embed-inc-inv :
          (inv : (i : Fin m) -> (f1 (f2 i)) == i)
          {i : Fin (m +' n)} {j : Fin m}
          (p : (embed-inc j) == i)
          -> (join-fin-f f1 g1 ∘ join-fin-f f2 g2) i == i
        join-fin-f-embed-inc-inv inv {i} {j} p =
          (\k -> join-fin-f f1 g1 (join-fin-f f2 g2 (p (~ k))))
          >=> join-fin-f-embed-inc-2
          >=> (cong embed-inc (inv j))
          >=> p

        join-fin-f-embed-suc-inv :
          (inv : (i : Fin n) -> (g1 (g2 i)) == i)
          {i : Fin (m +' n)} {j : Fin n}
          (p : (embed-suc j) == i)
          -> (join-fin-f f1 g1 ∘ join-fin-f f2 g2) i == i
        join-fin-f-embed-suc-inv inv {i} {j} p =
          (\k -> join-fin-f f1 g1 (join-fin-f f2 g2 (p (~ k))))
          >=> join-fin-f-embed-suc-2
          >=> (cong embed-suc (inv j))
          >=> p

  module _ (φ : Perm m) (ψ : Perm n) where
    appendPerm : Perm (m +' n)
    appendPerm .fun = join-fin-f (φ .fun) (ψ .fun)
    appendPerm .inv = join-fin-f (φ .inv) (ψ .inv)
    appendPerm .rightInv i = handle (split-fin i)
      where
      handle : SplitFin i -> join-fin-f (φ .fun) (ψ .fun) (join-fin-f (φ .inv) (ψ .inv) i) == i
      handle (inj-l (j , jp)) =
        join-fin-f-embed-inc-inv (φ .fun) (ψ .fun) (φ .inv) (ψ .inv) (φ .rightInv) jp
      handle (inj-r (j , jp)) =
        join-fin-f-embed-suc-inv (φ .fun) (ψ .fun) (φ .inv) (ψ .inv) (ψ .rightInv) jp
    appendPerm .leftInv i = handle (split-fin i)
      where
      handle : SplitFin i -> join-fin-f (φ .inv) (ψ .inv) (join-fin-f (φ .fun) (ψ .fun) i) == i
      handle (inj-l (j , jp)) =
        join-fin-f-embed-inc-inv (φ .inv) (ψ .inv) (φ .fun) (ψ .fun) (φ .leftInv) jp
      handle (inj-r (j , jp)) =
        join-fin-f-embed-suc-inv (φ .inv) (ψ .inv) (φ .fun) (ψ .fun) (ψ .leftInv) jp


private
  fin-injective->section : {n : Nat} (f : Fin n -> Fin n) -> Injective f -> Section f
  fin-injective->section {zero} f f-inj = (\i -> i) , (\i -> bot-elim (¬fin-zero i))
  fin-injective->section {suc n} f f-inj = handle (find-right-inverse f)
    where
    handle : (Σ[ j ∈ Fin (suc n) ] (∀ i -> ¬(f i == j))) ⊎ Section f -> Section f
    handle (inj-r inv) = inv
    handle (inj-l (j , not-image)) = bot-elim (pigeonhole-large (add1-< n) f' f'-inj)
      where
      f' : Fin (suc n) -> Fin n
      f' i = remove-fin j (f i) (not-image i ∘ sym)

      f'-inj : Injective f'
      f'-inj {i1} {i2} p =
        f-inj (remove-fin-inj j (f i1) (f i2) (not-image i1 ∘ sym) (not-image i2 ∘ sym) p)


module _ {n : Nat} (f : (Fin n) -> (Fin n)) (inj-f : (Injective f)) where
  open Iso
  private
    abstract
      Σg : Section f
      Σg = fin-injective->section f inj-f
      g : Fin n -> Fin n
      g = fst Σg
      sec : isSectionOf f g
      sec = snd Σg

  fin-injective->permutation : Perm n
  fin-injective->permutation .fun = f
  fin-injective->permutation .inv = g
  fin-injective->permutation .rightInv = sec
  fin-injective->permutation .leftInv x = inj-f (sec (f x))

module _ {n : Nat} where
  open Iso
  private
    forward : (Σ ((Fin n) -> (Fin n)) Injective) -> Perm n
    forward (f , inj-f) = fin-injective->permutation f inj-f

    backward : Perm n -> (Σ ((Fin n) -> (Fin n)) Injective)
    backward i = i .fun , f-inj
      where
      f-inj : Injective (i .fun)
      f-inj {x} {y} p = sym (i .leftInv x) >=> cong (i .inv) p >=> (i .leftInv y)

  fin-injective-permutation-iso : Iso (Σ ((Fin n) -> (Fin n)) Injective) (Perm n)
  fin-injective-permutation-iso .fun = forward
  fin-injective-permutation-iso .inv = backward
  fin-injective-permutation-iso .rightInv _ = isSet-iso-path isSetFin isSetFin refl
  fin-injective-permutation-iso .leftInv  (f , inj-f) = ΣProp-path (isPropInjective isSetFin) refl
