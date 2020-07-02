{-# OPTIONS --cubical --safe --exact-split #-}

module ind-permutation where

open import base
open import equality
open import equivalence
open import fin
open import functions
open import isomorphism
open import hlevel
open import nat
open import relation
open import sigma

open Iso

Perm : Nat -> Type₀
Perm n = Auto (FinInd n)

-- Identity permutation
idPerm : {n : Nat} -> Perm n
idPerm = id-iso

-- Permutation that holds 'zero-fin' constant and acts like the shifted argument otherwise
suc-fin-f : {n : Nat} -> (FinInd n -> FinInd n) -> (FinInd (suc n) -> FinInd (suc n))
suc-fin-f f (zero  , _          ) = zero-fin-ind
suc-fin-f f (suc i , (suc-≤i lt)) = suc-fin-ind (f (i , lt))

sucPerm : {n : Nat} -> Perm n -> Perm (suc n)
sucPerm φ .fun = suc-fin-f (φ .fun)
sucPerm φ .inv = suc-fin-f (φ .inv)
sucPerm φ .rightInv (zero  , (suc-≤i zero-≤i))   = refl
sucPerm φ .rightInv (suc i , (suc-≤i lt     )) j = suc-fin-ind (φ .rightInv (i , lt) j)
sucPerm φ .leftInv  (zero  , (suc-≤i zero-≤i))   = refl
sucPerm φ .leftInv  (suc i , (suc-≤i lt     )) j = suc-fin-ind (φ .leftInv (i , lt) j)


-- Rotation permutations

private
  -- 0 -> (n - 1) ; (suc i) -> i
  rotate-fin-f : {n : Nat} -> FinInd n -> FinInd n
  rotate-fin-f {suc n} (0       , _         ) .fst = n
  rotate-fin-f {suc n} (0       , _         ) .snd = (same-≤i (suc n))
  rotate-fin-f         ((suc i) , (suc-≤i _)) .fst = i
  rotate-fin-f         ((suc i) , (suc-≤i p)) .snd = (right-suc-≤i p)

  -- (n - 1) -> 0 ; otherwise i -> (suc i)
  rotate-fin-rev : {n : Nat} -> FinInd n -> FinInd n
  rotate-fin-rev {n@(suc _)} (i , _) = rec (split-nat<i (suc i) n)
    where
    rec : ((suc i <i n) ⊎ (n ≤i suc i)) -> FinInd n
    rec (inj-l p) = (suc i) , p
    rec (inj-r _) = 0 , zero-<i

  rotate-fin-rightInv : {n : Nat} (i : FinInd n) -> rotate-fin-f (rotate-fin-rev i) == i
  rotate-fin-rightInv i = ΣProp-path isProp≤i (inner i)
    where
    inner : {n : Nat} (i : FinInd n) -> rotate-fin-f (rotate-fin-rev i) .fst == i .fst
    inner {n@(suc n')} (i , p) with (split-nat<i (suc i) n)
    ... | (inj-l (suc-≤i _)) = refl
    ... | (inj-r q) = answer
      where
      n≤si : n ≤ suc i
      n≤si = transport (sym ≤==≤i) q
      si≤n : suc i ≤ n
      si≤n = transport (sym ≤==≤i) p

      answer : n' == i
      answer = suc-injective (≤-antisym n≤si si≤n)

  rotate-fin-leftInv : {n : Nat} (i : FinInd n) -> rotate-fin-rev (rotate-fin-f i) == i
  rotate-fin-leftInv i = ΣProp-path isProp≤i (inner i)
    where
    inner : {n : Nat} (i : FinInd n) -> rotate-fin-rev (rotate-fin-f i) .fst == i .fst
    inner {suc n} (0 , _) with (split-nat<i (suc n) (suc n))
    ... | (inj-l p) = bot-elim (same-≮ (transport (sym ≤==≤i) p))
    ... | (inj-r _) = refl
    inner {suc n} ((suc i) , p@(suc-≤i _)) with (split-nat<i (suc i) (suc n))
    ... | (inj-l _) = refl
    ... | (inj-r q) = bot-elim (same-≮ (trans-≤ (transport (sym ≤==≤i) p) (transport (sym ≤==≤i) q)))

rotatePerm : {n : Nat} -> Perm n
rotatePerm .fun = rotate-fin-f
rotatePerm .inv = rotate-fin-rev
rotatePerm .rightInv = rotate-fin-rightInv
rotatePerm .leftInv  = rotate-fin-leftInv

-- Append two permutations

module _ {m n : Nat} (φ : Perm m) (ψ : Perm n) where
  private
    embed-inc : FinInd m -> FinInd (m +' n)
    embed-inc (i , p) = (i , transport ≤==≤i (lemma (transport (sym ≤==≤i) p)))
      where
      lemma : i < m -> i < (m +' n)
      lemma p = trans-<-≤ p (transport (\k -> (+'-commute {m} {0} k) ≤ (m +' n))
                                       (transport (+-left-≤ m) zero-≤))

    embed-suc : FinInd n -> FinInd (m +' n)
    embed-suc (i , p) = (m +' i , transport ≤==≤i (lemma (transport (sym ≤==≤i) p)))
      where
      lemma : i < n -> (m +' i) < (m +' n)
      lemma p = transport (+-left-< m) p

    join-fin-f : (FinInd m -> FinInd m) -> (FinInd n -> FinInd n)
                  -> FinInd (m +' n) -> FinInd (m +' n)
    join-fin-f f g (i , p) with (split-nat< i m)
    ... | (inj-l i<m) = embed-inc res
      where
      res : FinInd m
      res = f (i , (transport ≤==≤i i<m))
    ... | (inj-r (j , j+m==i)) = embed-suc res
      where
      res : FinInd n
      res = g (j , (transport ≤==≤i lemma))
        where
        i<m+n : i < (m +' n)
        i<m+n = transport (sym ≤==≤i) p
        m+j<m+n : (m +' j) < (m +' n)
        m+j<m+n = transport (\k -> (sym j+m==i >=> +'-commute {j} {m}) k < (m +' n)) i<m+n
        lemma : j < n
        lemma = transport (sym (+-left-< m)) m+j<m+n
