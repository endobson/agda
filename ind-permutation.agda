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

-- Helper to deal with slow typechecking
make-perm : {n : Nat}
            (fun      : (FinInd n) -> (FinInd n))
            (inv      : (FinInd n) -> (FinInd n))
            (rightInv : section fun inv)
            (leftInv  : retract fun inv)
            -> Perm n
make-perm fun inv rightInv leftInv = record
  { fun = fun
  ; inv = inv
  ; rightInv = rightInv
  ; leftInv = leftInv
  }


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

module _ {m n : Nat} where
  private

    embed-suc : FinInd n -> FinInd (m +' n)
    embed-suc (i , lt) = (m +' i , (+-left-<i⁺ m lt))

    embed-inc : FinInd m -> FinInd (m +' n)
    embed-inc (i , lt) = (i , lemma lt)
      where
      lemma : i <i m -> i <i (m +' n)
      lemma p = trans-<i-≤i p (transport (\k -> (+'-commute {m} {0} k) ≤i (m +' n))
                                         (+-left-≤i⁺ m zero-≤i))

    embed-inc-injective : {i j : FinInd m} -> embed-inc i == embed-inc j -> i == j
    embed-inc-injective p = ΣProp-path isProp≤i (cong fst p)

    embed-suc-injective : {i j : FinInd n} -> embed-suc i == embed-suc j -> i == j
    embed-suc-injective p = ΣProp-path isProp≤i (+'-left-injective (cong fst p))

    embed-inc!=embed-suc : {i : FinInd m} {j : FinInd n} -> embed-inc i != embed-suc j
    embed-inc!=embed-suc {i , lt-i} {j , _} p = zero-≮i lt'
      where
      lt : (j +' m) <i m
      lt = transport (\k -> (cong fst p >=> +'-commute {m} {j}) k <i m) lt-i

      lt' : j <i 0
      lt' = (+-right-≤i⁻ m) lt

    SplitFin : FinInd (m +' n) -> Type₀
    SplitFin i = (Σ[ j ∈ FinInd m ] (embed-inc j) == i) ⊎
                 (Σ[ j ∈ FinInd n ] (embed-suc j) == i)

    split-fin : (i : FinInd (m +' n)) -> SplitFin i
    split-fin (i , p) with (split-nat<i i m)
    ... | (inj-l i<m) = inj-l ((i , i<m) , ΣProp-path isProp≤i refl)
    ... | (inj-r m≤i) = inj-r (j         , ΣProp-path isProp≤i path)
      where

      recur-down : {m i n : Nat} -> m ≤i i -> i <i (m +' n)
                   -> Σ[ x ∈ FinInd n ] (x .fst == (i -' m))
      recur-down {i = i} zero-≤i      lt           = (i , lt) , refl
      recur-down         (suc-≤i lt1) (suc-≤i lt2) = (recur-down lt1 lt2)

      j : FinInd n
      j = recur-down m≤i p .fst

      path' : m +' (i -' m) == i
      path' = rec m≤i
        where
        rec : {m i : Nat} -> m ≤i i -> (m +' (i -' m)) == i
        rec zero-≤i     = refl
        rec (suc-≤i lt) = cong suc (rec lt)

      path : m +' j .fst == i
      path = (\k -> m +' (recur-down m≤i p .snd k)) >=> path'


    join-fin-f : (FinInd m -> FinInd m) -> (FinInd n -> FinInd n)
                  -> FinInd (m +' n) -> FinInd (m +' n)
    join-fin-f f g i with (split-fin i)
    ... | (inj-l (j , _)) = embed-inc (f j)
    ... | (inj-r (j , _)) = embed-suc (g j)

    join-fin-f-embed-inc :
      (f : FinInd m -> FinInd m) ->
      (g : FinInd n -> FinInd n) ->
      (i : FinInd m) ->
      join-fin-f f g (embed-inc i) == embed-inc (f i)
    join-fin-f-embed-inc f g i with split-fin (embed-inc i)
    ... | (inj-l (_ , jp)) = cong (embed-inc ∘ f) (embed-inc-injective jp)
    ... | (inj-r (j , jp)) = bot-elim (embed-inc!=embed-suc {i} {j} (sym jp))

    join-fin-f-embed-suc :
      (f : FinInd m -> FinInd m) ->
      (g : FinInd n -> FinInd n) ->
      (i : FinInd n) ->
      join-fin-f f g (embed-suc i) == embed-suc (g i)
    join-fin-f-embed-suc f g i with split-fin (embed-suc i)
    ... | (inj-l (j , jp)) = bot-elim (embed-inc!=embed-suc {j} {i} jp)
    ... | (inj-r (_ , jp)) = cong (embed-suc ∘ g) (embed-suc-injective jp)

    module _ (f1 : FinInd m -> FinInd m) (g1 : FinInd n -> FinInd n)
             (f2 : FinInd m -> FinInd m) (g2 : FinInd n -> FinInd n) where

      join-fin-f-embed-inc-2 : {j : FinInd m} ->
        join-fin-f f1 g1 (join-fin-f f2 g2 (embed-inc j)) == embed-inc (f1 (f2 j))
      join-fin-f-embed-inc-2 {j} =
        (cong (join-fin-f f1 g1) (join-fin-f-embed-inc f2 g2 j))
        >=> join-fin-f-embed-inc f1 g1 (f2 j)

      join-fin-f-embed-suc-2 : {j : FinInd n} ->
        join-fin-f f1 g1 (join-fin-f f2 g2 (embed-suc j)) == embed-suc (g1 (g2 j))
      join-fin-f-embed-suc-2 {j} =
        (cong (join-fin-f f1 g1) (join-fin-f-embed-suc f2 g2 j))
        >=> join-fin-f-embed-suc f1 g1 (g2 j)

      join-fin-f-embed-inc-inv :
        (inv : (i : FinInd m) -> (f1 (f2 i)) == i)
        {i : FinInd (m +' n)} {j : FinInd m}
        (p : (embed-inc j) == i)
        -> join-fin-f f1 g1 (join-fin-f f2 g2 i) == i
      join-fin-f-embed-inc-inv inv {i} {j} p =
        (cong (join-fin-f f1 g1) (cong (join-fin-f f2 g2) (sym p)))
        >=> join-fin-f-embed-inc-2 {j}
        >=> (cong embed-inc (inv j))
        >=> p

      join-fin-f-embed-suc-inv :
        (inv : (i : FinInd n) -> (g1 (g2 i)) == i)
        {i : FinInd (m +' n)} {j : FinInd n}
        (p : (embed-suc j) == i)
        -> join-fin-f f1 g1 (join-fin-f f2 g2 i) == i
      join-fin-f-embed-suc-inv inv {i} {j} p =
        (cong (join-fin-f f1 g1) (cong (join-fin-f f2 g2) (sym p)))
        >=> join-fin-f-embed-suc-2 {j}
        >=> (cong embed-suc (inv j))
        >=> p

  module _ (φ : Perm m) (ψ : Perm n) where

    φf = (φ .fun)
    φi = (φ .inv)
    ψf = (ψ .fun)
    ψi = (ψ .inv)

    append-fun : FinInd (m +' n) -> FinInd (m +' n)
    append-fun = join-fin-f φf ψf
    append-inv : FinInd (m +' n) -> FinInd (m +' n)
    append-inv = join-fin-f φi ψi

    append-rightInv : section (join-fin-f φf ψf) (join-fin-f φi ψi)
    append-rightInv i = handle (split-fin i)
      where
      handle : SplitFin i -> join-fin-f φf ψf (join-fin-f φi ψi i) == i
      handle (inj-l (j , jp)) =
        join-fin-f-embed-inc-inv φf ψf φi ψi (φ .rightInv) jp
      handle (inj-r (j , jp)) =
        join-fin-f-embed-suc-inv φf ψf φi ψi (ψ .rightInv) jp

    append-leftInv : retract (join-fin-f φf ψf) (join-fin-f φi ψi)
    append-leftInv i = handle (split-fin i)
      where
      handle : SplitFin i -> join-fin-f φi ψi (join-fin-f φf ψf i) == i
      handle (inj-l (j , jp)) =
        join-fin-f-embed-inc-inv φi ψi φf ψf (φ .leftInv) jp
      handle (inj-r (j , jp)) =
        join-fin-f-embed-suc-inv φi ψi φf ψf (ψ .leftInv) jp

    appendPerm : Perm (m +' n)
    appendPerm = make-perm (join-fin-f φf ψf) (join-fin-f φi ψi) append-rightInv append-leftInv

sucPerm' : {n : Nat} -> Perm n -> Perm (suc n)
sucPerm' φ = appendPerm (idPerm {1}) φ

private
  sucPerm'-check-zero : {n : Nat} (φ : Perm n) -> sucPerm' φ .fun zero-fin-ind .fst == 0
  sucPerm'-check-zero _ = refl

  sucPerm'-check-suc : {n : Nat} (φ : Perm n) (i : FinInd n)
                        -> sucPerm' φ .fun (suc-fin-ind i) .fst
                           == suc-fin-ind (φ .fun i) .fst
  sucPerm'-check-suc _ _ = refl
