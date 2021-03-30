{-# OPTIONS --cubical --safe --exact-split #-}

module new-permutation where

open import base
open import equality
open import equivalence
open import fin
open import functions
open import isomorphism
open import hlevel
open import nat
open import pigeonhole
open import relation
open import sigma

open Iso

Perm : Nat -> Type₀
Perm n = Auto (Fin n)

-- Identity permutation
idPerm : {n : Nat} -> Perm n
idPerm = id-iso

-- Permutation that holds 'zero-fin' constant and acts like the shifted argument otherwise
suc-fin-f : {n : Nat} -> (Fin n -> Fin n) -> (Fin (suc n) -> Fin (suc n))
suc-fin-f f (zero  , lt) = (zero , lt)
suc-fin-f f (suc i , lt) = (suc-fin ∘ f) (i , pred-≤ lt)

private
  suc-fin-f-compose-path : {n : Nat} (f : Fin n -> Fin n) ->
    (suc-fin-f f ∘ suc-fin) == (suc-fin ∘ f)
  suc-fin-f-compose-path f k (i , p) = path k
    where
    lemma : (suc (f (i , pred-≤ (suc-≤ p)) .fst)) == suc (f (i , p) .fst)
    lemma k = (suc (f (i , isProp≤ (pred-≤ (suc-≤ p)) p k) .fst))

    path : (suc-fin-f f ∘ suc-fin) (i , p) == (suc-fin ∘ f) (i , p)
    path = ΣProp-path isProp≤ lemma

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
    path = ΣProp-path isProp≤ refl
  fin-fun-eq-split-zero {f = f} {g = g} zp sp i (suc j , p) =
    ((cong f path) ∙∙ (\i -> sp i (j , (pred-≤ p))) ∙∙ (cong g (sym path))) i

    where
    path : (suc j , p) == suc-fin (j , (pred-≤ p))
    path = ΣProp-path isProp≤ refl

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
  module _ where -- private
    embed-inc : Fin m -> Fin (m +' n)
    embed-inc (i , p) = (i , lemma)
      where
      lemma : i < (m +' n)
      lemma = trans-<-≤ p (transport (\k -> (+'-commute {m} {0} k) ≤ (m +' n))
                                     (+-left-≤⁺ m zero-≤))

    embed-suc : Fin n -> Fin (m +' n)
    embed-suc (i , p) = m +' i , (+-left-<⁺ m p)

    embed-inc-injective : {i j : Fin m} -> embed-inc i == embed-inc j -> i == j
    embed-inc-injective p = ΣProp-path isProp≤ (cong fst p)

    embed-suc-injective : {i j : Fin n} -> embed-suc i == embed-suc j -> i == j
    embed-suc-injective p = ΣProp-path isProp≤ (+'-left-injective (cong fst p))

    embed-inc!=embed-suc : {i : Fin m} {j : Fin n} -> embed-inc i != embed-suc j
    embed-inc!=embed-suc {i , lt-i} {j , _} p = zero-≮ lt'
      where
      lt : (j +' m) < m
      lt = transport (\k -> (cong fst p >=> +'-commute {m} {j}) k < m) lt-i
      lt' : j < 0
      lt' = (+-right-≤⁻ m) lt

    SplitFin : Fin (m +' n) -> Type₀
    SplitFin i = (Σ[ j ∈ Fin m ] (embed-inc j) == i) ⊎
                 (Σ[ j ∈ Fin n ] (embed-suc j) == i)

    split-fin : (i : Fin (m +' n)) -> SplitFin i
    split-fin (i , p) with (split-nat< i m)
    ... | (inj-l i<m)          = inj-l ((i , i<m) , ΣProp-path isProp≤ refl)
    ... | (inj-r (j , j+m==i)) = inj-r (res , ΣProp-path isProp≤ (+'-commute {m} {j} >=> j+m==i))
      where
      res : Fin n
      res = (j , lemma)
        where
        m+j<m+n : (m +' j) < (m +' n)
        m+j<m+n = transport (\k -> (sym j+m==i >=> +'-commute {j} {m}) k < (m +' n)) p
        lemma : j < n
        lemma = +-left-<⁻ m m+j<m+n

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
  fin-injective->reverse0 : (f : Fin 0 -> Fin 0) -> Injective f
                           -> Σ[ g ∈ (Fin 0 -> Fin 0) ] (Injective g × (∀ x -> (g (f x) == x)))
  fin-injective->reverse0 f inj-f = f , (inj-f , \p -> bot-elim (¬fin-zero p))

  adjust-index-grow : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
  adjust-index-grow        (0     , lt ) j             = suc-fin j
  adjust-index-grow        (suc i , lt1) (0     , lt2) = (0 , right-suc-< lt2)
  adjust-index-grow {zero} (suc i , lt1) (suc j , lt2) = bot-elim (zero-≮ lt2)
  adjust-index-grow {n = n@(suc m)} (suc i , lt1) (suc j , lt2) =
    suc-fin (adjust-index-grow (i , pred-≤ lt1) (j , pred-≤ lt2))

  adjust-index-grow' : {n : Nat} -> FinInd' (suc n) -> FinInd' n -> FinInd' (suc n)
  adjust-index-grow' zero    j       = suc j
  adjust-index-grow' (suc i) zero    = zero
  adjust-index-grow' (suc i) (suc j) = suc (adjust-index-grow' i j)

  adjust-index-shrink' : {n : Nat} -> (i j : FinInd' (suc n)) -> i != j -> FinInd' n
  adjust-index-shrink' {n = _}       zero     zero    np = bot-elim (np refl)
  adjust-index-shrink' {n = (suc _)} (suc i)  zero    np = zero
  adjust-index-shrink' {n = (suc _)} zero     (suc j) np = j
  adjust-index-shrink' {n = (suc _)} (suc i)  (suc j) np =
    suc (adjust-index-shrink' i j (np ∘ cong suc))

  adjust-index-shrink'-inj : {n : Nat} -> (i j1 j2 : FinInd' (suc n))
                             -> (np1 : i != j1) -> (np2 : i != j2)
                             -> adjust-index-shrink' i j1 np1 == adjust-index-shrink' i j2 np2
                             -> j1 == j2
  adjust-index-shrink'-inj {n = _}       zero    zero     zero     np1 np2 p = refl
  adjust-index-shrink'-inj {n = (suc _)} zero    zero     (suc j2) np1 np2 p = bot-elim (np1 refl)
  adjust-index-shrink'-inj {n = (suc _)} zero    (suc j1) zero     np1 np2 p = bot-elim (np2 refl)
  adjust-index-shrink'-inj {n = (suc _)} zero    (suc j1) (suc j2) np1 np2 p = cong suc p
  adjust-index-shrink'-inj {n = (suc _)} (suc i) zero     zero     np1 np2 p = refl
  adjust-index-shrink'-inj {n = (suc _)} (suc i) zero     (suc j2) np1 np2 p =
    bot-elim (fin-ind'-zero!=suc p)
  adjust-index-shrink'-inj {n = (suc _)} (suc i) (suc j1) zero     np1 np2 p =
    bot-elim (fin-ind'-zero!=suc (sym p))
  adjust-index-shrink'-inj {n = (suc _)} (suc i) (suc j1) (suc j2) np1 np2 p =
    cong suc (adjust-index-shrink'-inj i j1 j2 (np1 ∘ cong suc) (np2 ∘ cong suc)
                                       (fin-ind'-suc-injective p))

  smaller-fun : {n : Nat} -> (f : FinInd' (suc n) -> FinInd' (suc n))
              -> Injective f -> (FinInd' n -> FinInd' n)
  smaller-fun f inj-f x = adjust-index-shrink' (f zero) (f (suc x))
                          (fin-ind'-zero!=suc ∘ inj-f)

  smaller-fun-inj : {n : Nat} (f : FinInd' (suc n) -> FinInd' (suc n)) -> (inj-f : Injective f)
                    -> Injective (smaller-fun f inj-f)
  smaller-fun-inj f inj-f {a} {b} p =
    fin-ind'-suc-injective
      (inj-f (adjust-index-shrink'-inj (f zero) (f (suc a)) (f (suc b))
                                       (fin-ind'-zero!=suc ∘ inj-f)
                                       (fin-ind'-zero!=suc ∘ inj-f)
                                       p))

  adjust-index-same' : {n : Nat} -> (i j : FinInd' (suc n)) -> (p : (i != j)) ->
                       adjust-index-grow' i (adjust-index-shrink' i j p) == j
  adjust-index-same' {n = _}       zero     zero    np = bot-elim (np refl)
  adjust-index-same' {n = (suc _)} (suc i)  zero    np = refl
  adjust-index-same' {n = (suc _)} zero     (suc j) np = refl
  adjust-index-same' {n = (suc _)} (suc i)  (suc j) np =
    cong suc (adjust-index-same' i j (np ∘ cong suc))

  smaller-fun-same : {n : Nat} (f : FinInd' (suc n) -> FinInd' (suc n)) (inj-f : Injective f)
                     -> (x : (FinInd' n))
                     -> f (suc x) == adjust-index-grow' (f zero) (smaller-fun f inj-f x)
  smaller-fun-same f inj-f x =
    sym (adjust-index-same' (f zero) (f (suc x)) (fin-ind'-zero!=suc ∘ inj-f))


private
  fin-injective->reverse : {n : Nat} (f : Fin n -> Fin n) -> Injective f
                           -> Satisfiable (RightInverse f)
  fin-injective->reverse {zero} f f-inj = (\i -> bot-elim (¬fin-zero i)) , (\i -> bot-elim (¬fin-zero i))
  fin-injective->reverse {suc n} f f-inj = handle (find-right-inverse f)
    where
    handle : (Σ[ j ∈ Fin (suc n) ] (∀ i -> ¬(f i == j))) ⊎ (Satisfiable (RightInverse f))
              -> Satisfiable (RightInverse f)
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
    Σg = fin-injective->reverse f inj-f
    g = fst Σg
    right-inv = snd Σg

  abstract
    fin-injective->permutation : Perm n
    fin-injective->permutation .fun = f
    fin-injective->permutation .inv = g
    fin-injective->permutation .rightInv = right-inv
    fin-injective->permutation .leftInv x = inj-f (right-inv (f x))
