{-# OPTIONS --cubical --safe --exact-split #-}

module fin where

open import base
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import nat
open import relation
open import sigma
open import sum

-- Fin type is based on ≤ instead of straight inductive structure
-- This is so that things compute better when using transport.

Fin : Nat -> Type₀
Fin n = Σ[ i ∈ Nat ] (i < n)

zero-fin : {n : Nat} -> Fin (suc n)
zero-fin = 0 , zero-<

suc-fin : {n : Nat} -> Fin n -> Fin (suc n)
suc-fin (i , p) = suc i , suc-≤ p

zero-fin!=suc-fin : {n : Nat} {x : Fin n} -> zero-fin != (suc-fin x)
zero-fin!=suc-fin p = zero-suc-absurd (cong fst p)

¬fin-zero : ¬ (Fin 0)
¬fin-zero (i , p) = zero-≮ p

suc-fin-injective : {n : Nat} -> {x y : Fin n} -> suc-fin x == suc-fin y -> x == y
suc-fin-injective p = ΣProp-path isProp≤ (suc-injective (cong fst p))

-- Fin is a Set

decide-fin : {n : Nat} (x : Fin n) -> (y : Fin n) -> Dec (x == y)
decide-fin (i , p1) (j , p2) with decide-nat i j
... | (no i≠j)  = no (i≠j ∘ cong fst)
... | (yes i==j) = yes (ΣProp-path isProp≤ i==j)

discreteFin : {n : Nat} -> Discrete (Fin n)
discreteFin = decide-fin

isSetFin : {n : Nat} -> isSet (Fin n)
isSetFin = Discrete->isSet discreteFin

isPropFin0 : isProp (Fin 0)
isPropFin0 (x , lt) = bot-elim (zero-≮ lt)

isContrFin1 : isContr (Fin 1)
isContrFin1 = zero-fin , proof
  where
  abstract
    proof : (i : Fin 1) -> zero-fin == i
    proof (0 , lt) = ΣProp-path isProp≤ refl
    proof (suc i , lt) = bot-elim (zero-≮ (pred-≤ lt))

fin->nat : {n : Nat} -> Fin n -> Nat
fin->nat (i , p) = i

private
  fin->nat-iso : {n : Nat} {x y : Fin n} -> Iso (x == y) (fin->nat x == fin->nat y)
  Iso.fun fin->nat-iso = cong fin->nat
  Iso.inv fin->nat-iso = ΣProp-path isProp≤
  Iso.rightInv fin->nat-iso _ = isSet->Square isSetNat
  Iso.leftInv  fin->nat-iso _ = isSet->Square isSetFin

fin->nat-path : {n : Nat} {x y : Fin n} -> (x == y) == (fin->nat x == fin->nat y)
fin->nat-path = ua (isoToEquiv fin->nat-iso)

private
  pred-fin : {n : Nat} -> Fin (suc (suc n)) -> Fin (suc n)
  pred-fin (zero  , p)  = (zero , zero-<)
  pred-fin (suc i , p)  = (i    , pred-≤ p)

  suc-fin-iso' : {n : Nat} {x y : Fin (suc n)} -> Iso (x == y) (suc-fin x == suc-fin y)
  Iso.fun suc-fin-iso' p = cong suc-fin p
  Iso.inv suc-fin-iso' p = ΣProp-path isProp≤ (cong (fst ∘ pred-fin) p)
  Iso.rightInv suc-fin-iso' p = isSet->Square isSetFin
  Iso.leftInv  suc-fin-iso' p = isSet->Square isSetFin

-- Naturals in a range

isInRange : Nat -> Nat -> Nat -> Type₀
isInRange m n i = (m ≤ i × i < n)

isPropIsInRange : {m n i : Nat} -> isProp (isInRange m n i)
isPropIsInRange = isProp× isProp≤ isProp≤


InRange : Nat -> Nat -> Type₀
InRange m n = Σ Nat (isInRange m n)

private
  inRange->fin : {m n : Nat} -> InRange m n -> Fin (n -' m)
  inRange->fin {m} {n} (i , ((j , j+m==i) , i<n)) = j , <-minus j+'m<n
    where
    j+'m<n : (j +' m) < n
    j+'m<n = transport (\k -> j+m==i (~ k) < n) i<n

  fin->inRange : {m n : Nat} -> Fin (n -' m) -> InRange m n
  fin->inRange {m} {n} (j , j<n-m) = (j +' m , ((j , refl) , <-minus-rev j<n-m))


  fin->inRange->fin : {m n : Nat} (i : Fin (n -' m))
                      -> (inRange->fin {m} (fin->inRange i)) == i
  fin->inRange->fin _ = ΣProp-path isProp≤ refl

  inRange->fin->inRange : {m n : Nat} (i : InRange m n)
                      -> (fin->inRange (inRange->fin i)) == i
  inRange->fin->inRange (_ , ((_ , path) , _)) = ΣProp-path isPropIsInRange path

  fin-inRange-iso : {m n : Nat} -> Iso (Fin (n -' m)) (InRange m n)
  Iso.fun fin-inRange-iso = fin->inRange
  Iso.inv fin-inRange-iso = inRange->fin
  Iso.rightInv fin-inRange-iso = inRange->fin->inRange
  Iso.leftInv  (fin-inRange-iso {m} {n}) = fin->inRange->fin {m} {n}


fin-inRange-path : {m n : Nat} -> (Fin (n -' m)) == (InRange m n)
fin-inRange-path = ua (isoToEquiv fin-inRange-iso)

-- Finite search functions
abstract
  finite-search : {ℓ₁ ℓ₂ : Level} {n : Nat} {P : Pred (Fin n) ℓ₁} {Q : Pred (Fin n) ℓ₂}
                  -> (Universal (P ∪ Q))
                  -> (Satisfiable P) ⊎ (Universal Q)
  finite-search {n = zero}  dec = inj-r (\ i -> (bot-elim (¬fin-zero i)))
  finite-search {n = suc _} {P} {Q} dec =
    case (dec zero-fin) return _ of \where
      (inj-l p) -> inj-l (zero-fin , p)
      (inj-r q) ->
        case (finite-search (dec ∘ suc-fin))
             return _ of \ where
          (inj-l (i , p)) -> inj-l (suc-fin i , p)
          (inj-r f) -> inj-r \ where
            (zero  , lt) -> subst Q (ΣProp-path isProp≤ refl) q
            (suc i , lt) -> subst Q (ΣProp-path isProp≤ refl) (f (i , pred-≤ lt))

  find-counterexample : {ℓ : Level} {n : Nat} {P : Pred (Fin n) ℓ} -> Decidable P
                        -> (Satisfiable (Comp P)) ⊎ (Universal P)
  find-counterexample dec = finite-search (\x -> ⊎-swap (dec->⊎ (dec x)))

  find-example : {ℓ : Level} {n : Nat} {P : Pred (Fin n) ℓ} -> Decidable P
                        -> (Satisfiable P) ⊎ (Universal (Comp P))
  find-example dec = finite-search (\x -> dec->⊎ (dec x))

-- Inverse functions exist
module _ {n m : Nat} (f : Fin n -> Fin m) where
  private
    -- `Image j i` is the predicate that `j` is the image of `i` under `f`.
    Image : Fin m -> Pred (Fin n) ℓ-zero
    Image j i = (f i == j)

    -- `j` is not the image of any `i`
    neverImage : Pred (Fin m) ℓ-zero
    neverImage j = Universal (Comp (Image j))

    -- `j` is the image of some `i`
    someImage : Pred (Fin m) ℓ-zero
    someImage j = Satisfiable (Image j)

    cases : (Satisfiable neverImage) ⊎ (Universal someImage)
    cases = finite-search (\j -> (⊎-swap (find-example (\i -> discreteFin (f i) j))))

    finite-inverse : (Universal someImage) ->
                     Σ[ g ∈ (Fin m -> Fin n) ] (∀ j -> f (g j) == j)
    finite-inverse images = g , g-inv
      where
      g : Fin m -> Fin n
      g j = fst (images j)

      g-inv : (j : Fin m) -> (f (g j)) == j
      g-inv j = snd (images j)

  abstract
    find-right-inverse : (Satisfiable neverImage) ⊎
                         (Satisfiable (RightInverse f))
    find-right-inverse = ⊎-map-right finite-inverse cases

-- Remove a particular number from the set
private
  remove-fin' : {n : Nat} -> (i : Nat) -> i < (suc n) -> (j : Nat) -> j < (suc n)
                -> i != j -> Fin n
  remove-fin'               zero    i-lt zero    j-lt np = bot-elim (np refl)
  remove-fin'               (suc i) i-lt zero    j-lt np = zero , (trans-≤-< zero-≤ (pred-≤ i-lt))
  remove-fin'               zero    i-lt (suc j) j-lt np = j , pred-≤ j-lt
  remove-fin' {n = zero}    (suc i) i-lt (suc j) j-lt np = bot-elim (zero-≮ (pred-≤ i-lt))
  remove-fin' {n = (suc n)} (suc i) i-lt (suc j) j-lt np =
    suc-fin (remove-fin' i (pred-≤ i-lt) j (pred-≤ j-lt) (np ∘ cong suc))

  remove-fin'-inj : {n : Nat}
                    -> (i : Nat) -> (i-lt : i < (suc n) )
                    -> (j1 : Nat) -> (j1-lt : j1 < (suc n)) -> (j1-np : i != j1)
                    -> (j2 : Nat) -> (j2-lt : j2 < (suc n)) -> (j2-np : i != j2)
                    -> remove-fin' i i-lt j1 j1-lt j1-np == remove-fin' i i-lt j2 j2-lt j2-np
                    -> j1 == j2
  remove-fin'-inj               zero    i-lt zero     j1-lt j1-np zero     j2-lt j2-np p =
    refl
  remove-fin'-inj               zero    i-lt zero     j1-lt j1-np (suc j2) j2-lt j2-np p =
    bot-elim (j1-np refl)
  remove-fin'-inj               zero    i-lt (suc j1) j1-lt j1-np zero     j2-lt j2-np p =
    bot-elim (j2-np refl)
  remove-fin'-inj               zero    i-lt (suc j1) j1-lt j1-np (suc j2) j2-lt j2-np p =
    cong (suc ∘ fst) p
  remove-fin'-inj {n = zero}    (suc i) i-lt j1       j1-lt j1-np j2       j2-lt j2-np p =
    bot-elim (zero-≮ (pred-≤ i-lt))
  remove-fin'-inj {n = (suc n)} (suc i) i-lt zero     j1-lt j1-np zero     j2-lt j2-np p =
    refl
  remove-fin'-inj {n = (suc n)} (suc i) i-lt zero     j1-lt j1-np (suc j2) j2-lt j2-np p =
    zero-suc-absurd (cong fst p)
  remove-fin'-inj {n = (suc n)} (suc i) i-lt (suc j1) j1-lt j1-np zero     j2-lt j2-np p =
    zero-suc-absurd (cong fst (sym p))
  remove-fin'-inj {n = (suc n)} (suc i) i-lt (suc j1) j1-lt j1-np (suc j2) j2-lt j2-np p =
    cong suc
      (remove-fin'-inj i (pred-≤ i-lt)
                       j1 (pred-≤ j1-lt) (j1-np ∘ cong suc)
                       j2 (pred-≤ j2-lt) (j2-np ∘ cong suc)
                       (suc-fin-injective p))

abstract
  remove-fin : {n : Nat} -> (i j : Fin (suc n)) -> i != j -> Fin n
  remove-fin (i , i-lt) (j , j-lt) np = remove-fin' i i-lt j j-lt (np ∘ ΣProp-path isProp≤)

  remove-fin-inj : {n : Nat} -> (i j1 j2 : Fin (suc n)) -> (j1-np : i != j1) -> (j2-np : i != j2)
                   -> remove-fin i j1 j1-np == remove-fin i j2 j2-np
                   -> j1 == j2
  remove-fin-inj (i , i-lt) (j1 , j1-lt) (j2 , j2-lt) j1-np j2-np p =
    ΣProp-path isProp≤
      (remove-fin'-inj i i-lt
                       j1 j1-lt (j1-np ∘ ΣProp-path isProp≤)
                       j2 j2-lt (j2-np ∘ ΣProp-path isProp≤)
                       p)

-- Fins based on inductive ≤

FinInd : Nat -> Type₀
FinInd n = Σ[ i ∈ Nat ] (i <i n)

zero-fin-ind : {n : Nat} -> FinInd (suc n)
zero-fin-ind = zero , zero-<i

suc-fin-ind : {n : Nat} -> FinInd n -> FinInd (suc n)
suc-fin-ind (i , p) = suc i , suc-≤i p

fin-fin-ind-iso : {n : Nat} -> Iso (Fin n) (FinInd n)
Iso.fun fin-fin-ind-iso (i , p) = (i , (Iso.fun ≤-≤i-iso p))
Iso.inv fin-fin-ind-iso (i , p) = (i , (Iso.inv ≤-≤i-iso p))
Iso.rightInv fin-fin-ind-iso (i , p) = ΣProp-path isProp≤i refl
Iso.leftInv  fin-fin-ind-iso (i , p) = ΣProp-path isProp≤ refl

Fin==FinInd : {n : Nat} -> Fin n == FinInd n
Fin==FinInd {n} k = Σ[ i ∈ Nat ] (≤==≤i {suc i} {n} k)

-- Fins using an inductive data type

data FinInd' : Nat -> Type₀ where
  zero : {n : Nat} -> FinInd' (suc n)
  suc  : {n : Nat} -> FinInd' n -> FinInd' (suc n)

private
  FinInd'Zero : {n : Nat} -> FinInd' n -> Set
  FinInd'Zero zero    = Top
  FinInd'Zero (suc _) = Bot

  fin-ind'-pred : {n : Nat} -> FinInd' (suc (suc n)) -> FinInd' (suc n)
  fin-ind'-pred zero    = zero
  fin-ind'-pred (suc x) = x

fin-ind'-suc-injective : {n : Nat} {x y : FinInd' n}
                          -> Path (FinInd' (suc n)) (suc x) (suc y) -> x == y
fin-ind'-suc-injective {suc n} p = cong fin-ind'-pred p

fin-ind'-zero!=suc : {n : Nat} {x : FinInd' n} -> zero != suc x
fin-ind'-zero!=suc p = bot-elim (transport (cong FinInd'Zero p) tt)

decide-fin-ind' : {n : Nat} -> (x y : FinInd' n) -> Dec (x == y)
decide-fin-ind' zero    zero    = yes refl
decide-fin-ind' zero    (suc y) = no fin-ind'-zero!=suc
decide-fin-ind' (suc _) zero    = no (fin-ind'-zero!=suc ∘ sym)
decide-fin-ind' (suc x) (suc y) with decide-fin-ind' x y
... | (yes p) = yes (cong suc p)
... | (no f) = no (f ∘ fin-ind'-suc-injective)

isSetFinInd' : {n : Nat} -> isSet (FinInd' n)
isSetFinInd' = Discrete->isSet decide-fin-ind'

private
  fin-ind'->fin-ind : {n : Nat} -> FinInd' n -> FinInd n
  fin-ind'->fin-ind zero    = zero-fin-ind
  fin-ind'->fin-ind (suc f) = suc-fin-ind (fin-ind'->fin-ind f)

  fin-ind->fin-ind' : {n : Nat} -> FinInd n -> FinInd' n
  fin-ind->fin-ind' (zero  , (suc-≤i _))  = zero
  fin-ind->fin-ind' (suc f , (suc-≤i lt)) = suc (fin-ind->fin-ind' (f , lt))

  fin-ind'->fin-ind->fin-ind' : {n : Nat} (f : FinInd' n)
                                -> (fin-ind->fin-ind' (fin-ind'->fin-ind f)) == f
  fin-ind'->fin-ind->fin-ind' zero    = refl
  fin-ind'->fin-ind->fin-ind' (suc f) = cong suc (fin-ind'->fin-ind->fin-ind' f)

  fin-ind->fin-ind'->fin-ind : {n : Nat} (f : FinInd n)
                                -> (fin-ind'->fin-ind (fin-ind->fin-ind' f)) == f
  fin-ind->fin-ind'->fin-ind (zero  , (suc-≤i zero-≤i))  = refl
  fin-ind->fin-ind'->fin-ind (suc f , (suc-≤i lt)) = cong suc-fin-ind (fin-ind->fin-ind'->fin-ind (f , lt))


  fin-ind'-fin-ind-iso : {n : Nat} -> Iso (FinInd' n) (FinInd n)
  Iso.fun fin-ind'-fin-ind-iso = fin-ind'->fin-ind
  Iso.inv fin-ind'-fin-ind-iso = fin-ind->fin-ind'
  Iso.rightInv fin-ind'-fin-ind-iso = fin-ind->fin-ind'->fin-ind
  Iso.leftInv  fin-ind'-fin-ind-iso = fin-ind'->fin-ind->fin-ind'

fin-fin-ind'-iso : {n : Nat} -> Iso (Fin n) (FinInd' n)
fin-fin-ind'-iso = (iso⁻¹ fin-ind'-fin-ind-iso) ∘ⁱ fin-fin-ind-iso

Fin==FinInd' : {n : Nat} -> Fin n == FinInd' n
Fin==FinInd' = isoToPath fin-fin-ind'-iso
