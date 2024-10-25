{-# OPTIONS --cubical --safe --exact-split #-}

module fin where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical
open import discrete
open import equality
open import functions
open import hlevel
open import isomorphism
open import nat
open import nat.order
open import order
open import order.instances.nat
open import relation
open import sigma.base
open import sum
open import truncation
open import univalence

-- Fin type is based on ≤ instead of straight inductive structure
-- This is so that things compute better when using transport.

record Fin (n : Nat) : Type₀ where
  constructor _,_
  field
    i : Nat
    i<n : i < n

private
  fin-i-pathᵉ : {n : Nat} {x y : Fin n} -> Fin.i x == Fin.i y -> x == y
  fin-i-pathᵉ {n} {x} {y} p = \i -> p i , q i
    where
    q : PathP (\i -> p i < n) (Fin.i<n x) (Fin.i<n y)
    q = isProp->PathP (\i -> isProp-≤)

opaque
  fin-i-path : {n : Nat} {x y : Fin n} -> Fin.i x == Fin.i y -> x == y
  fin-i-path = fin-i-pathᵉ

  fin-j-path : {n : Nat} {x y : Fin n} -> fst (Fin.i<n x) == fst (Fin.i<n y) -> x == y
  fin-j-path {n} {xi , xj , xj+sxi=n} {yi , yj , yj+syi=n} xj=yj = fin-i-path xi=yi
    where
    p1 : yj + (suc xi) == yj + (suc yi)
    p1 = +-left (sym xj=yj) >=> xj+sxi=n >=> sym (yj+syi=n)
    p2 : (suc xi) == (suc yi)
    p2 = +'-left-injective p1
    xi=yi : xi == yi
    xi=yi = cong pred p2


zero-fin : {n : Nat} -> Fin (suc n)
zero-fin = 0 , zero-<

suc-fin : {n : Nat} -> Fin n -> Fin (suc n)
suc-fin (i , p) = suc i , suc-≤ p

inc-fin : {n : Nat} -> Fin n -> Fin (suc n)
inc-fin (i , p) = i , right-suc-≤ p

zero-fin!=suc-fin : {n : Nat} {x : Fin n} -> zero-fin != (suc-fin x)
zero-fin!=suc-fin p = zero-suc-absurd (cong Fin.i p)

¬fin-zero : ¬ (Fin 0)
¬fin-zero (i , p) = zero-≮ p

suc-fin-injective : {n : Nat} -> {x y : Fin n} -> suc-fin x == suc-fin y -> x == y
suc-fin-injective p = fin-i-path (suc-injective (cong Fin.i p))

-- Fin is a Set

decide-fin : {n : Nat} (x : Fin n) -> (y : Fin n) -> Dec (x == y)
decide-fin (i , p1) (j , p2) with decide-nat i j
... | (no i≠j)  = no (i≠j ∘ cong Fin.i)
... | (yes i==j) = yes (fin-i-path i==j)

discreteFin : {n : Nat} -> Discrete (Fin n)
discreteFin = decide-fin

isSetFin : {n : Nat} -> isSet (Fin n)
isSetFin = Discrete->isSet discreteFin

isPropFin0 : isProp (Fin 0)
isPropFin0 (x , lt) = bot-elim (zero-≮ lt)

isContrFin1 : isContr (Fin 1)
isContrFin1 = zero-fin , proof
  where
  opaque
    proof : (i : Fin 1) -> zero-fin == i
    proof (0 , lt) = fin-i-path refl
    proof (suc i , lt) = bot-elim (zero-≮ (pred-≤ lt))

isPropFin1 : isProp (Fin 1)
isPropFin1 x y = sym (snd isContrFin1 x) >=> (snd isContrFin1 y)

fin->nat : {n : Nat} -> Fin n -> Nat
fin->nat (i , p) = i

private
  fin->nat-iso : {n : Nat} {x y : Fin n} -> Iso (x == y) (fin->nat x == fin->nat y)
  Iso.fun fin->nat-iso = cong fin->nat
  Iso.inv fin->nat-iso = fin-i-path
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
  Iso.inv suc-fin-iso' p = fin-i-path (cong (Fin.i ∘ pred-fin) p)
  Iso.rightInv suc-fin-iso' p = isSet->Square isSetFin
  Iso.leftInv  suc-fin-iso' p = isSet->Square isSetFin

-- Single step recursion/induction for Fin (suc n)

fin-rec : {ℓ : Level} {A : Type ℓ} {n : Nat} -> A -> (Fin n -> A) -> Fin (suc n) -> A
fin-rec e f (0     , lt) = e
fin-rec e f (suc i , lt) = f (i , pred-≤ lt)

opaque
  fin-rec-suc-point : {ℓ : Level} {A : Type ℓ} {n : Nat} -> (e : A) -> (f : (Fin n -> A)) -> (i : Fin n)
                      -> (fin-rec e f (suc-fin i)) == f i
  fin-rec-suc-point e f i = cong f (fin-i-path refl)

  fin-rec-suc : {ℓ : Level} {A : Type ℓ} {n : Nat} -> (e : A) -> (f : (Fin n -> A))
                -> fin-rec e f ∘ suc-fin == f
  fin-rec-suc e f k i = fin-rec-suc-point e f i k

  fin-elim : {ℓ : Level} {n : Nat} {P : Fin (suc n) -> Type ℓ}
             -> P zero-fin
             -> ((i : Fin n) -> P (suc-fin i))
             -> (i : Fin (suc n)) -> P i
  fin-elim {P = P} z s (0     , lt) =
    transport (cong P (fin-i-path refl)) z
  fin-elim {P = P} z s (suc i , lt) =
    transport (cong P (fin-i-path refl)) (s (i , pred-≤ lt))

  fin-rec-reduce : {ℓ : Level} {A : Type ℓ} {n : Nat} -> (f : (Fin (suc n) -> A))
                   -> fin-rec (f zero-fin) (f ∘ suc-fin) == f
  fin-rec-reduce f i (0 , lt) = cong f i-path i
    where
    i-path : zero-fin == (0 , lt)
    i-path = fin-i-path refl
  fin-rec-reduce {n = n} f i (suc j , lt) = cong f i-path i
    where
    i-path : Path (Fin (suc n)) (suc j , (suc-≤ (pred-≤ lt))) (suc j , lt)
    i-path = fin-i-path refl


-- Naturals in a range

isInRange : Nat -> Nat -> Nat -> Type₀
isInRange m n i = (m ≤ i × i < n)

isPropIsInRange : {m n i : Nat} -> isProp (isInRange m n i)
isPropIsInRange = isProp× isProp-≤ isProp-≤


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
  fin->inRange->fin _ = fin-i-path refl

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


-- Map `Fin n` into `Fin (suc n)` keeping the order but skipping a particular value.
avoid-fin : {n : Nat} -> Fin (suc n) -> Fin n -> Fin (suc n)
avoid-fin {zero}  _ = suc-fin
avoid-fin {suc _}   = fin-rec (suc-fin) (\i -> fin-rec zero-fin (suc-fin ∘ avoid-fin i))

opaque
  avoid-fin-no-path : {n : Nat} {j : Fin n} (i : Fin (suc n))
                      -> avoid-fin i j != i
  avoid-fin-no-path {zero}  {j} = bot-elim (¬fin-zero j)
  avoid-fin-no-path {suc n} (0     , lt2) p =
    zero-suc-absurd (cong Fin.i (sym p))
  avoid-fin-no-path {suc n} {0     , lt}  (suc i , lt2) p =
    zero-suc-absurd (cong Fin.i p)
  avoid-fin-no-path {suc n} {suc j , lt1} (suc i , lt2) p =
    no-path (p >=> fin-i-path refl)
    where
    no-path : avoid-fin (suc i , lt2) (suc j , lt1) != suc-fin (i , pred-≤ lt2)
    no-path = avoid-fin-no-path (i , pred-≤ lt2) ∘ suc-fin-injective

  avoid-fin-inj : {n : Nat} (i : Fin (suc n))
                  -> Injective (avoid-fin i)
  avoid-fin-inj {zero} _ {x} {y} p = bot-elim (¬fin-zero x)
  avoid-fin-inj {suc n} (0     , lt) = suc-fin-injective
  avoid-fin-inj {suc n} (suc i , lt) {0      , lt1} {0      , lt2} p =
    fin-i-path refl
  avoid-fin-inj {suc n} (suc i , lt) {0      , lt1} {suc j2 , lt2} p =
    zero-suc-absurd (cong Fin.i p)
  avoid-fin-inj {suc n} (suc i , lt) {suc j1 , lt1} {0      , lt2} p =
    zero-suc-absurd (cong Fin.i (sym p))
  avoid-fin-inj {suc n} (suc i , lt) {suc j1 , lt1} {suc j2 , lt2} p =
    fin-i-path (cong suc path)
    where
    rec : Injective (avoid-fin (i , pred-≤ lt))
    rec = avoid-fin-inj (i , pred-≤ lt)

    path : j1 == j2
    path = cong Fin.i (rec (suc-fin-injective p))

-- Remove a particular number from the set
private
  remove-fin' : {n : Nat} -> (i j : Fin (suc n)) -> Fin.i i != Fin.i j -> Fin n
  remove-fin' {n = zero}    i j np = bot-elim (np (cong Fin.i (isPropFin1 i j)))
  remove-fin' {n = suc _}   (zero    , i-lt) (zero    , j-lt) np =
    bot-elim (np refl)
  remove-fin' {n = suc _}   ((suc i) , i-lt) (zero    , j-lt) np =
    zero , (trans-≤-< zero-≤ (pred-≤ i-lt))
  remove-fin' {n = suc _}   (zero    , i-lt) ((suc j) , j-lt) np =
    j , pred-≤ j-lt
  remove-fin' {n = (suc _)} ((suc i) , i-lt) ((suc j) , j-lt) np =
    suc-fin (remove-fin' (i , (pred-≤ i-lt)) (j , (pred-≤ j-lt)) (np ∘ cong suc))

  remove-fin'-inj : {n : Nat}
                    -> (i : Fin (suc n))
                    -> (j1 : Fin (suc n)) -> (j1-np : Fin.i i != Fin.i j1)
                    -> (j2 : Fin (suc n)) -> (j2-np : Fin.i i != Fin.i j2)
                    -> remove-fin' i j1 j1-np == remove-fin' i j2 j2-np
                    -> Fin.i j1 == Fin.i j2
  remove-fin'-inj {n = zero}   _ j1 j1-np j2 j2-np p =
    cong Fin.i (isPropFin1 j1 j2)
  remove-fin'-inj {n = suc _}   (zero  , i-lt) (zero   , j1-lt) j1-np (zero   , j2-lt) j2-np p =
    refl
  remove-fin'-inj {n = suc _}   (zero  , i-lt) (zero   , j1-lt) j1-np (suc j2 , j2-lt) j2-np p =
    bot-elim (j1-np refl)
  remove-fin'-inj {n = suc _}   (zero  , i-lt) (suc j1 , j1-lt) j1-np (zero   , j2-lt) j2-np p =
    bot-elim (j2-np refl)
  remove-fin'-inj {n = suc _}   (zero  , i-lt) (suc j1 , j1-lt) j1-np (suc j2 , j2-lt) j2-np p =
    cong (suc ∘ Fin.i) p
  remove-fin'-inj {n = (suc n)} (suc i , i-lt) (zero   , j1-lt) j1-np (zero   , j2-lt) j2-np p =
    refl
  remove-fin'-inj {n = (suc n)} (suc i , i-lt) (zero   , j1-lt) j1-np (suc j2 , j2-lt) j2-np p =
    zero-suc-absurd (cong Fin.i p)
  remove-fin'-inj {n = (suc n)} (suc i , i-lt) (suc j1 , j1-lt) j1-np (zero   , j2-lt) j2-np p =
    zero-suc-absurd (cong Fin.i (sym p))
  remove-fin'-inj {n = (suc n)} (suc i , i-lt) (suc j1 , j1-lt) j1-np (suc j2 , j2-lt) j2-np p =
    cong suc
      (remove-fin'-inj (i , (pred-≤ i-lt))
                       (j1 , (pred-≤ j1-lt)) (j1-np ∘ cong suc)
                       (j2 , (pred-≤ j2-lt)) (j2-np ∘ cong suc)
                       (suc-fin-injective p))

opaque
  remove-fin : {n : Nat} -> (i j : Fin (suc n)) -> i != j -> Fin n
  remove-fin i j np = remove-fin' i j (np ∘ fin-i-path)

  remove-fin-inj : {n : Nat} -> (i j1 j2 : Fin (suc n)) -> (j1-np : i != j1) -> (j2-np : i != j2)
                   -> remove-fin i j1 j1-np == remove-fin i j2 j2-np
                   -> j1 == j2
  remove-fin-inj i j1 j2 j1-np j2-np p =
    fin-i-path
      (remove-fin'-inj i j1 (j1-np ∘ fin-i-path) j2 (j2-np ∘ fin-i-path) p)

-- Combine avoid-fin and remove-fin
private
  avoid-fin-suc : {n : Nat} (i : Fin (suc n)) (j : Fin n)
                        -> avoid-fin (suc-fin i) (suc-fin j) == suc-fin (avoid-fin i j)
  avoid-fin-suc {zero}  i j = bot-elim (¬fin-zero j)
  avoid-fin-suc {suc n} i j = (\k -> suc-fin (avoid-fin (p1 k) (p2 k)))
    where
    p1 : (pred-fin (suc-fin i)) == i
    p1 = fin-i-path refl

    p2 : (pred-fin (suc-fin j)) == j
    p2 = fin-i-path refl

  avoid-fin-remove-fin'-path :
    {n : Nat} (i j : Fin (suc n)) (p : (Fin.i i) != (Fin.i j))
    -> avoid-fin i (remove-fin' i j p) == j
  avoid-fin-remove-fin'-path {zero} i j p = bot-elim (p (cong Fin.i (isPropFin1 i j)))
  avoid-fin-remove-fin'-path {suc _} (0     , lt1) (0     , lt2) p =
    bot-elim (p refl)
  avoid-fin-remove-fin'-path {suc _} (0     , lt1) (suc j , lt2) p =
    (fin-i-path refl)
  avoid-fin-remove-fin'-path {suc _} (suc i , lt1) (0     , lt2) p =
    (fin-i-path refl)
  avoid-fin-remove-fin'-path {suc n} fi@(suc i , lt1) fj@(suc j , lt2) p = ans
    where
    module _ where
    pi : Fin (suc n)
    pi = (i , pred-≤ lt1)
    pj : Fin (suc n)
    pj = (j , pred-≤ lt2)

    i-path : fi == suc-fin pi
    i-path = fin-i-path refl
    j-path : fj == suc-fin pj
    j-path = fin-i-path refl

    rec : avoid-fin pi (remove-fin' pi pj (p ∘ cong suc)) == pj
    rec = avoid-fin-remove-fin'-path pi pj (p ∘ cong suc)

    ans4 : suc-fin (avoid-fin pi (remove-fin' pi pj (p ∘ cong suc)))
           == fj
    ans4 = cong suc-fin rec >=> (sym j-path)

    ans3 : avoid-fin (suc-fin pi) (suc-fin (remove-fin' pi pj (p ∘ cong suc)))
           == fj
    ans3 = avoid-fin-suc pi (remove-fin' pi pj (p ∘ cong suc))
           >=> ans4

    ans2 : avoid-fin fi (suc-fin (remove-fin' pi pj (p ∘ cong suc)))
           == fj
    ans2 = (\k -> avoid-fin (i-path k) (suc-fin (remove-fin' pi pj (p ∘ cong suc))))
           >=> ans3

    ans : avoid-fin fi (remove-fin' fi fj p) == fj
    ans = ans2

  remove-fin'-avoid-fin-path :
    {n : Nat} (i : Fin (suc n)) (j : Fin n) (p : Fin.i i != Fin.i (avoid-fin i j))
    -> Fin.i (remove-fin' i (avoid-fin i j) p) == Fin.i j
  remove-fin'-avoid-fin-path {zero}  i j p = bot-elim (¬fin-zero j)
  remove-fin'-avoid-fin-path {suc n} (0     , lt) (j     , lt2) p = refl
  remove-fin'-avoid-fin-path {suc n} (suc i , lt) (0     , lt2) p = refl
  remove-fin'-avoid-fin-path {suc n} fi@(suc i , lt) fj@(suc j , lt2) p = ans
    where
    pi : Fin (suc n)
    pi = (i , pred-≤ lt)
    pj : Fin n
    pj = (j , pred-≤ lt2)

    avoid-path : (pred-fin (suc-fin (avoid-fin pi pj))) == (avoid-fin pi pj)
    avoid-path = fin-i-pathᵉ refl

    rec : Fin.i (remove-fin' pi (avoid-fin pi pj) (p ∘ cong suc)) == Fin.i pj
    rec = (remove-fin'-avoid-fin-path pi pj (p ∘ cong suc))

    ans : suc (Fin.i (remove-fin' pi
                       (pred-fin (suc-fin (avoid-fin pi pj)))
                       (p ∘ cong suc))) == Fin.i fj
    ans = (\k -> suc (Fin.i (remove-fin' pi (avoid-path k) (p ∘ cong suc))))
          >=> (cong suc rec)

opaque
  unfolding remove-fin

  avoid-fin-remove-fin-path :
    {n : Nat} (i j : Fin (suc n)) (p : i != j)
    -> avoid-fin i (remove-fin i j p) == j
  avoid-fin-remove-fin-path i j np =
    avoid-fin-remove-fin'-path i j (np ∘ fin-i-path)

  remove-fin-avoid-fin-path :
    {n : Nat} (i : Fin (suc n)) (j : Fin n) (p : i != (avoid-fin i j))
    -> remove-fin i (avoid-fin i j) p == j
  remove-fin-avoid-fin-path i j p =
    fin-i-path (remove-fin'-avoid-fin-path i j (p ∘ fin-i-path))
