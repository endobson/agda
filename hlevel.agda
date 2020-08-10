{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel where

open import base
open import equality
open import equivalence
open import isomorphism
open import relation
open import sigma
open import sum

open import hlevel.base public

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A A₁ A₂ : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> B a -> Type ℓ
    D : (a : A) -> (b : B a) -> C a b -> Type ℓ

-- h-level for Path Types

isProp->isContrPath : isProp A -> (x y : A) -> isContr (x == y)
isProp->isContrPath h x y = (h x y , isProp->isSet h x y (h x y))

isContr->isContrPath : isContr A -> (x y : A) -> isContr (x == y)
isContr->isContrPath h = isProp->isContrPath (isContr->isProp h)

isOfHLevelPath' : (n : Nat) → isOfHLevel (suc n) A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath' 0 = isProp->isContrPath
isOfHLevelPath' (suc _) h x y = h x y

isOfHLevelPath : (n : Nat) → isOfHLevel n A → (x y : A) → isOfHLevel n (x ≡ y)
isOfHLevelPath 0 = isContr->isContrPath
isOfHLevelPath (suc n) h x y = isOfHLevelSuc n (isOfHLevelPath' n h x y)

-- h-level for Π Types

isOfHLevelΠ :
  (n : Nat) -> ((x : A) -> (isOfHLevel n (B x))) -> isOfHLevel n ((x : A) -> B x)
isOfHLevelΠ {A = A} {B = B} 0 h = (\x -> fst (h x)) , (\ f i y -> (snd (h y)) (f y) i)
isOfHLevelΠ {A = A} {B = B} 1 h f g i a = h a (f a) (g a) i
isOfHLevelΠ {A = A} {B = B} (suc (suc n)) h f g =
   subst (isOfHLevel (suc n)) funExtPath (isOfHLevelΠ (suc n) (\a -> h a (f a) (g a)))

isPropΠ : ((x : A) -> isProp (B x)) -> isProp ((x : A) -> (B x))
isPropΠ = isOfHLevelΠ 1

isPropΠ2 : ((x : A) -> (y : B x) -> isProp (C x y)) -> isProp ((x : A) -> (y : B x) -> C x y)
isPropΠ2 h = isPropΠ (\ a -> isPropΠ (h a))

isPropΠ3 : ((x : A) -> (y : B x) -> (z : (C x y)) -> isProp (D x y z))
           -> isProp ((x : A) -> (y : B x) -> (z : C x y) -> D x y z)
isPropΠ3 h = isPropΠ (\ a -> isPropΠ (\ b -> isPropΠ (h a b)))

isSetΠ : ((x : A) -> isSet (B x)) -> isSet ((x : A) -> (B x))
isSetΠ = isOfHLevelΠ 2

-- h-level for Σ types

isContrΣ : isContr A -> ((x : A) -> isContr (B x)) -> isContr (Σ A B)
isContrΣ {A = A} {B = B} (a , p) q = elem , path-f
  where
  elem : Σ A B
  elem = (a , q a .fst)
  h : (a : A) (b : B a) -> (q a) .fst == b
  h a b = (q a) .snd b

  path-f : (s2 : (Σ A B)) -> elem == s2
  path-f s2 i = (p (s2 .fst) i) , path-b i
    where
    path-b : PathP (\k -> B (p (s2 .fst) k)) (q a .fst) (s2 .snd)
    path-b i = h (p (s2 .fst) i) (transp (\ j -> B (p (s2 .fst) (i ∨ ~ j))) i (s2 .snd)) i

ΣProp== : ((a : A) -> isProp (B a)) -> {u v : Σ A B} (p : u .fst == v .fst) -> u == v
ΣProp== {B = B} pB {u} {v} p i = (p i , isProp->PathP (\ i -> pB (p i)) (u .snd) (v .snd) i)

ΣProp==-equiv : (pB : (a : A) -> isProp (B a)) {u v : Σ A B} -> isEquiv (ΣProp== pB {u} {v})
ΣProp==-equiv {A = A} pB {u} {v} = isoToIsEquiv (iso (ΣProp== pB) (cong fst) sq (\ _ -> refl))
  where
  sq : (p : u == v) -> ΣProp== pB (cong fst p) == p
  sq p j i = (p i .fst) , isProp->PathP (\ i -> isOfHLevelPath 1 (pB (fst (p i)))
                                                  (ΣProp== pB {u} {v} (cong fst p) i .snd)
                                                  (p i .snd))
                                        refl refl i j

isPropΣ : isProp A -> ((a : A) -> isProp (B a)) -> isProp (Σ A B)
isPropΣ pA pB (a1 , _) (a2 , _) = ΣProp== pB (pA a1 a2)

isOfHLevelΣ : (n : Nat) -> isOfHLevel n A -> ((x : A) -> isOfHLevel n (B x)) -> isOfHLevel n (Σ A B)
isOfHLevelΣ 0 = isContrΣ
isOfHLevelΣ 1 = isPropΣ
isOfHLevelΣ {B = B} (suc (suc n)) hA hB x0 x1 =
  let hΣ : isOfHLevel (suc n) (x0 Σ==T x1)
      hΣ = isOfHLevelΣ (suc n) (hA (fst x0) (fst x1))
                       (\ p -> (hB (p i1)) (subst B p (snd x0)) (snd x1))
  in transport (\i -> isOfHLevel (suc n) (pathSigma==sigmaPath x0 x1 (~ i))) hΣ

isSetΣ : isSet A -> ((a : A) -> isSet (B a)) -> isSet (Σ A B)
isSetΣ = isOfHLevelΣ 2


isProp× : isProp A₁ -> isProp A₂ -> isProp (A₁ × A₂)
isProp× pA₁ pA₂ = isPropΣ pA₁ (\_ -> pA₂)

-- h-level for Top

isContrTop : isContr Top
isContrTop = (tt , \_ -> refl)

isPropTop : isProp Top
isPropTop tt tt = refl

-- h-level for Bot and ¬

isPropBot : isProp Bot
isPropBot x _ = bot-elim x

isProp¬ : (A : Type ℓ) -> isProp (¬ A)
isProp¬ _ ¬x ¬y i x = isPropBot (¬x x) (¬y x) i

-- Hedbergs Theorem

private
  Stable==->isSet : ((x y : A) -> Stable (x == y)) -> isSet A
  Stable==->isSet {A = A} st a0 a1 p1 p2 j i =
    let
     -- Push through the stabilizer
     f : (x : A) -> a0 == x -> a0 == x
     f x p = st a0 x (\h -> h p)
     -- Pushing through the stabilizer is a constant function
     fIsConst : (x : A) -> (p q : a0 == x) -> f x p == f x q
     fIsConst x p q i = st a0 x (isProp¬ _ (\h -> h p) (\h -> h q) i)
     -- Shows that we can extend to any path starting from refl
     rem : (p : a0 == a1) -> PathP (\i -> a0 == p i) (f a0 refl) (f a1 p)
     rem p j = f (p j) (\ i -> p (i ∧ j))

    in hcomp (\ k -> (\ { (i = i0) -> f a0 refl k
                        ; (i = i1) -> fIsConst a1 p1 p2 j k
                        ; (j = i0) -> rem p1 i k
                        ; (j = i1) -> rem p2 i k})) a0

Discrete->isSet : Discrete A -> isSet A
Discrete->isSet d = Stable==->isSet (\ x y -> Dec->Stable (d x y))

-- h-level for ⊎ types

isSet⊎ : Discrete A₁ -> Discrete A₂ -> isSet (A₁ ⊎ A₂)
isSet⊎ da db = Discrete->isSet (Discrete⊎ da db)

-- h-level for Dec types

isPropDec : isProp A -> isProp (Dec A)
isPropDec ha (yes a1) (yes a2) = cong yes (ha a1 a2)
isPropDec ha (yes a)  (no ¬a)  = bot-elim (¬a a)
isPropDec ha (no ¬a)  (yes a)  = bot-elim (¬a a)
isPropDec ha (no ¬a1) (no ¬a2) = cong no (isProp¬ _ ¬a1 ¬a2)

-- Sets make any square

isSet->Square : {ℓ : Level} {A : Type ℓ}
                {a₀₀ : A} {a₀₁ : A} {a₀₋ : Path A a₀₀ a₀₁}
                {a₁₀ : A} {a₁₁ : A} {a₁₋ : Path A a₁₀ a₁₁}
                {a₋₀ : Path A a₀₀ a₁₀}
                {a₋₁ : Path A a₀₁ a₁₁} -> isSet A -> Square a₀₋ a₁₋ a₋₀ a₋₁
isSet->Square h = isProp->PathP (\ k -> (h _ _)) _ _

isProp->Square : {ℓ : Level} {A : Type ℓ}
                {a₀₀ : A} {a₀₁ : A} {a₀₋ : Path A a₀₀ a₀₁}
                {a₁₀ : A} {a₁₁ : A} {a₁₋ : Path A a₁₀ a₁₁}
                {a₋₀ : Path A a₀₀ a₁₀}
                {a₋₁ : Path A a₀₁ a₁₁} -> isProp A -> Square a₀₋ a₁₋ a₋₀ a₋₁
isProp->Square h = isProp->PathP (\ _ -> (isProp->isSet h _ _)) _ _
