{-# OPTIONS --cubical --safe --exact-split #-}

module hlevel.base where

open import base
open import cubical
open import equality

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    A A₁ A₂ : Type ℓ
    B : A -> Type ℓ
    C : (a : A) -> (B a) -> Type ℓ
    D : (a : A) -> (b : B a) -> (C a b) -> Type ℓ
    E : (a : A) -> (b : B a) -> (c : (C a b)) -> (D a b c) -> Type ℓ
    F : (a : A) -> (b : B a) -> (c : (C a b)) -> (d : (D a b c)) -> (E a b c d) -> Type ℓ

-- Basic isOfHLevel

-- Deifined in core
-- isContr : Type ℓ -> Type ℓ
-- isContr A = Σ[ x ∈ A ] ((y : A) -> x == y)

isProp : Type ℓ -> Type ℓ
isProp A = (x y : A) -> x == y

isSet : Type ℓ -> Type ℓ
isSet A = (x y : A) -> isProp (x == y)

isOfHLevel : Nat -> Type ℓ -> Type ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = ∀ (x y : A) -> isOfHLevel (suc n) (x == y)

abstract
  -- Increasing h-level

  isContr->isProp : isContr A -> isProp A
  isContr->isProp (x , p) a b i =
    hcomp (\j -> (\ { (i = i0) -> p a j
                    ; (i = i1) -> p b j})) x

  isProp->isSet : isProp A -> isSet A
  isProp->isSet h a0 a1 p1 p2 j i =
    hcomp (\k -> (\ { (i = i0) -> h a0 a0 k
                    ; (i = i1) -> h a0 a1 k
                    ; (j = i0) -> h a0 (p1 i) k
                    ; (j = i1) -> h a0 (p2 i) k })) a0

  isOfHLevelSuc : (n : Nat) → isOfHLevel n A → isOfHLevel (suc n) A
  isOfHLevelSuc 0 = isContr->isProp
  isOfHLevelSuc 1 = isProp->isSet
  isOfHLevelSuc (suc (suc n)) h a b = isOfHLevelSuc (suc n) (h a b)

  isProp->isOfHLevelSuc : (n : Nat) -> isProp A -> isOfHLevel (suc n) A
  isProp->isOfHLevelSuc 0 p = p
  isProp->isOfHLevelSuc (suc n) p = isOfHLevelSuc (suc n) (isProp->isOfHLevelSuc n p)

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

-- Dependent h-level

abstract
  private
    module _ {A : I -> Type ℓ} {x : A i0} {y : A i1} where
      toPathP : transp A i0 x == y -> PathP A x y
      toPathP p i = hcomp (\ j -> (\ { (i = i0) -> x
                                     ; (i = i1) -> p j}))
                          (transp (\ j -> A (i ∧ j)) (~ i) x)
  isProp->PathP : {B : I -> Type ℓ} -> ((i : I) -> isProp (B i)) -> {b0 : (B i0)} {b1 : (B i1)}
                  -> PathP (\i -> B i) b0 b1
  isProp->PathP hB = toPathP (hB _ _ _)

  isProp->PathPᵉ : {B : I -> Type ℓ} -> ((i : I) -> isProp (B i)) -> (b0 : (B i0)) (b1 : (B i1))
                  -> PathP (\i -> B i) b0 b1
  isProp->PathPᵉ hB _ _ = isProp->PathP hB

isOfHLevelDep : Nat -> {A : Type ℓ₁} -> (B : A -> Type ℓ₂) -> Type (ℓ-max ℓ₁ ℓ₂)
isOfHLevelDep 0 {A = A} B =
  {a : A} -> Σ[ b ∈ B a ] ({a' : A} (b' : B a') (p : a == a') -> PathP (\i -> (B (p i))) b b')
isOfHLevelDep 1 {A = A} B =
  {a0 a1 : A} (b0 : B a0) (b1 : B a1) (p : a0 == a1) -> PathP (\i -> B (p i)) b0 b1
isOfHLevelDep (suc (suc n)) {A = A} B =
  {a0 a1 : A} (b0 : B a0) (b1 : B a1)
  -> isOfHLevelDep (suc n) {A = a0 == a1} (\p -> PathP (\i -> B (p i)) b0 b1)

abstract
  isOfHLevel->isOfHLevelDep :
    (n : Nat) -> (h : (a : A) -> isOfHLevel n (B a)) -> isOfHLevelDep n {A = A} B
  isOfHLevel->isOfHLevelDep 0 h {a} =
    (h a .fst , (\ b p -> isProp->PathP (\i -> isContr->isProp (h (p i)))))
  isOfHLevel->isOfHLevelDep 1 h = (\ b0 b1 p -> isProp->PathP (\i -> (h (p i))))
  isOfHLevel->isOfHLevelDep {A = A} {B = B} (suc (suc n)) h {a0} {a1} b0 b1 =
    isOfHLevel->isOfHLevelDep (suc n) (\ p -> helper a1 p b1)
    where
    helper : (a1 : A) (p : a0 == a1) (b1 : B a1) ->
      isOfHLevel (suc n) (PathP (\i -> (B (p i))) b0 b1)
    helper a1 p b1 = J (\ a1 p -> ∀ b1 -> isOfHLevel (suc n) (PathP (\i -> (B (p i))) b0 b1))
                       (\ _ -> h _ _ _) p b1

-- ΣProp==/isPropΠ since they are simple and needed for some of the meta hlevel cases
abstract
  ΣProp== : ((a : A) -> isProp (B a)) -> {u v : Σ A B} (p : u .fst == v .fst) -> u == v
  ΣProp== {B = B} pB {u} {v} p i = (p i , isProp->PathPᵉ (\ i -> pB (p i)) (u .snd) (v .snd) i)

  section-ΣProp== : (pB : (x : A) → isProp (B x)) {u v : Σ A B} ->
                    (∀ x -> (ΣProp== pB {u} {v} (\j -> fst (x j))) == x)
  section-ΣProp== {A = A} pB {u} {v} p j i =
    (p i .fst) , isProp->PathPᵉ (\ i -> isOfHLevelPath 1 (pB (fst (p i)))
                                          (ΣProp== pB {u} {v} (\j -> fst (p j)) i .snd)
                                          (p i .snd))
                                          refl refl i j

abstract

  isPropΠ : ((x : A) -> isProp (B x)) -> isProp ((x : A) -> (B x))
  isPropΠ h f g i a = h a (f a) (g a) i

  isPropΠ2 : ((x : A) -> (y : B x) -> isProp (C x y)) -> isProp ((x : A) -> (y : B x) -> C x y)
  isPropΠ2 h = isPropΠ (\ a -> isPropΠ (h a))

  isPropΠ3 : ((x : A) -> (y : B x) -> (z : (C x y)) -> isProp (D x y z))
             -> isProp ((x : A) -> (y : B x) -> (z : C x y) -> D x y z)
  isPropΠ3 h = isPropΠ (\ a -> isPropΠ (\ b -> isPropΠ (h a b)))

  isPropΠ4 : ((x : A) -> (y : B x) -> (z : (C x y)) -> (w : (D x y z)) -> isProp (E x y z w))
             -> isProp ((x : A) -> (y : B x) -> (z : C x y) -> (w : D x y z) -> E x y z w)
  isPropΠ4 h = isPropΠ (\ a -> isPropΠ (\ b -> isPropΠ (\ c -> (isPropΠ (h a b c)))))

  isPropΠ5 : ((x : A) -> (y : B x) -> (z : (C x y)) -> (w : (D x y z)) -> (v : (E x y z w)) ->
              (isProp (F x y z w v)))
             -> isProp ((x : A) -> (y : B x) -> (z : C x y) -> (w : D x y z) -> (v : E x y z w) ->
                        (F x y z w v))
  isPropΠ5 h = isPropΠ (\a -> isPropΠ4 (h a))



  -- hlevel of isOfHLevel

  isProp-isContr : isProp (isContr A)
  isProp-isContr c1@(a1 , f1) (a2 , f2) =
    ΣProp== (\_ -> (isPropΠ (\_ -> (isProp->isSet (isContr->isProp c1)) _ _))) (f1 a2)

  isProp-isOfHLevel : (n : Nat) -> isProp (isOfHLevel n A)
  isProp-isOfHLevel 0 = isProp-isContr
  isProp-isOfHLevel 1 pa1 pa2 i a1 a2 = isOfHLevelPath 1 pa1 a1 a2 (pa1 a1 a2) (pa2 a1 a2) i
  isProp-isOfHLevel (suc (suc n)) ha1 ha2 i a1 a2 = isProp-isOfHLevel (suc n) (ha1 a1 a2) (ha2 a1 a2) i

  isProp-isProp : isProp (isProp A)
  isProp-isProp = isProp-isOfHLevel 1

  isProp-isSet : isProp (isSet A)
  isProp-isSet = isProp-isOfHLevel 2

  -- hlevel of equivalences (Needed early for univalence)

  isProp-isEquiv : {f : A₁ -> A₂} -> isProp (isEquiv f)
  isProp-isEquiv e1 e2 j .equiv-proof a2 =
    isProp-isContr (e1 .equiv-proof a2) (e2 .equiv-proof a2) j

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

-- Implicit hlevels
record isSet' (A : Type ℓ) : Type ℓ where
  field
    f : isSet A
