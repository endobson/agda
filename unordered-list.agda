{-# OPTIONS --cubical --safe --exact-split #-}

module unordered-list where

open import base
open import commutative-monoid
open import equality
open import hlevel
open import monoid
open import nat
open import relation
open import sigma

private
  variable
    ℓ : Level
    A B C : Type ℓ

infixr 5 _::_
data UList (A : Type ℓ) : Type ℓ
  where
  [] : UList A
  _::_  : (a : A) -> UList A -> UList A
  swap : (a b : A) -> (l : UList A) -> (a :: (b :: l)) == (b :: (a :: l))
  trunc : isSet (UList A)

-- Elimination functions

module Elim {ℓ} {B : UList A -> Type ℓ}
  (trunc* : (as : UList A) -> isSet (B as))
  ([]* : B [])
  (_::*_ : (a : A) -> {as : UList A} -> B as -> B (a :: as))
  (swap* : (a1 a2 : A) -> {as : UList A} -> (bs : B as)
           -> PathP (\ i -> B (swap a1 a2 as i)) (a1 ::* (a2 ::* bs)) (a2 ::* (a1 ::* bs)))
  where

  f : (as : UList A) -> (B as)
  f [] = []*
  f (a :: as) = a ::* (f as)
  f (swap a1 a2 as i) = (swap* a1 a2 (f as) i)
  f (trunc as1 as2 p q i j) =
    isOfHLevel->isOfHLevelDep 2 trunc* (f as1) (f as2) (cong f p) (cong f q) (trunc as1 as2 p q) i j

module PropElim {ℓ} {B : UList A -> Type ℓ}
  (BProp : {as : UList A} -> isProp (B as))
  ([]* : B [])
  (_::*_ : (a : A) -> {as : UList A} -> B as -> B (a :: as))
  where

  swap* : (a1 a2 : A) -> {as : UList A} -> (bs : B as)
          -> PathP (\ i -> B (swap a1 a2 as i)) (a1 ::* (a2 ::* bs)) (a2 ::* (a1 ::* bs))
  swap* a1 a2 {as} bs =
    toPathP (BProp
              (transp (\ i -> B (swap a1 a2 as i)) i0 (a1 ::* (a2 ::* bs)))
              (a2 ::* (a1 ::* bs)))
  trunc* : (as : UList A) -> isSet (B as)
  trunc* as = isProp->isSet (BProp {as})

  f : (as : UList A) -> (B as)
  f = Elim.f {B = B} trunc* []* _::*_ swap*

module Rec {ℓ} {B : Type ℓ}
  (BSet* : isSet B)
  ([]* : B)
  (_::*_ : A -> B -> B)
  (swap* : (a0 a1 : A) (b : B) -> (a0 ::* (a1 ::* b)) == (a1 ::* (a0 ::* b)))
  where

  f : (as : UList A) -> B
  f [] = []*
  f (a :: as) = a ::* (f as)
  f (swap a1 a2 as i) = (swap* a1 a2 (f as) i)
  f (trunc as1 as2 p q i j) = (BSet* (f as1) (f as2) (cong f p) (cong f q) i j)

-- Basic manipulation functions

map : (A -> B) -> UList A -> UList B
map f = Rec.f trunc [] (\ a -> f a ::_) (\ a0 a1 -> (swap (f a0) (f a1)))

_++_ : (UList A) -> (UList A) -> (UList A)
_++_ as bs = Rec.f trunc bs _::_ swap as

length : (l : UList A) -> Nat
length = Rec.f isSetNat 0 (\ _ -> 1 +'_) (\ _ _ _ -> refl)

++-right-[] : ∀ (as : UList A) -> as ++ [] == as
++-right-[] =
  PropElim.f
    (trunc _ _)
    refl
    (\ a p i -> a :: p i)

++-extract-right : ∀ (as : UList A) (b : A) (bs : UList A)
                     -> as ++ (b :: bs) == b :: (as ++ bs)
++-extract-right {A = A} as b bs =
  PropElim.f
    (trunc _ _)
    refl
    _::*_
    as
  where
  _::*_ : ∀ (a : A) {as : UList A}
           -> (as ++ (b :: bs)) == b :: (as ++ bs)
           -> a :: (as ++ (b :: bs)) == b :: (a :: as ++ bs)
  _::*_ a p = (cong (a ::_) p) >=> (swap a b _)

++-commute : ∀ (as : UList A) (bs : UList A) -> as ++ bs == bs ++ as
++-commute {A = A} as bs =
  PropElim.f
    (trunc _ _)
    (++-right-[] as)
    _::*_
    bs
  where
  _::*_ : ∀ (b : A) {bs : UList A}
           -> (as ++ bs) == (bs ++ as)
           -> (as ++ (b :: bs)) == b :: (bs ++ as)
  _::*_ b {bs} p =  (++-extract-right as b bs) >=> (cong (b ::_) p)

++-assoc : ∀ (as : UList A) (bs : UList A) (cs : UList A)
             -> (as ++ bs) ++ cs == as ++ (bs ++ cs)
++-assoc {A = A} as bs cs =
  PropElim.f
    (trunc _ _)
    refl
    _::*_
    as
  where
  _::*_ : ∀ (a : A) {as : UList A}
           -> (as ++ bs) ++ cs == as ++ (bs ++ cs)
           -> (a :: as ++ bs) ++ cs == a :: as ++ (bs ++ cs)
  _::*_ a p i = a :: p i

-- Monoid instances

instance
  UListMonoid : Monoid (UList A)
  UListMonoid = record
    { ε = []
    ; _∙_ = _++_
    ; ∙-assoc = (\ {as} {bs} {cs} -> ++-assoc as bs cs)
    ; ∙-left-ε = refl
    ; ∙-right-ε = (\ {l} -> ++-right-[] l)
    }

  UListCommMonoid : CommMonoid (UList A)
  UListCommMonoid = record
    { ∙-commute = (\ {as} {bs} -> ++-commute as bs )
    }

concat : {{M : CommMonoid A}} -> isSet A -> UList A -> A
concat {A = A} {{M = M}} h =
  Rec.f h ε _∙_ swap*
  where
  open CommMonoid M
  swap* : (a0 a1 : A) (a : A) -> (a0 ∙ (a1 ∙ a)) == (a1 ∙ (a0 ∙ a))
  swap* a0 a1 a = (sym (∙-assoc {a0})) >=> ∙-left (∙-commute {a0} {a1}) >=> ∙-assoc {a1}

concatʰ : {{M : CommMonoid A}} -> {h : isSet A}
  -> CommMonoidʰ (concat {{M}} h)
concatʰ {A = A} {{M = M}} {h} = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  open CommMonoid M

  preserves-∙ : (xs ys : UList A) -> concat h (xs ++ ys) == (concat h xs) ∙ (concat h ys)
  preserves-∙ xs ys = PropElim.f (h _ _) (sym ∙-left-ε) _::*_ xs
    where
    _::*_ : ∀ (x : A) {xs : UList A}
             -> (concat h (xs ++ ys)) == (concat h xs) ∙ (concat h ys)
             -> (concat h (x :: (xs ++ ys))) == (concat h (x :: xs)) ∙ (concat h ys)
    x ::* p = (\i -> x ∙ p i) >=> sym ∙-assoc

mapʰ : {f : A -> B} -> CommMonoidʰ (map f)
mapʰ {A = A} {f = f} = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  preserves-∙ : (xs ys : UList A) -> map f (xs ++ ys) == (map f xs) ++ (map f ys)
  preserves-∙ xs ys = PropElim.f (trunc _ _) refl _::*_ xs
    where
    _::*_ : ∀ (x : A) {xs : UList A}
             -> (map f (xs ++ ys)) == (map f xs) ++ (map f ys)
             -> (map f (x :: (xs ++ ys))) == (map f (x :: xs)) ++ (map f ys)
    (x ::* p) i = (f x) :: p i

lengthʰ : CommMonoidʰ {D₁ = UList A} length
lengthʰ = record
  { preserves-ε = refl
  ; preserves-∙ = preserves-∙
  }
  where
  preserves-∙ : (xs ys : UList A) -> length (xs ++ ys) == (length xs) +' (length ys)
  preserves-∙ {A = A} xs ys = PropElim.f (isSetNat _ _) refl _::*_ xs
    where
    _::*_ : ∀ (x : A) {xs : UList A}
             -> (length (xs ++ ys)) == (length xs) +' (length ys)
             -> (length ((x :: xs) ++ ys)) == (length (x :: xs)) +' (length ys)
    (_::*_) _ = cong suc
