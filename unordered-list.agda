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

-- Count and Remove

module _ (discA : Discrete A) where

 count : (x : A) -> UList A -> Nat
 count x = Rec.f isSetNat 0 _::*_ swap*
   where
   _::*_ : (a : A) -> Nat -> Nat
   (a ::* n) with (discA x a)
   ...          | (yes _)     = suc n
   ...          | (no  _)     = n
   swap* : (a1 : A) (a2 : A) -> (n : Nat) -> (a1 ::* (a2 ::* n)) == (a2 ::* (a1 ::* n))
   swap* a1 a2 n with (discA x a1) | (discA x a2)
   ...              | (yes _)      | (yes _)      = refl
   ...              | (yes _)      | (no  _)      = refl
   ...              | (no  _)      | (yes _)      = refl
   ...              | (no  _)      | (no  _)      = refl

 count-== : {x : A} {a : A} (as : UList A) -> (x == a) -> count x (a :: as) == suc (count x as)
 count-== {x} {a} as x==a with (discA x a)
 ...                         | (yes _)     = refl
 ...                         | (no x!=a)   = bot-elim (x!=a x==a)

 count-!= : {x : A} {a : A} (as : UList A) -> (x != a) -> count x (a :: as) == (count x as)
 count-!= {x} {a} as x!=a with (discA x a)
 ...                         | (yes x==a)  = bot-elim (x!=a x==a)
 ...                         | (no _)   = refl

 remove1 : (x : A) -> UList A -> UList A
 remove1 x [] = []
 remove1 x (a :: as) with (discA x a)
 ...                    | (yes _)     = as
 ...                    | (no  _)     = a :: (remove1 x as)
 remove1 x (swap a1 a2 as i) = path i
   where
   path : (remove1 x (a1 :: (a2 :: as))) == (remove1 x (a2 :: (a1 :: as)))
   path with (discA x a1) | (discA x a2)
   ... | (yes p1) | (yes p2) = (\i -> ((sym p2 >=> p1) i) :: as)
   ... | (yes p1) | (no _) = (\i -> a2 :: (inner (~ i)))
     where
     inner : remove1 x (a1 :: as) == as
     inner with (discA x a1)
     ...      | (yes _)      = refl
     ...      | (no ¬p1)     = bot-elim (¬p1 p1)
   ... | (no _) | (yes p2) = (\i -> a1 :: (inner i))
     where
     inner : remove1 x (a2 :: as) == as
     inner with (discA x a2)
     ...      | (yes _)      = refl
     ...      | (no ¬p2)     = bot-elim (¬p2 p2)
   ... | (no ¬p1) | (no ¬p2) = (\i -> a1 :: p i) ∙∙ swap a1 a2 (remove1 x as) ∙∙ (\i -> a2 :: q (~ i))
     where
     p : (remove1 x (a2 :: as)) == a2 :: (remove1 x as)
     p with (discA x a2)
     ...  | (yes p2) = bot-elim (¬p2 p2)
     ...  | (no _)  = refl
     q : (remove1 x (a1 :: as)) == a1 :: (remove1 x as)
     q with (discA x a1)
     ...  | (yes p1) = bot-elim (¬p1 p1)
     ...  | (no _)  = refl
 remove1 x (trunc as1 as2 p q i j) =
   (trunc (remove1 x as1) (remove1 x as2) (cong (remove1 x) p) (cong (remove1 x) q) i j)

 remove1-== : {x : A} {a : A} (as : UList A) -> (x == a) -> remove1 x (a :: as) == as
 remove1-== {x} {a} as x==a with (discA x a)
 ...                         | (yes _)     = refl
 ...                         | (no x!=a)   = bot-elim (x!=a x==a)

 remove1-!= : {x : A} {a : A} (as : UList A) -> (x != a) -> remove1 x (a :: as) == a :: (remove1 x as)
 remove1-!= {x} {a} as x!=a with (discA x a)
 ...                         | (yes x==a)  = bot-elim (x!=a x==a)
 ...                         | (no _)   = refl
