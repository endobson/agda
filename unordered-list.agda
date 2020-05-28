{-# OPTIONS --cubical --safe --exact-split #-}

module unordered-list where

open import base
open import equality
open import hlevel
open import monoid
open import commutative-monoid

private
  variable
    ℓ : Level
    A B C : Type ℓ

infixr 5 _::_
data UnorderedList (A : Type ℓ) : Type ℓ
  where 
  [] : UnorderedList A
  _::_  : (a : A) -> UnorderedList A -> UnorderedList A
  swap : (a b : A) -> (l : UnorderedList A) -> (a :: (b :: l)) == (b :: (a :: l))
  trunc : isSet (UnorderedList A)

-- Elimination functions
module Elim {ℓ} {B : UnorderedList A -> Type ℓ}
  (trunc* : (as : UnorderedList A) -> isSet (B as))
  ([]* : B [])
  (_::*_ : (a : A) -> {as : UnorderedList A} -> B as -> B (a :: as))
  (swap* : (a1 a2 : A) -> {as : UnorderedList A} -> (bs : B as)
           -> PathP (\ i -> B (swap a1 a2 as i)) (a1 ::* (a2 ::* bs)) (a2 ::* (a1 ::* bs)))
  where

  f : (as : UnorderedList A) -> (B as)
  f [] = []*
  f (a :: as) = a ::* (f as)
  f (swap a1 a2 as i) = (swap* a1 a2 (f as) i)
  f (trunc as1 as2 p q i j) =
    isOfHLevel->isOfHLevelDep 2 trunc* (f as1) (f as2) (cong f p) (cong f q) (trunc as1 as2 p q) i j

module PropElim {ℓ} {B : UnorderedList A -> Type ℓ}
  (BProp : {as : UnorderedList A} -> isProp (B as))
  ([]* : B [])
  (_::*_ : (a : A) -> {as : UnorderedList A} -> B as -> B (a :: as))
  where

  swap* : (a1 a2 : A) -> {as : UnorderedList A} -> (bs : B as)
          -> PathP (\ i -> B (swap a1 a2 as i)) (a1 ::* (a2 ::* bs)) (a2 ::* (a1 ::* bs))
  swap* a1 a2 {as} bs =
    toPathP (BProp
              (transp (\ i -> B (swap a1 a2 as i)) i0 (a1 ::* (a2 ::* bs)))
              (a2 ::* (a1 ::* bs)))
  trunc* : (as : UnorderedList A) -> isSet (B as)
  trunc* as = isProp->isSet (BProp {as})

  f : (as : UnorderedList A) -> (B as)
  f = Elim.f {B = B} trunc* []* _::*_ swap*

module Rec {ℓ} {B : Type ℓ}
  (BSet* : isSet B)
  ([]* : B)
  (_::*_ : A -> B -> B)
  (swap* : (a0 a1 : A) (b : B) -> (a0 ::* (a1 ::* b)) == (a1 ::* (a0 ::* b)))
  where
  
  f : (as : UnorderedList A) -> B
  f [] = []*
  f (a :: as) = a ::* (f as)
  f (swap a1 a2 as i) = (swap* a1 a2 (f as) i)
  f (trunc as1 as2 p q i j) = (BSet* (f as1) (f as2) (cong f p) (cong f q) i j)
  
map : (A -> B) -> UnorderedList A -> UnorderedList B
map f = Rec.f trunc [] (\ a -> f a ::_) (\ a0 a1 -> (swap (f a0) (f a1)))

_++_ : (UnorderedList A) -> (UnorderedList A) -> (UnorderedList A)
_++_ as bs = Rec.f trunc bs _::_ swap as

++-right-[] : ∀ (as : UnorderedList A) -> as ++ [] == as
++-right-[] =
  PropElim.f
    (trunc _ _)
    refl
    (\ a p i -> a :: p i)

++-extract-right : ∀ (as : UnorderedList A) (b : A) (bs : UnorderedList A)
                     -> as ++ (b :: bs) == b :: (as ++ bs)
++-extract-right {A = A} as b bs = 
  PropElim.f
    (trunc _ _)
    refl
    _::*_
    as
  where
  _::*_ : ∀ (a : A) {as : UnorderedList A} 
           -> (as ++ (b :: bs)) == b :: (as ++ bs)
           -> a :: (as ++ (b :: bs)) == b :: (a :: as ++ bs)
  _::*_ a p = (\i -> a :: p i) >=> (swap a b _)


++-commute : ∀ (as : UnorderedList A) (bs : UnorderedList A)
               -> as ++ bs == bs ++ as
++-commute {A = A} as bs = 
  PropElim.f
    (trunc _ _)
    (++-right-[] as)
    _::*_
    bs
  where
  _::*_ : ∀ (b : A) {bs : UnorderedList A} 
           -> (as ++ bs) == (bs ++ as)
           -> (as ++ (b :: bs)) == b :: (bs ++ as)
  _::*_ b {bs} p =  (++-extract-right as b bs) >=> (cong (b ::_) p)

++-assoc : ∀ (as : UnorderedList A) (bs : UnorderedList A) (cs : UnorderedList A)
             -> (as ++ bs) ++ cs == as ++ (bs ++ cs)
++-assoc {A = A} as bs cs = 
  PropElim.f
    (trunc _ _)
    refl
    _::*_
    as
  where
  _::*_ : ∀ (a : A) {as : UnorderedList A} 
           -> (as ++ bs) ++ cs == as ++ (bs ++ cs)
           -> (a :: as ++ bs) ++ cs == a :: as ++ (bs ++ cs)
  _::*_ a p i = a :: p i



instance
  MonoidUnorderedList : Monoid (UnorderedList A)
  MonoidUnorderedList = record
    { ε = []
    ; _∙_ = _++_
    ; ∙-assoc = (\ {as} {bs} {cs} -> ++-assoc as bs cs)
    ; ∙-left-ε = refl
    ; ∙-right-ε = (\ {l} -> ++-right-[] l)
    }

  CommutativeMonoidUnorderedList : CommutativeMonoid (UnorderedList A)
  CommutativeMonoidUnorderedList = record
    { ∙-commute = (\ {as} {bs} -> ++-commute as bs )
    }
