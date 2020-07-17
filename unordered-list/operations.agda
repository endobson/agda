{-# OPTIONS --cubical --safe --exact-split #-}

module unordered-list.operations where

open import base
open import commutative-monoid
open import equality
open import functions
open import hlevel
open import monoid
open import nat
open import unordered-list.base

private
  variable
    ℓ : Level
    A B C : Type ℓ

map : (A -> B) -> UList A -> UList B
map f = UListElim.rec trunc [] (\ a -> f a ::_) (\ a0 a1 -> (swap (f a0) (f a1)))

double-map : (f : B -> C) (g : A -> B) (as : UList A)
             -> map f (map g as) == map (f ∘ g) as
double-map {A = A} f g as = UListElim.prop (trunc _ _) refl ::* as
  where
  ::* : (a : A) {as : UList A}
        -> map f (map g as) == map (f ∘ g) as
        -> map f (map g (a :: as)) == map (f ∘ g) (a :: as)
  ::* a p = cong (f (g a) ::_) p

_++_ : (UList A) -> (UList A) -> (UList A)
_++_ as bs = UListElim.rec trunc bs _::_ swap as

length : (l : UList A) -> Nat
length = UListElim.rec isSetNat 0 (\ _ -> 1 +'_) (\ _ _ _ -> refl)

++-right-[] : ∀ (as : UList A) -> as ++ [] == as
++-right-[] =
  UListElim.prop
    (trunc _ _)
    refl
    (\ a p i -> a :: p i)

++-extract-right : ∀ (as : UList A) (b : A) (bs : UList A)
                     -> as ++ (b :: bs) == b :: (as ++ bs)
++-extract-right {A = A} as b bs =
  UListElim.prop
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
  UListElim.prop
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
  UListElim.prop
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
  UListElim.rec h ε _∙_ swap*
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
  preserves-∙ xs ys = UListElim.prop (h _ _) (sym ∙-left-ε) _::*_ xs
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
  preserves-∙ xs ys = UListElim.prop (trunc _ _) refl _::*_ xs
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
  preserves-∙ {A = A} xs ys = UListElim.prop (isSetNat _ _) refl _::*_ xs
    where
    _::*_ : ∀ (x : A) {xs : UList A}
             -> (length (xs ++ ys)) == (length xs) +' (length ys)
             -> (length ((x :: xs) ++ ys)) == (length (x :: xs)) +' (length ys)
    (_::*_) _ = cong suc

-- More properties, now using the CommMonoid structure

length0->[] : {as : UList A} -> (length as) == 0 -> as == []
length0->[] {as = as} = UListElim.prop PProp []* _::*_ as
  where
  P : (as : UList A) -> Type _
  P as = (length as) == 0 -> as == []

  PProp : {as : UList A} -> isProp (P as)
  PProp {as} = isPropΠ (\ _ -> (trunc _ _))

  []* : P []
  []* _ = refl

  _::*_ : (a : A) -> {as : UList A} -> P as -> P (a :: as)
  (a ::* _) p = bot-elim (zero-suc-absurd (sym p))

++-left-id->[] : {as bs : UList A} -> as ++ bs == bs -> as == []
++-left-id->[] {as = as} {bs = bs} p =
  length0->[] (transport (sym (+'-right-path _)) (sym (preserves-∙ as bs) >=> (cong length p)))
  where
  open CommMonoidʰ lengthʰ

++-right-id->[] : {as bs : UList A} -> as ++ bs == as -> bs == []
++-right-id->[] {as = as} {bs = bs} p =
  length0->[] (transport (sym (+'-right-path _))
                         (+'-commute {length bs} >=> sym (preserves-∙ as bs) >=> (cong length p)))
  where
  open CommMonoidʰ lengthʰ

as++bs==[]->as==[] : {as bs : UList A} -> as ++ bs == [] -> as == []
as++bs==[]->as==[] {as = as} {bs = bs} p =
    (length0->[] (m+'n==0->m==0 (sym (preserves-∙ as bs) >=> (cong length p))))
  where
  open CommMonoidʰ lengthʰ

as++bs==[]->bs==[] : {as bs : UList A} -> as ++ bs == [] -> bs == []
as++bs==[]->bs==[] {as = as} {bs = bs} p = as++bs==[]->as==[] (++-commute bs as >=> p)
