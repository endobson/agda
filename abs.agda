{-# OPTIONS --cubical --safe --exact-split #-}

module abs where

open import additive-group
open import additive-group.instances.int
open import base
open import equality
open import int
open import nat
open import ring
open import ring.implementations.int
open import semiring


data NonNegIntRec : Int -> Set where
  non-neg-zero : NonNegIntRec zero-int
  non-neg-suc : {m : Int} -> NonNegIntRec m -> NonNeg m ->  NonNegIntRec (add1 m)

non-neg-int-rec : {m : Int} -> (NonNeg m) -> NonNegIntRec m
non-neg-int-rec {zero-int} _ = non-neg-zero
non-neg-int-rec {pos zero} _ = non-neg-suc {zero-int} (non-neg-int-rec (inj-r tt)) (inj-r tt)
non-neg-int-rec {pos (suc m)} _ = non-neg-suc {pos m} (non-neg-int-rec (inj-l tt)) (inj-l tt)
non-neg-int-rec {neg _} (inj-l ())
non-neg-int-rec {neg _} (inj-r ())

abs' : Int -> Nat
abs' (nonneg x) = x
abs' (neg x) = suc x

abs : Int -> Int
abs x = (nonneg (abs' x))

abs-NonZero : {a : Int} -> {NonZero a} -> NonZero (abs a)
abs-NonZero {zero-int} {inj-l ()}
abs-NonZero {zero-int} {inj-r ()}
abs-NonZero {pos _} = (inj-l tt)
abs-NonZero {neg _} = (inj-l tt)

NonNeg-abs : (a : Int) -> NonNeg (abs a)
NonNeg-abs a = NonNeg-nonneg (abs' a)

abs-inject-add1 : {m : Int} -> (NonNeg m) -> abs (add1 m) == add1 (abs m)
abs-inject-add1 {nonneg _} _ = refl
abs-inject-add1 {neg _} (inj-l ())
abs-inject-add1 {neg _} (inj-r ())

abs-inject-+ : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> abs (m + n) == abs m + abs n
abs-inject-+ {_} {n} mp np = rec (non-neg-int-rec mp)
  where
  rec : {m : Int} -> NonNegIntRec m -> abs (m + n) == abs m + abs n
  rec non-neg-zero = cong abs +-left-zero >=> sym +-left-zero
  rec (non-neg-suc {m} m-rec mp) =
    begin
      abs (add1 m + n)
    ==< cong abs (add1-extract-left {m}) >
      abs (add1 (m + n))
    ==< abs-inject-add1 (+-NonNeg-NonNeg mp np) >
      add1 (abs (m + n))
    ==< cong add1 (rec m-rec) >
      add1 (abs m + abs n)
    ==< sym (add1-extract-left {abs m}) >
      add1 (abs m) + abs n
    ==< sym (+-left (abs-inject-add1 mp)) >
      abs (add1 m) + abs n
    end


abs-inject-*/non-neg : {m n : Int} -> NonNeg m -> NonNeg n -> abs (m * n) == abs m * abs n
abs-inject-*/non-neg {_} {n} mp np = rec (non-neg-int-rec mp)
  where
  rec : {m : Int} -> NonNegIntRec m -> abs (m * n) == abs m * abs n
  rec non-neg-zero = cong abs (*-left-zero) >=> sym *-left-zero
  rec (non-neg-suc {m} m-rec mp) =
    begin
      abs (add1 m * n)
    ==< cong abs (add1-extract-* {m}) >
      abs (n + m * n)
    ==< abs-inject-+ np (*-NonNeg-NonNeg mp np) >
      abs n + abs (m * n)
    ==< +-right (rec m-rec) >
      abs n + abs m * abs n
    ==< sym (add1-extract-* {abs m} {abs n}) >
      add1 (abs m) * abs n
    ==< *-left (sym (abs-inject-add1 mp)) >
      abs (add1 m) * abs n
    end

abs-cancel-minus : {m : Int} -> abs (- m) == abs m
abs-cancel-minus {zero-int} = refl
abs-cancel-minus {pos _} = refl
abs-cancel-minus {neg _} = refl

abs-inject-* : {m n : Int} -> abs (m * n) == abs m * abs n
abs-inject-* {zero-int} {zero-int} = abs-inject-*/non-neg (inj-r tt) (inj-r tt)
abs-inject-* {zero-int} {pos n} = abs-inject-*/non-neg (inj-r tt) (inj-l tt)
abs-inject-* {zero-int} {neg n} = cong abs *-left-zero >=> sym *-left-zero
abs-inject-* {pos m} {zero-int} = abs-inject-*/non-neg {pos m} {zero-int} (inj-l tt) (inj-r tt)
abs-inject-* {pos m} {pos n} = abs-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt)
abs-inject-* {pos m} {neg n} =
  begin
    abs (pos m * neg n)
  ==< cong abs minus-extract-right >
    abs (- (pos m * pos n))
  ==< abs-cancel-minus {pos m * pos n}>
    abs (pos m * pos n)
  ==< abs-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt) >
    abs (pos m) * abs (neg n)
  end
abs-inject-* {neg m} {pos n} =
  begin
    abs (neg m * pos n)
  ==< cong abs minus-extract-left >
    abs (- (pos m * pos n))
  ==< abs-cancel-minus {pos m * pos n}>
    abs (pos m * pos n)
  ==< abs-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt) >
    abs (neg m) * abs (pos n)
  end
abs-inject-* {neg m} {neg n} =
  begin
    abs (neg m * neg n)
  ==< cong abs minus-extract-left >
    abs (- (pos m * neg n))
  ==< cong abs (cong minus minus-extract-right) >
    abs (- (- (pos m * pos n)))
  ==< abs-cancel-minus { - (pos m * pos n)}>=> abs-cancel-minus {pos m * pos n} >
    abs (pos m * pos n)
  ==< abs-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt) >
    abs (neg m) * abs (pos n)
  end
abs-inject-* {neg m} {zero-int} =
  begin
    abs (neg m * zero-int)
  ==< cong abs *-right-zero >
    zero-int
  ==< sym *-right-zero >
    abs (neg m) * abs zero-int
  end

--- abs'

abs->abs' : {m n : Int} -> abs m == abs n -> abs' m == abs' n
abs->abs' pr = cong abs' pr

nonneg-abs' : (m : Int) -> (NonNeg m) -> m == int (abs' m)
nonneg-abs' (nonneg _) _ = refl
nonneg-abs' (neg _) (inj-l ())
nonneg-abs' (neg _) (inj-r ())

nonpos-abs' : (m : Int) -> (NonPos m) -> m == - int (abs' m)
nonpos-abs' (nonneg (suc n)) (inj-l ())
nonpos-abs' (nonneg zero)    _ = refl
nonpos-abs' (neg _)          _ = refl


abs'-inject-add1 : {m : Int} -> (NonNeg m) -> abs' (add1 m) == suc (abs' m)
abs'-inject-add1 {nonneg _} _ = refl
abs'-inject-add1 {neg _} (inj-l ())
abs'-inject-add1 {neg _} (inj-r ())

abs'-inject-+ : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> abs' (m + n) == abs' m +' abs' n
abs'-inject-+ {_} {n} mp np = rec (non-neg-int-rec mp)
  where
  rec : {m : Int} -> NonNegIntRec m -> abs' (m + n) == abs' m +' abs' n
  rec non-neg-zero = cong abs' +-left-zero
  rec (non-neg-suc {m} m-rec mp) =
    begin
      abs' (add1 m + n)
    ==< cong abs' (add1-extract-left {m}) >
      abs' (add1 (m + n))
    ==< abs'-inject-add1 (+-NonNeg-NonNeg mp np) >
      suc (abs' (m + n))
    ==< cong suc (rec m-rec) >
      suc (abs' m +' abs' n)
    ==<>
      suc (abs' m) +' abs' n
    ==< sym (+'-left (abs'-inject-add1 mp)) >
      abs' (add1 m) +' abs' n
    end


abs'-inject-*/non-neg : {m n : Int} -> NonNeg m -> NonNeg n -> abs' (m * n) == abs' m *' abs' n
abs'-inject-*/non-neg {_} {n} mp np = rec (non-neg-int-rec mp)
  where
  rec : {m : Int} -> NonNegIntRec m -> abs' (m * n) == abs' m *' abs' n
  rec non-neg-zero = cong abs' *-left-zero
  rec (non-neg-suc {m} m-rec mp) =
    begin
      abs' (add1 m * n)
    ==< cong abs' (add1-extract-* {m}) >
      abs' (n + m * n)
    ==< abs'-inject-+ np (*-NonNeg-NonNeg mp np) >
      abs' n +' abs' (m * n)
    ==< +'-right {abs' n} (rec m-rec) >
      abs' n +' abs' m *' abs' n
    ==<>
      suc (abs' m) *' abs' n
    ==< *'-left (sym (abs'-inject-add1 mp)) >
      abs' (add1 m) *' abs' n
    end

abs'-cancel-minus : {m : Int} -> abs' (- m) == abs' m
abs'-cancel-minus {zero-int} = refl
abs'-cancel-minus {pos _} = refl
abs'-cancel-minus {neg _} = refl

abs'-inject-* : {m n : Int} -> abs' (m * n) == abs' m *' abs' n
abs'-inject-* {zero-int} {zero-int} = abs'-inject-*/non-neg (inj-r tt) (inj-r tt)
abs'-inject-* {zero-int} {pos n} = abs'-inject-*/non-neg (inj-r tt) (inj-l tt)
abs'-inject-* {zero-int} {neg n} = cong abs' *-left-zero
abs'-inject-* {pos m} {zero-int} = abs'-inject-*/non-neg {pos m} {zero-int} (inj-l tt) (inj-r tt)
abs'-inject-* {pos m} {pos n} = abs'-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt)
abs'-inject-* {pos m} {neg n} =
  begin
    abs' (pos m * neg n)
  ==< cong abs' minus-extract-right >
    abs' (- (pos m * pos n))
  ==< abs'-cancel-minus {pos m * pos n} >
    abs' (pos m * pos n)
  ==< abs'-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt) >
    abs' (pos m) *' abs' (neg n)
  end
abs'-inject-* {neg m} {pos n} =
  begin
    abs' (neg m * pos n)
  ==< cong abs' minus-extract-left >
    abs' (- (pos m * pos n))
  ==< abs'-cancel-minus {pos m * pos n} >
    abs' (pos m * pos n)
  ==< abs'-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt) >
    abs' (neg m) *' abs' (pos n)
  end
abs'-inject-* {neg m} {neg n} =
  begin
    abs' (neg m * neg n)
  ==< cong abs' minus-extract-left >
    abs' (- (pos m * neg n))
  ==< cong abs' (cong minus minus-extract-right) >
    abs' (- (- (pos m * pos n)))
  ==< abs'-cancel-minus { - (pos m * pos n)} >=> abs'-cancel-minus {pos m * pos n} >
    abs' (pos m * pos n)
  ==< abs'-inject-*/non-neg {pos m} {pos n} (inj-l tt) (inj-l tt) >
    abs' (neg m) *' abs' (pos n)
  end
abs'-inject-* {neg m} {zero-int} =
  begin
    abs' (neg m * zero-int)
  ==< cong abs' (*-right-zero) >
    zero
  ==< *'-commute {abs' zero-int} {abs' (neg m)} >
    abs' (neg m) *' abs' zero-int
  end

int-inject-+' : {m n : Nat} -> int (m +' n) == int m + int n
int-inject-+' {zero} {n} = sym +-left-zero
int-inject-+' {suc m} {n} =
  begin
    int (suc m +' n)
  ==<>
    add1 (int (m +' n))
  ==< cong add1 (int-inject-+' {m}) >
    add1 (int m + int n)
  ==< sym (add1-extract-left {int m}) >
    add1 (int m) + int n
  ==<>
    int (suc m) + int n
  end

int-inject-*' : {m n : Nat} -> int (m *' n) == int m * int n
int-inject-*' {zero} {n} = sym *-left-zero
int-inject-*' {suc m} {n} =
  begin
    int (suc m *' n)
  ==<>
    int (n +' (m *' n))
  ==< int-inject-+' {n} >
    int n + int (m *' n)
  ==< +-right (int-inject-*' {m} {n}) >
    int n + int m * int n
  ==< sym (add1-extract-* {int m} {int n}) >
    add1 (int m) * int n
  ==<>
    int (suc m) * int n
  end

non-neg-same-abs : {m n : Int} -> NonNeg m -> NonNeg n -> abs m == abs n -> m == n
non-neg-same-abs {nonneg m} {nonneg n} _ _ eq = eq
non-neg-same-abs {nonneg m} {neg n} _ (inj-l ())
non-neg-same-abs {nonneg m} {neg n} _ (inj-r ())
non-neg-same-abs {neg m} {_} (inj-l ())
non-neg-same-abs {neg m} {_} (inj-r ())
