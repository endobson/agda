{-# OPTIONS --cubical --safe --exact-split #-}

module abs where

open import equality
open import base
open import nat
open import int


data NonNegIntRec : Int -> Set where
  non-neg-zero : NonNegIntRec zero-int
  non-neg-suc : {m : Int} -> NonNegIntRec m -> NonNeg m ->  NonNegIntRec (add1 m)

non-neg-int-rec : {m : Int} -> (NonNeg m) -> NonNegIntRec m
non-neg-int-rec {zero-int} _ = non-neg-zero
non-neg-int-rec {pos zero} _ = non-neg-suc {zero-int} (non-neg-int-rec tt) tt
non-neg-int-rec {pos (suc m)} _ = non-neg-suc {pos m} (non-neg-int-rec tt) tt

abs' : Int -> Nat
abs' (nonneg x) = x
abs' (neg x) = suc x

abs : Int -> Int
abs x = (nonneg (abs' x))

abs-NonZero : {a : Int} -> {NonZero a} -> NonZero (abs a)
abs-NonZero {zero-int} {}
abs-NonZero {pos _} = tt
abs-NonZero {neg _} = tt

abs-inject-add1 : {m : Int} -> (NonNeg m) -> abs (add1 m) == add1 (abs m)
abs-inject-add1 {nonneg _} _ = refl

abs-inject-+ : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> abs (m + n) == abs m + abs n
abs-inject-+ {_} {n} mp np = rec (non-neg-int-rec mp)
  where
  rec : {m : Int} -> NonNegIntRec m -> abs (m + n) == abs m + abs n
  rec non-neg-zero = refl
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
  rec non-neg-zero = refl
  rec (non-neg-suc {m} m-rec mp) =
    begin
      abs (add1 m * n)
    ==< cong abs (add1-extract-* {m}) >
      abs (n + m * n)
    ==< abs-inject-+ np (*-NonNeg-NonNeg mp np) >
      abs n + abs (m * n)
    ==< +-right {abs n} (rec m-rec) >
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
abs-inject-* {zero-int} {zero-int} = refl
abs-inject-* {zero-int} {pos n} = refl
abs-inject-* {zero-int} {neg n} = refl
abs-inject-* {pos m} {zero-int} = abs-inject-*/non-neg {pos m} {zero-int} tt tt
abs-inject-* {pos m} {pos n} = abs-inject-*/non-neg {pos m} {pos n} tt tt
abs-inject-* {pos m} {neg n} =
  begin
    abs (pos m * neg n)
  ==< cong abs (minus-extract-right {pos m} {pos n}) >
    abs (- (pos m * pos n))
  ==< abs-cancel-minus {pos m * pos n}>
    abs (pos m * pos n)
  ==< abs-inject-*/non-neg {pos m} {pos n} tt tt >
    abs (pos m) * abs (neg n)
  end
abs-inject-* {neg m} {pos n} =
  begin
    abs (neg m * pos n)
  ==< cong abs (minus-extract-left {pos m} {pos n}) >
    abs (- (pos m * pos n))
  ==< abs-cancel-minus {pos m * pos n}>
    abs (pos m * pos n)
  ==< abs-inject-*/non-neg {pos m} {pos n} tt tt >
    abs (neg m) * abs (pos n)
  end
abs-inject-* {neg m} {neg n} =
  begin
    abs (neg m * neg n)
  ==< cong abs (minus-extract-left {pos m} {neg n}) >
    abs (- (pos m * neg n))
  ==< cong abs (cong minus (minus-extract-right {pos m} {pos n})) >
    abs (- (- (pos m * pos n)))
  ==< abs-cancel-minus { - (pos m * pos n)}>=> abs-cancel-minus {pos m * pos n} >
    abs (pos m * pos n)
  ==< abs-inject-*/non-neg {pos m} {pos n} tt tt >
    abs (neg m) * abs (pos n)
  end
abs-inject-* {neg m} {zero-int} =
  begin
    abs (neg m * zero-int)
  ==< cong abs (*-commute {neg m} {zero-int}) >
    zero-int
  ==< *-commute {abs zero-int} {abs (neg m)} >
    abs (neg m) * abs zero-int
  end

--- abs'

abs->abs' : {m n : Int} -> abs m == abs n -> abs' m == abs' n
abs->abs' pr = cong abs' pr

abs'-inject-add1 : {m : Int} -> (NonNeg m) -> abs' (add1 m) == suc (abs' m)
abs'-inject-add1 {nonneg _} _ = refl

abs'-inject-+ : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> abs' (m + n) == abs' m +' abs' n
abs'-inject-+ {_} {n} mp np = rec (non-neg-int-rec mp)
  where
  rec : {m : Int} -> NonNegIntRec m -> abs' (m + n) == abs' m +' abs' n
  rec non-neg-zero = refl
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
  rec non-neg-zero = refl
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
abs'-inject-* {zero-int} {zero-int} = refl
abs'-inject-* {zero-int} {pos n} = refl
abs'-inject-* {zero-int} {neg n} = refl
abs'-inject-* {pos m} {zero-int} = abs'-inject-*/non-neg {pos m} {zero-int} tt tt
abs'-inject-* {pos m} {pos n} = abs'-inject-*/non-neg {pos m} {pos n} tt tt
abs'-inject-* {pos m} {neg n} =
  begin
    abs' (pos m * neg n)
  ==< cong abs' (minus-extract-right {pos m} {pos n}) >
    abs' (- (pos m * pos n))
  ==< abs'-cancel-minus {pos m * pos n} >
    abs' (pos m * pos n)
  ==< abs'-inject-*/non-neg {pos m} {pos n} tt tt >
    abs' (pos m) *' abs' (neg n)
  end
abs'-inject-* {neg m} {pos n} =
  begin
    abs' (neg m * pos n)
  ==< cong abs' (minus-extract-left {pos m} {pos n}) >
    abs' (- (pos m * pos n))
  ==< abs'-cancel-minus {pos m * pos n} >
    abs' (pos m * pos n)
  ==< abs'-inject-*/non-neg {pos m} {pos n} tt tt >
    abs' (neg m) *' abs' (pos n)
  end
abs'-inject-* {neg m} {neg n} =
  begin
    abs' (neg m * neg n)
  ==< cong abs' (minus-extract-left {pos m} {neg n}) >
    abs' (- (pos m * neg n))
  ==< cong abs' (cong minus (minus-extract-right {pos m} {pos n})) >
    abs' (- (- (pos m * pos n)))
  ==< abs'-cancel-minus { - (pos m * pos n)} >=> abs'-cancel-minus {pos m * pos n} >
    abs' (pos m * pos n)
  ==< abs'-inject-*/non-neg {pos m} {pos n} tt tt >
    abs' (neg m) *' abs' (pos n)
  end
abs'-inject-* {neg m} {zero-int} =
  begin
    abs' (neg m * zero-int)
  ==< cong abs' (*-commute {neg m} {zero-int}) >
    zero
  ==< *'-commute {abs' zero-int} {abs' (neg m)} >
    abs' (neg m) *' abs' zero-int
  end

int-inject-+' : {m n : Nat} -> int (m +' n) == int m + int n
int-inject-+' {zero} {n} = refl
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
int-inject-*' {zero} {n} = refl
int-inject-*' {suc m} {n} =
  begin
    int (suc m *' n)
  ==<>
    int (n +' (m *' n))
  ==< int-inject-+' {n} >
    int n + int (m *' n)
  ==< +-right {int n} (int-inject-*' {m} {n}) >
    int n + int m * int n
  ==< sym (add1-extract-* {int m} {int n}) >
    add1 (int m) * int n
  ==<>
    int (suc m) * int n
  end

non-neg-same-abs : {m n : Int} -> NonNeg m -> NonNeg n -> abs m == abs n -> m == n
non-neg-same-abs {nonneg m} {nonneg n} _ _ eq = eq
