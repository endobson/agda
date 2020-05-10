module abs where

open import base


data NonNegIntRec : Int -> Set where
  non-neg-zero : NonNegIntRec zero-int
  non-neg-suc : {m : Int} -> NonNegIntRec m -> NonNeg m ->  NonNegIntRec (add1 m)

non-neg-int-rec : {m : Int} -> (NonNeg m) -> NonNegIntRec m
non-neg-int-rec {zero-int} _ = non-neg-zero 
non-neg-int-rec {pos zero} _ = non-neg-suc {zero-int} (non-neg-int-rec tt) tt
non-neg-int-rec {pos (suc m)} _ = non-neg-suc {pos m} (non-neg-int-rec tt) tt

abs : Int -> Int
abs zero-int = zero-int
abs (pos x) = pos x
abs (neg x) = pos x

abs-NonNeg : {n : Int} -> NonNeg (abs n)
abs-NonNeg {zero-int} = tt
abs-NonNeg {pos _} = tt
abs-NonNeg {neg _} = tt

abs-NonZero : {a : Int} -> {NonZero a} -> NonZero (abs a)
abs-NonZero {zero-int} {}
abs-NonZero {pos _} = tt
abs-NonZero {neg _} = tt

abs-inject-add1 : {m : Int} -> (NonNeg m) -> abs (add1 m) == add1 (abs m)
abs-inject-add1 {zero-int} _ = refl
abs-inject-add1 {pos m} _ = refl

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
    ==< sym (add1-extract-* {abs m}) >
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
  ==< abs-cancel-minus >
    abs (pos m * pos n)
  ==< abs-inject-*/non-neg {pos m} {pos n} tt tt >
    abs (pos m) * abs (neg n)
  end
abs-inject-* {neg m} {pos n} =
  begin
    abs (neg m * pos n)
  ==< cong abs (minus-extract-left {pos m} {pos n}) >
    abs (- (pos m * pos n))
  ==< abs-cancel-minus >
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
  ==< abs-cancel-minus >=> abs-cancel-minus >
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


abs' : Int -> Nat
abs' zero-int = zero
abs' (pos x) = suc x
abs' (neg x) = suc x


abs->abs' : {m n : Int} -> abs m == abs n -> abs' m == abs' n
abs->abs' {zero-int} {zero-int} _ = refl
abs->abs' {pos m} {pos n} refl = refl
abs->abs' {pos m} {neg n} refl = refl
abs->abs' {neg m} {pos n} refl = refl
abs->abs' {neg m} {neg n} refl = refl
abs->abs' {zero-int} {pos n} ()
abs->abs' {zero-int} {neg n} ()
abs->abs' {pos n} {zero-int} ()
abs->abs' {neg n} {zero-int} ()


abs'-inject-add1 : {m : Int} -> (NonNeg m) -> abs' (add1 m) == suc (abs' m)
abs'-inject-add1 {zero-int} _ = refl
abs'-inject-add1 {pos m} _ = refl

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
  ==< abs'-cancel-minus >
    abs' (pos m * pos n)
  ==< abs'-inject-*/non-neg {pos m} {pos n} tt tt >
    abs' (pos m) *' abs' (neg n)
  end
abs'-inject-* {neg m} {pos n} =
  begin
    abs' (neg m * pos n)
  ==< cong abs' (minus-extract-left {pos m} {pos n}) >
    abs' (- (pos m * pos n))
  ==< abs'-cancel-minus >
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
  ==< abs'-cancel-minus >=> abs'-cancel-minus >
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


-- 
-- abs'->abs : {m n : Int} -> abs' m == abs' n -> abs m == abs n
-- abs'->abs {zero-int} {zero-int} _ = refl
-- abs'->abs {pos m} {pos n} refl = refl
-- abs'->abs {pos m} {neg n} refl = refl
-- abs'->abs {neg m} {pos n} refl = refl
-- abs'->abs {neg m} {neg n} refl = refl
-- abs'->abs {zero-int} {pos n} ()
-- abs'->abs {zero-int} {neg n} ()
-- abs'->abs {pos n} {zero-int} ()
-- abs'->abs {neg n} {zero-int} ()
-- 
-- abs'-inject-add1 : {m : Int} -> (NonNeg m) -> abs' (add1 m) == suc (abs' m)
-- abs'-inject-add1 {zero-int} _ = refl
-- abs'-inject-add1 {pos m} _ = refl
-- 
-- 
-- abs'-inject-+ : {m n : Int} -> (NonNeg m) -> (NonNeg n) -> abs' (m + n) == abs' m +' abs' n
-- abs'-inject-+ {_} {n} mp np = rec (non-neg-int-rec mp)
--   where
--   rec : {m : Int} -> NonNegIntRec m -> abs' (m + n) == abs' m +' abs' n
--   rec non-neg-zero = refl
--   rec (non-neg-suc {m} m-rec mp) =
--     begin
--       abs' (add1 m + n)
--     ==< cong abs' (add1-extract-left {m}) >
--       abs' (add1 (m + n))
--     ==< abs'-inject-add1 (+-NonNeg-NonNeg mp np) >
--       suc (abs' (m + n))
--     ==< cong suc (rec m-rec) >
--       suc (abs' m +' abs' n)
--     ==< +'-left (sym (abs'-inject-add1 mp)) >
--       abs' (add1 m) +' abs' n
--     end 
-- 
-- abs'-inject-* : {m n : Int} -> NonNeg m -> NonNeg n -> abs' (m * n) == abs' m *' abs' n
-- abs'-inject-* {_} {n} mp np = rec (non-neg-int-rec mp)
--   where
--   rec : {m : Int} -> NonNegIntRec m -> abs' (m * n) == abs' m *' abs' n
--   rec non-neg-zero = refl
--   rec (non-neg-suc {m} m-rec mp) = 
--     begin
--       abs' (add1 m * n)
--     ==< cong abs' (add1-extract-* {m}) >
--       abs' (n + m * n)
--     ==< abs'-inject-+ np (*-NonNeg-NonNeg mp np) >
--       abs' n +' abs' (m * n)
--     ==< +'-right {abs' n} (rec m-rec) >
--       abs' n +' abs' m *' abs' n
--     ==<>
--       suc (abs' m) *' abs' n
--     ==< *'-left (sym (abs'-inject-add1 mp)) >
--       abs' (add1 m) *' abs' n
--     end
-- 
-- 
-- abs'-cancel-minus : {m : Int} -> abs' (- m) == abs' m
-- abs'-cancel-minus {zero-int} = refl
-- abs'-cancel-minus {pos _} = refl
-- abs'-cancel-minus {neg _} = refl
-- 
-- 
-- data Sign : Set where
--   pos-sign : Sign
--   neg-sign : Sign
-- 
-- data SignedNat : Set where
--   snat : Sign -> Nat -> SignedNat
-- int->snat : Int -> SignedNat
-- int->snat (zero-int) = snat pos-sign zero
-- int->snat (pos m) = snat pos-sign (suc m)
-- int->snat (neg m) = snat neg-sign (suc m)
-- 
-- snat->int : SignedNat -> Int
-- snat->int (snat pos-sign n) = int n
-- snat->int (snat neg-sign n) = - int n
-- 
-- int->snat->int-id : {n : Int} -> (snat->int (int->snat n)) == n
-- int->snat->int-id {zero-int} = refl
-- int->snat->int-id {pos n} = refl
-- int->snat->int-id {neg n} = refl
-- 
-- snat-abs : SignedNat -> SignedNat
-- snat-abs (snat _ n) = (snat pos-sign n)
-- 
-- abs-extract-int->snat : {n : Int} -> int->snat (abs n) == snat-abs (int->snat n)
-- abs-extract-int->snat {zero-int} = refl
-- abs-extract-int->snat {pos n} = refl
-- abs-extract-int->snat {neg n} = refl
-- 
-- _sign-*_ : Sign -> Sign -> Sign
-- pos-sign sign-* pos-sign = pos-sign
-- pos-sign sign-* neg-sign = neg-sign
-- neg-sign sign-* pos-sign = neg-sign
-- neg-sign sign-* neg-sign = pos-sign
-- 
-- _snat-*_ : SignedNat -> SignedNat -> SignedNat
-- (snat s1 n1) snat-* (snat s2 n2) = (snat (s1 sign-* s2) (n1 *' n2))
-- 
-- snat-abs-inject-* : {m n : SignedNat} -> snat-abs (m snat-* n) == (snat-abs m) snat-* (snat-abs n)
-- snat-abs-inject-* {snat s1 n1} {snat s2 n2} = refl
-- 
-- -- int->snat-* : {m n : Int} -> int->snat (m * n) == int->snat m * int->snat n 


