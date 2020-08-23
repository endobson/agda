{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.eulers-algorithm where

open import abs
open import base
open import equality
open import div
open import int
open import linear-combo
open import nat
open import gcd.propositional

linear-combo->gcd : {a b d : Int} -> LinearCombination a b d -> d div a -> d div b -> GCD a b (abs d)
linear-combo->gcd (linear-combo _ _ _ x y {p}) da db =
  (gcd tt (div-abs-left da) (div-abs-left db)
    (\ z za zb -> transport (\i -> z div abs (p i)) (div-abs-right (div-linear za zb {x} {y}))))

data LinearGCD : Int -> Int -> Int -> Set where
 linear-gcd : {a : Int} -> {b : Int} -> {d : Int}
   -> (lc : (LinearCombination a b d))
   -> (gcd : (GCD a b d))
   -> LinearGCD a b d

linear-gcd-sym : {a b d : Int} -> LinearGCD a b d -> LinearGCD b a d
linear-gcd-sym (linear-gcd lc gc) = (linear-gcd (linear-combo-sym lc) (gcd-sym gc))

linear-gcd-negate : {a b d : Int} -> LinearGCD a b d -> LinearGCD a (- b) d
linear-gcd-negate (linear-gcd lc gc) =
  (linear-gcd (linear-combo-negate lc)
              (gcd-negate gc))

data CompareNat3 : Nat -> Nat -> Set where
  compare3-= : {m n : Nat} -> m == n -> CompareNat3 m n
  compare3-< : {a m n : Nat}
    -> (pos a) + (pos m) == (pos n)
    -> suc (a +' m) ≤ (m +' n)
    -> CompareNat3 m n
  compare3-> : {a m n : Nat}
    -> (pos a) + (pos n) == (pos m)
    -> suc (a +' n) ≤ (m +' n)
    -> CompareNat3 m n
decide-compare3 : (m : Nat) -> (n : Nat) -> CompareNat3 m n
decide-compare3 zero zero = compare3-= refl
decide-compare3 zero (suc n) = compare3-< {n} (+-commute {pos n}) ≤-proof
  where
  ≤-proof : (suc n +' zero) ≤ suc n
  ≤-proof = transport (\i -> (+'-right-zero {suc n} (~ i)) ≤ suc n) (same-≤ (suc n))
decide-compare3 (suc m) zero = compare3-> {m} (+-commute {pos m}) (same-≤ (suc (m +' zero)))
decide-compare3 (suc m) (suc n) = fix (decide-compare3 m n)
  where fix : CompareNat3 m n -> CompareNat3 (suc m) (suc n)
        fix (compare3-= p) = (compare3-= (cong suc p))
        fix (compare3-< {a} pr rec-≤) =
          compare3-< {a} (add1-extract-right {pos a} >=> cong add1 pr) ≤-proof
          where
          ≤-proof : (suc a +' suc m) ≤ (suc m +' suc n)
          ≤-proof = transport (\i -> (+'-right-suc {suc a} {m} (~ i)) ≤ (+'-right-suc {suc m} {n} (~ i)))
                              (suc-≤ (right-suc-≤ rec-≤))
        fix (compare3-> {a} pr rec-≤) =
          compare3-> {a} (add1-extract-right {pos a} >=> cong add1 pr) ≤-proof
          where
          ≤-proof : (suc a +' suc n) ≤ (suc m +' suc n)
          ≤-proof = transport (\i -> (+'-right-suc {suc a} {n} (~ i)) ≤ (+'-right-suc {suc m} {n} (~ i)))
                              (suc-≤ (right-suc-≤ rec-≤))


eulers-helper-gcd : (m : Nat) -> (n : Nat) ->
                    {a : Nat} -> (pos a + pos m == pos n) -> {d : Int} ->
                    GCD (pos a) (pos m) d
                    -> GCD (pos m) (pos n) d
eulers-helper-gcd m n {a} pr {d} (gcd non-neg d-div-a' d-div-m' f) =
  gcd non-neg d-div-m' div-proof rec-proof
  where
  div-proof : d div (pos n)
  div-proof = transport (\i -> d div (pr i)) (div-sum d-div-a' d-div-m')
  rec-proof : (x : Int) -> x div (pos m) -> x div (pos n) -> x div d
  rec-proof x x-div-m' x-div-n' = f x x-div-a' x-div-m'
    where
    x-div-mn : x div (neg m + pos n)
    x-div-mn = div-sum (div-negate x-div-m') x-div-n'
    mn==a : neg m + pos n == pos a
    mn==a =
      begin
        neg m + pos n
      ==< +-right {neg m} (sym pr) >
        neg m + (pos a + pos m)
      ==< +-right {neg m} (+-commute {pos a}) >
        neg m + (pos m + pos a)
      ==< sym (+-assoc {neg m}) >
        (neg m + pos m) + pos a
      ==< +-left (add-minus-zero {neg m}) >
        pos a
      end
    x-div-a' : x div (pos a)
    x-div-a' = transport (\i -> x div (mn==a i)) x-div-mn

eulers-helper-lc : (m : Nat) -> (n : Nat) ->
                   {a : Nat} -> (pos a + pos m == pos n) -> {d : Int} ->
                   LinearCombination (pos a) (pos m) d
                   -> LinearCombination (pos m) (pos n) d
eulers-helper-lc m' n' {a'} add-pr (linear-combo a m d x y {pr}) =
  (linear-combo m n d z x {proof})
  where
  n : Int
  n = pos n'
  z : Int
  z = - x + y
  proof : z * m + x * n == d
  proof =
    begin
       z * m + x * n
    ==< +-commute {z * m} >
       x * n + z * m
    ==< +-left (*-right {x} (sym add-pr)) >
       x * (a + m) + z * m
    ==< +-left (*-commute {x}) >
       (a + m) * x + z * m
    ==< +-left (*-distrib-+ {a}) >
       (a * x + m * x) + z * m
    ==< +-left (+-left (*-commute {a} {x})) >
       (x * a + m * x) + z * m
    ==< +-left (+-right {x * a} (*-commute {m} {x})) >
       (x * a + x * m) + z * m
    ==< +-assoc {x * a} >
       x * a + (x * m + z * m)
    ==< +-right {x * a} (sym (*-distrib-+ {x})) >
       x * a + (x + z) * m
    ==<>
       x * a + (x + (- x + y)) * m
    ==< +-right {x * a} (*-left (sym (+-assoc {x}))) >
       x * a + ((x + - x) + y) * m
    ==< +-right {x * a} (*-left (+-left (add-minus-zero {x}))) >
       x * a + y * m
    ==< pr >
      d
    end

eulers-helper : (m : Nat) -> (n : Nat) ->
                {a : Nat} -> (pos a + pos m == pos n) -> {d : Int} ->
                LinearGCD (pos a) (pos m) d
                -> LinearGCD (pos m) (pos n) d
eulers-helper m n {a} pr {d} (linear-gcd lc gc) =
  (linear-gcd (eulers-helper-lc m n {a} pr {d} lc)
              (eulers-helper-gcd m n {a} pr {d} gc))

pos-eulers-algo' : (b : Nat) -> (m : Nat) -> (n : Nat)
  -> (m +' n) < b
  -> Σ[ d ∈ Int ] (LinearGCD (pos m) (pos n) d)
pos-eulers-algo' (suc b) m n size-pr = split (decide-compare3 m n)
  where
  split : CompareNat3 m n -> Σ[ d ∈ Int ] (LinearGCD (pos m) (pos n) d)
  split (compare3-= pr) =
    transport
      (\i -> Σ[ d ∈ Int ] (LinearGCD (pos m) (pos (pr i)) d))
      ((pos m) , (linear-gcd linear-combo-refl gcd-refl))
  split (compare3-< {a} pr rec-size-pr) = handle (pos-eulers-algo' b a m new-size-pr)
    where
    handle : Σ[ d ∈ Int ] (LinearGCD (pos a) (pos m) d) -> Σ[ d ∈ Int ] (LinearGCD (pos m) (pos n) d)
    handle (d , gc) = (d , (eulers-helper m n {a} pr {d} gc))
    new-size-pr : (a +' m) < b
    new-size-pr = pred-≤ (trans-≤-< rec-size-pr size-pr)
  split (compare3-> {a} pr rec-size-pr) = handle (pos-eulers-algo' b a n new-size-pr)
    where
    handle : Σ[ d ∈ Int ] (LinearGCD (pos a) (pos n) d) -> Σ[ d ∈ Int ](LinearGCD (pos m) (pos n) d)
    handle (d , gc) = (d , (linear-gcd-sym (eulers-helper n m {a} pr {d} gc)))
    new-size-pr : (a +' n) < b
    new-size-pr = pred-≤ (trans-≤-< rec-size-pr size-pr)
pos-eulers-algo' zero m n <b = bot-elim (zero-≮ <b)


pos-eulers-algo : (m : Nat) -> (n : Nat) -> Σ[ d ∈ Int ] (LinearGCD (pos m) (pos n) d)
pos-eulers-algo m n = pos-eulers-algo' (suc (m +' n)) m n (add1-< (m +' n))


eulers-algo : (m : Int) -> (n : Int) -> Σ[ d ∈ Int ] (LinearGCD m n d)
eulers-algo m zero-int =
  (abs m) ,
  (linear-gcd (linear-combo-abs linear-combo-zero) gcd-zero)
eulers-algo zero-int n@(pos _) =
  (abs n) ,
  (linear-gcd-sym (linear-gcd (linear-combo-abs linear-combo-zero) gcd-zero))
eulers-algo zero-int n@(neg _) =
  (abs n) ,
  (linear-gcd-sym (linear-gcd (linear-combo-abs linear-combo-zero) gcd-zero))
eulers-algo (pos m) (pos n) = pos-eulers-algo m n
eulers-algo (neg m) (pos n) = handle (pos-eulers-algo m n)
  where
  handle : Σ[ d ∈ Int ] (LinearGCD (pos m) (pos n) d) -> Σ[ d ∈ Int ] (LinearGCD (neg m) (pos n) d)
  handle (d , pr) = d , (linear-gcd-sym (linear-gcd-negate (linear-gcd-sym pr)))
eulers-algo (pos m) (neg n) = handle (pos-eulers-algo m n)
  where
  handle : Σ[ d ∈ Int ] (LinearGCD (pos m) (pos n) d) -> Σ[ d ∈ Int ] (LinearGCD (pos m) (neg n) d)
  handle (d , pr) = d , (linear-gcd-negate pr)
eulers-algo (neg m) (neg n) = handle (pos-eulers-algo m n)
  where
  handle : Σ[ d ∈ Int ] (LinearGCD (pos m) (pos n) d) -> Σ[ d ∈ Int ] (LinearGCD (neg m) (neg n) d)
  handle (d , pr) =
    d , (linear-gcd-sym (linear-gcd-negate (linear-gcd-sym (linear-gcd-negate pr))))

gcd-exists : (m : Int) -> (n : Int) -> Σ[ d ∈ Int ] (GCD m n d)
gcd-exists m n = handle (eulers-algo m n)
  where
  handle : Σ[ d ∈ Int ] (LinearGCD m n d) -> Σ[ d ∈ Int ] (GCD m n d)
  handle (d , (linear-gcd _ gc)) = d , gc

gcd->linear-combo : {a b d : Int} -> GCD a b d -> LinearCombination a b d
gcd->linear-combo {a} {b} {d} gcd-d = handle (eulers-algo a b)
  where
  handle : Σ[ d ∈ Int ] (LinearGCD a b d) -> LinearCombination a b d
  handle (d' , (linear-gcd lc gcd-d')) =
    transport (\i -> LinearCombination a b ((gcd-unique gcd-d' gcd-d) i)) lc
