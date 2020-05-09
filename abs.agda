module abs where

open import base

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

-- abs-inject-* : {m n : Int} -> abs (m * n) ==  abs m * abs n
-- abs-inject-* {zero-int} {_} = refl
-- abs-inject-* {m} {zero-int} = (cong abs (*-commute {m})) >=> (*-commute {abs zero-int} {abs m})
-- abs-inject-* {pos m} {pos n} = proof
--   where
--     proof : abs ((pos m) * (pos n)) == pos m * pos n
--     proof = ?
-- abs-inject-* {_} {_} = ?

