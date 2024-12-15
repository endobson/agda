{-# OPTIONS --cubical --safe --exact-split #-}

module conat where

open import base
open import nat
open import order
open import order.instances.boolean
open import order.instances.nat
open import sum

record CoNat : Type₀ where
  constructor conat
  field
    bits : Nat -> Boolean
    increasing : ∀ {i j} -> i ≤ j -> bits i ≤ bits j

ℕ->CoNat : ℕ -> CoNat
ℕ->CoNat n = record { bits = bits ; increasing = increasing }
  where

  handle-cases : {i : ℕ} -> (i < n) ⊎ (n ≤ i) -> Boolean
  handle-cases = either (\_ -> false) (\_ -> true)

  bits : ℕ -> Boolean
  bits i = handle-cases (split-< i n)

  opaque
    increasing : ∀ {i j} -> i ≤ j -> bits i ≤ bits j
    increasing {i} {j} i≤j = handle (split-< i n) (split-< j n)
      where
      handle : (ci : (i < n) ⊎ (n ≤ i)) -> (cj : (j < n) ⊎ (n ≤ j)) ->
               handle-cases ci ≤ handle-cases cj
      handle (inj-l _)   (inj-l _)   = false≤false
      handle (inj-l _)   (inj-r _)   = false≤true
      handle (inj-r n≤i) (inj-l j<n) = bot-elim (convert-≤ i≤j (trans-<-≤ j<n n≤i))
      handle (inj-r _)   (inj-r _)   = true≤true

conat-ω : CoNat
conat-ω = record
  { bits = \_ -> false
  ; increasing = \_ -> false≤false
  }
