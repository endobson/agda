{-# OPTIONS --cubical --safe --exact-split #-}

module prime-div-count where

open import base
open import div
open import equality
open import gcd
open import lcm
open import nat
open import prime
open import prime-gcd
open import relation
open import sigma


record PrimeDivCount (p : Prime') (a : Nat) (n : Nat)  : Type₀ where
  constructor prime-div-count

  private
    p' = ⟨ p ⟩

  field
    %a : (prime-power p n) div' a

  r : Nat
  r = ⟨ %a ⟩

  r-path : r *' (prime-power p n) == a
  r-path = snd %a

  field
    ¬p%r : ¬ (⟨ p ⟩ div' r)

  ¬p^sn%a : ¬ (prime-power p (suc n) div' a)
  ¬p^sn%a (x , x-path) = ¬p%r (x , path')
    where
    path' : (x *' p') == r
    path' = *'-right-injective (prime-power⁺ p n) (*'-assoc {x} {p'} >=> x-path >=> sym r-path)

  a-pos : Pos' a
  a-pos = handle r refl
    where
    handle : (x : Nat) -> (x == r) -> Pos' a
    handle zero    path = bot-elim (¬p%r (transport (cong (p' div'_) path) div'-zero))
    handle (suc x) path = transport (cong Pos' r-path)
                                    (*'-Pos'-Pos' (transport (cong Pos' path) tt)
                                                             (snd (prime-power⁺ p n)))
