{-# OPTIONS --cubical --safe --exact-split #-}

module rational.factor-order where

open import base
open import equality
open import order
open import order.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-< ; split-<)
open import relation
open import sign
open import sign.instances.rational

module _ (q r : ℚ) (q≤r : q ℚ≤ r)
         (a b c d : ℚ) (ab=q : (a r* b) == q) (cd=r : (c r* d) == r) where

  factor-order-PPPP : (pa : Pos a) (pb : Pos b) (pc : Pos c) (pd : Pos d) -> (a ℚ≤ c ⊎ b ℚ≤ d)
  factor-order-PPPP pa pb pc pd = handle (split-< c a) (split-< d b)
    where
    handle : (c < a) ⊎ (a ℚ≤ c) -> (d < b) ⊎ (b ℚ≤ d) -> (a ℚ≤ c ⊎ b ℚ≤ d)
    handle (inj-r lt)  _           = (inj-l lt)
    handle (inj-l _)   (inj-r lt)  = (inj-r lt)
    handle (inj-l c<a) (inj-l d<b) =
      bot-elim (irrefl-< {_} {_} {_} {r} (trans-<-≤ {r} {q} {r} r<q q≤r))
      where
      cd<cb : (c r* d) < (c r* b)
      cd<cb = r*₁-preserves-order (c , pc) d b d<b
      cb<ab : (c r* b) < (a r* b)
      cb<ab = r*₂-preserves-order c a (b , pb) c<a
      r<q : r < q
      r<q = subst2 _<_ cd=r ab=q (trans-< {_} {_} {_} {c r* d} {c r* b} {a r* b} cd<cb cb<ab)
