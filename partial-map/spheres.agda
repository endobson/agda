{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import cubical
open import dominance
open import equality-path
open import equivalence
open import functions
open import funext
open import hlevel
open import isomorphism
open import relation
open import sigma
open import sigma.base
open import transport
open import type-algebra
open import univalence
open import partial-map
open import spheres2

module partial-map.spheres where

idS1 : S1 -> S1
idS1 base = base
idS1 (loop i) = loop i

R : Rel S1 ℓ-zero
R x y = x == y

add-loop : (a : S1) -> a == base -> a == base
add-loop a p = p >=> loop

-- loop-commute : (p : S1) (p2 : S1) -> p1 == p2 ->

--loop-commute : (p : base == base) -> (loop ∙∙ p ∙∙ refl) == (refl ∙∙ p ∙∙ loop)
--loop-commute p i j =
--  hcomp (\k -> \{ (i = i0) -> i0-case j k
--                ; (i = i1) -> i1-case j k
--                ; (j = i0) -> j0-case i k
--                ; (j = i1) -> j1-case i k
--                })
--        (p j)
--  where
--  i0-case : Square (sym loop) refl p (loop ∙∙ p ∙∙ refl)
--  i0-case = ?
--  i1-case : Square refl (sym loop) p (refl ∙∙ p ∙∙ loop)
--  i1-case = ?
--  j0-case : Square (sym loop) refl refl refl
--  j0-case = ?
--  j1-case : Square refl (sym loop) refl refl
--  j1-case = ?



--add-loop' : (a : S1) -> a == a -> a == a
--add-loop' base p = p >=> loop
--add-loop' (loop i) p j = ? -- outS ans
--  where
--  φ : I
--  φ = (i ∨ ~ i ∨ j ∨ ~ j)
--
--  spec : Partial φ S1
--  spec = (\{ (i = i0) -> (p >=> loop) j
--           ; (i = i1) -> (p >=> loop) j
--           ; (j = i0) -> loop i
--           ; (j = i1) -> loop i
--           })
--
--  ans' : S1
--  ans' = (hcomp (\k -> \{ (i = i0) -> ?
--                        ; (i = i1) -> ?
--                        ; (j = i0) -> ?
--                        ; (j = i1) -> base
--                        })
--                  (p j))
--


  -- ans : Sub S1 φ spec
  -- ans = inS (hcomp (\k -> \{ (i = i0) -> ?
  --                          ; (i = i1) -> ?
  --                          ; (j = i0) -> ?
  --                          ; (j = i1) -> loop (~ k ∨ i)
  --                          })
  --                  (p j))


--add-loop' : (a b : S1) -> a == b -> a == b
--add-loop' base     b p = loop >=> p
--add-loop' (loop i) b p j = outS ans
--  where
--  spec : Partial (i ∨ ~ i ∨ j ∨ ~ j) S1
--  spec = (\{ (i = i0) -> (loop >=> p) j
--           ; (i = i1) -> (loop >=> p) j
--           ; (j = i0) -> loop i
--           ; (j = i1) -> b
--           })
--
--  ans : Sub S1 (i ∨ ~ i ∨ j ∨ ~ j) spec
--  ans = ?
--
--  module _ (k : I) where
--    ans-back : Sub S1 (~ i ∧ (~ k ∨ k ∨ j ∨ ~ j)
--                (\{ (i = i0) (k = i1) -> (loop >=> p) j
--                  ; (i = i0) (k = i0) -> p j
--                  })
--    ans-back = ?
--    ans-front : Sub S1 (i ∧ (~ k ∨ k))
--                 (\{ (i = i1) (k = i1) -> (loop >=> p) j ; (i = i1) (k = i0) -> p j})
--    ans-front = ?
--    ans-left : Sub S1 (~ j ∧ (~ k ∨ k))
--                 (\{ (j = i0) (k = i1) -> loop i ; (j = i0) (k = i0) -> loop i})
--    ans-left = ?
--    ans-right : Sub S1 (j ∧ (~ k ∨ k))
--                 (\{ (j = i1) (k = i1) -> b ; (j = i1) (k = i0) -> b})
--    ans-right = ?
--
--
--  ans2 : Sub S1 (i ∨ ~ i ∨ j ∨ ~ j) spec
--  ans2 = inS (hcomp (\k -> (\{ (i = i0) -> outS (ans-back k)
--                             ; (i = i1) -> outS (ans-front k)
--                             ; (j = i0) -> outS (ans-left k)
--                             ; (j = i1) -> outS (ans-right k)
--                        }))
--               (p j))



--self-inverse1 : InverseRelations R R
--self-inverse1 a b = isoToEquiv (iso sym sym (\_ -> refl) (\_ -> refl))


--self-inverse2 : InverseRelations R R
--self-inverse2 a b = isoToEquiv (iso f ? ? ?)
--  where
--  f : a == b -> b == a
--  f p = ?


