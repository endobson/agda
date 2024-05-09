{-# OPTIONS --cubical --safe --exact-split #-}

module equality.pathp-iso where

open import base
open import cubical
open import isomorphism
open import equivalence
open import equality-path
open import functions

-- Taken from GroupoidLaws in cubical stdlib

-- u : This is a partial cube across dimension 'i'.
-- u0 : This is the initial value that align with (u i0)
-- h2 : This is another filler that matches u when it is φ and
--      on i0 is the wrapped u0
--
-- The result shows that hcomp is the same output as h2 when φ is one.
-- The path is also the const path of the value (u i1) on φ.

private
  hcomp-unique : {ℓ : Level} {A : Type ℓ} {φ : I} ->
    (u : I -> Partial φ A) -> (u0 : Sub A φ \{ (φ = i1) -> u i0 1=1}) ->
    (h2 : (i : I) -> Sub A (φ ∨ ~ i) \{ (φ = i1) -> u i 1=1 ; (i = i0) -> outS u0 }) ->
    Sub (hcomp u (outS u0) == outS (h2 i1)) φ \{ (φ = i1) -> \i -> u i1 1=1 }
  hcomp-unique {φ = φ} u u0 h2 =
    inS (\i -> hcomp (\j -> \{ (φ = i1) -> u j 1=1
                             ; (i = i1) -> outS (h2 j)})
                (outS u0))


-- Heavily copied from PathPIsoPath in cubical stdlib
module _ {ℓ : Level} {A : I -> Type ℓ} {x : A i0} {y : A i1} where
  private
    forward : (PathP A x y) -> (transport (\k -> A k) x == y)
    forward p i = transp (\j -> A (i ∨ j)) i (p i)

    backward : (transport (\k -> A k) x == y) -> (PathP A x y)
    backward p i =
      hcomp (\j -> \{ (i = i0) -> x
                    ; (i = i1) -> p j})
            (transp (\j -> A (i ∧ j)) (~ i) x)

    bf : (p : PathP A x y) ->
         backward (forward p) == p
    bf p k i =
      outS (hcomp-unique
             (\j -> \{ (i = i0) -> x
                     ; (i = i1) -> transp (\k -> A (j ∨ k)) j (p j)})
             (inS (transp (\j -> A (i ∧ j)) (~ i) x) )
             (\j -> inS (transp (\l -> A (i ∧ (j ∨ l))) (~ i ∨ j) (p (i ∧ j)))))
           k

    fb : (p : transport (\k -> A k) x == y) ->
         forward (backward p) == p
    fb p k i =
      hcomp
        (\j -> \{ (i = i0) -> slide (j ∨ ~ k)
                ; (i = i1) -> p j
                ; (k = i0) -> transp (\l -> A (i ∨ l)) i (backward-filler j)
                ; (k = i1) -> slide2-square j
                })
        (outS base)
      where

      slide : (i : I) -> A i1
      slide i = transp (\l -> A (i ∨ l)) i (transp (\l -> A (i ∧ l)) (~ i) x)

      base : Sub (A i1) (i ∨ ~ i ∨ k ∨ ~ k)
             \{ (i = i0) -> slide (~ k)
              ; (i = i1) -> transp (\l -> A l) i0 x
              ; (k = i0) -> slide i
              ; (k = i1) -> slide i
              }
      base = inS
        (transp (\ l -> A (i ∨ ~ k ∨ l)) (i ∨ ~ k)
          (transp (\ l -> (A (i ∨ (~ k ∧ l)))) (k ∨ i)
            (transp (\ l -> A (i ∧ l)) (~ i)
              x)))

      backward-filler : (j : I) -> A i
      backward-filler j =
        hfill
          (\j -> \{ (i = i0) -> x
                  ; (i = i1) -> p j })
          (inS (transp (\l -> A (i ∧ l)) (~ i) x)) j

      slide2-square : (j : I) -> A i1
      slide2-square j =
        hcomp
          (\l -> \{ (i = i0) -> slide j
                  ; (i = i1) -> p (l ∧ j)
                  ; (j = i0) -> slide i
                  ; (j = i1) -> p (l ∧ i)
                  })
          (slide (i ∨ j))


  abstract
    PathP≃transport : (PathP A x y) ≃ (transport (\i -> A i) x == y)
    PathP≃transport = isoToEquiv (iso forward backward fb bf)

-- Much simpler proof
module _ {ℓ : Level} {A : I -> Type ℓ} {x : A i0} {y : A i1} where
  PathP==transport : (PathP A x y) == (transport (\i -> A i) x == y)
  PathP==transport i =
    PathP (\j -> A (i ∨ j)) (transport-filler (\j -> A j) x i) y


module _ {ℓ : Level} {A B C D : Type ℓ}
         (p1 : A == C) (p2 : B == D)
         (f-ab : A -> B) (f-cd : C -> D)
         where
  opaque
    private
      t1 : PathP (\k -> p1 (~ k) -> p1 i1) (\x -> x) (\x -> transport p1 x)
      t1 k x = transp (\j -> p1 (~ k ∨ j)) (~ k) x

      t2 : PathP (\k -> p2 i0 -> p2 k) (\x -> x) (\x -> transport p2 x)
      t2 k x = transp (\j -> p2 (k ∧ j)) (~ k) x

    function-pathp==commuting-squareᵉ :
      (PathP (\i -> p1 i -> p2 i) f-ab f-cd) ==
      ((transport p2) ∘ f-ab == f-cd ∘ (transport p1))
    function-pathp==commuting-squareᵉ i =
      PathP (\j -> p1 (~ i ∧ j) -> p2 (i ∨ j)) ((t2 i) ∘ f-ab) (f-cd ∘ (t1 i))

module _ {ℓ : Level} {A B C D : Type ℓ}
         {p1 : A == C} {p2 : B == D}
         {f-ab : A -> B} {f-cd : C -> D}
         where
  function-pathp==commuting-square :
    (PathP (\i -> p1 i -> p2 i) f-ab f-cd) ==
    ((transport p2) ∘ f-ab == f-cd ∘ (transport p1))
  function-pathp==commuting-square = function-pathp==commuting-squareᵉ p1 p2 f-ab f-cd
