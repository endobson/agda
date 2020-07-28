{-# OPTIONS --cubical --safe --exact-split #-}

module list.powerset where

open import base
open import equality
open import list
open import nat

private
  variable
    ℓ : Level
    A : Type ℓ

powerset : List A -> List (List A)
powerset []        = [ [] ]
powerset (a :: as) = powerset as ++ (map (a ::_) (powerset as))

private

  powerset-contains-only : (as : List A) -> ContainsOnly (\x -> Subsequence A x as) (powerset as)
  powerset-contains-only {A = A} [] (0 , p) =
    transport (\i -> Subsequence A (p (~ i)) []) subsequence-empty
  powerset-contains-only [] (suc _ , ())
  powerset-contains-only {A = A} (a :: as) {a = x} c =
    handle (split-contains-++ (powerset as) (map (a ::_) (powerset as)) c)
    where
    handle : contains x (powerset as) ⊎ contains x (map (a ::_) (powerset as))
             -> Subsequence A x (a :: as)
    handle (inj-l c) = subsequence-drop a (powerset-contains-only as c)
    handle (inj-r c) = handle2 (map-contains' (a ::_) (powerset as) c)
      where
      handle2 : Σ[ x2 ∈ List A ] (contains x2 (powerset as) × (a :: x2 == x))
                -> Subsequence A x (a :: as)
      handle2 ( x2 , c-x2 , p) =
        transport (\i -> Subsequence A (p i) (a :: as))
                  (subsequence-keep a (powerset-contains-only as c-x2))

  powerset-contains-all : (as : List A) -> ContainsAll (\x -> Subsequence A x as) (powerset as)
  powerset-contains-all []        subsequence-empty       = (0 , refl)
  powerset-contains-all (a :: as) (subsequence-drop a ss) =
    ++-contains-left (powerset as) (map (a ::_) (powerset as))
      (powerset-contains-all as ss)
  powerset-contains-all (a :: as) (subsequence-keep a ss) =
    ++-contains-right (powerset as) (map (a ::_) (powerset as))
      (map-contains (a ::_) (powerset as) (powerset-contains-all as ss))

  powerset-contains-exactly :
    (as : List A) -> ContainsExactly (\x -> Subsequence A x as) (powerset as)
  powerset-contains-exactly as = (powerset-contains-only as , powerset-contains-all as)
