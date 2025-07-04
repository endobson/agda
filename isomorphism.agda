{-# OPTIONS --cubical --safe --exact-split #-}

module isomorphism where

open import base
open import cubical
open import equality-path
open import equality.square
open import equivalence.base
open import functions
open import hlevel.base
open import sigma.base

open import isomorphism.base public

private
  variable
    ℓ : Level
    A B C : Type ℓ

module _ where
  open Iso

  -- Common isomorphism operations
  _∘ⁱ_ : Iso B C -> Iso A B -> Iso A C
  fun (f ∘ⁱ g) = fun f ∘ fun g
  inv (f ∘ⁱ g) = inv g ∘ inv f
  rightInv (f ∘ⁱ g) c = (\i -> (fun f (rightInv g (inv f c) i))) >=> rightInv f c
  leftInv (f ∘ⁱ g) a = (\i -> (inv g (leftInv f (fun g a) i))) >=> leftInv g a

  _>iso>_ : Iso A B -> Iso B C -> Iso A C
  _>iso>_ f g = g ∘ⁱ f

  iso⁻¹ : Iso A B -> Iso B A
  fun (iso⁻¹ f) = inv f
  inv (iso⁻¹ f) = fun f
  rightInv (iso⁻¹ f) = leftInv f
  leftInv  (iso⁻¹ f) = rightInv f

  id-iso : Iso A A
  fun id-iso a = a
  inv id-iso a = a
  rightInv id-iso _ = refl
  leftInv  id-iso _ = refl

  -- Properties of the common isomorphisms
  ∘ⁱ-id-left : {f : Iso A B} -> id-iso ∘ⁱ f == f
  fun (∘ⁱ-id-left {f = f} i) = fun f
  inv (∘ⁱ-id-left {f = f} i) = inv f
  rightInv (∘ⁱ-id-left {f = f} i) b = compPath-refl-right (rightInv f b) i
  leftInv (∘ⁱ-id-left {f = f} i) a = compPath-refl-left (leftInv f a) i

  -- Convert a path to an isomorphism
  path->iso : A == B -> Iso A B
  fun (path->iso p) = transport p
  inv (path->iso p) = transport (sym p)
  rightInv (path->iso p) b =
    transport-twice p (sym p) b >=>
    cong (\p -> transport p b) (compPath-sym (sym p)) >=>
    transportRefl b
  leftInv (path->iso p) a =
    transport-twice (sym p) p a >=>
    cong (\p -> transport p a) (compPath-sym p) >=>
    transportRefl a

module _ (iso : Iso A B) where
  open Iso iso renaming
    ( fun      to f
    ; inv      to g
    ; rightInv to s
    ; leftInv  to t
    )

  -- We now want to show that the fibers of f are contractible.
  -- That is:
  --   ∀ (y : B) -> isContr (fiber f).
  -- Remember that:
  -- isContr X :
  --   Σ[ x₁ ∈ X ] (∀ (x₂ : X) -> x₁ == x₂)
  -- fiber f b :
  --   Σ[ a : A ] (f a == b)

  -- Expanded out this is:
  --   ∀ (y : B) -> Σ[ fi₁ ∈ (fiber f y) ] ((fi₂ : (fiber f y)) -> fi₁ == fi₂)
  --   ∀ (y : B)
  --     -> Σ[ fi₁ ∈ Σ[ a₁ : A ] (f a₁ == y) ]
  --          (∀ (fi₂ : Σ[ a₂ : A ] (f a₂ == y) ])
  --             -> fi₁ == fi₂)
  --
  -- In English this is:
  --   For all y in B, there exists an a₁ such that (f a₁) is equivalent to y via path p₁, and
  --   that for any a₂ such that (f a₂) is equivalent to y via path p₂, then p₁ and p₂ are path
  --   equivalent.
  --
  -- To do this we will first show that for any given y and two representatives of the
  -- fiber, that we have a path between the representatives.
  private
    module _ (y : B) (a1 a2 : A) (p1 : f a1 == y) (p2 : f a2 == y) where

      -- We need to show that we have a square with the following shape
      --
      --      (cong f pa)
      --
      --   (f a1) --- (f a2)
      --     |          |
      --  p1 |          | p2
      --     |          |
      --     y  ------  y
      --
      --         refl
      --
      -- where we have the choice of what path pa to use.

      --  To do this we will construct a similar square in A and then apply f and s to it.
      --
      --             (cong g (cong f pa))
      --
      --           (g (f a1)) - (g (f a2))
      --                |          |
      --    (cong g p1) |          | (cong g p2)
      --                |          |
      --              (g y) ---- (g y)
      --
      --                    refl

      -- To construct this square we will first construct five other squares that form the rest
      -- of a cube and push the top down to this base square.

      -- The key part of the construction is that while we have a path of the form (f
      -- a1 == f a2) already (sym p1 ∙∙ refl ∙∙ p2), it isn't clear that we can
      -- factor the f out and maintain the other three sides of the square.


      -- First give names to the sides on the bottom.
      g-p1 : g (f a1) == g y
      g-p1 = cong g p1

      g-p2 : g (f a2) == g y
      g-p2 = cong g p2

      left-square : Square (t a1) refl g-p1 _
      left-square = square-filler (t a1) refl g-p1

      right-square : Square (t a2) refl g-p2 _
      right-square = square-filler (t a2) refl g-p2

      -- The top left and top right sides are determined by the left and right
      -- squares.
      TL : a1 == g y
      TL = square-final-side left-square

      TR : a2 == g y
      TR = square-final-side right-square

      -- TD is refl
      -- TU is pa; our path from a1 to a2

      top-square' : Square (sym TL) (sym TR) refl _
      top-square' = (square-filler (sym TL) (sym TR) refl)

      pa : a1 == a2
      f-pa : f a1 == f a2
      g-f-pa : g (f a1) == g (f a2)

      pa = square-final-side top-square'
      f-pa = cong f pa
      g-f-pa = cong g f-pa

      -- Flip up/down so that pa and refl are in the right spots for later
      top-square : Square TL TR pa refl
      top-square i j = top-square' i (~ j)

      -- Construct the last two sides
      up-square : Square (t a1) (t a2) g-f-pa pa
      up-square i j = t (pa i) j

      down-square : ConstantSquare (g y)
      down-square i j = g y


      -- Pull our square back to the base using the sides
      base-square : Square g-p1 g-p2 g-f-pa refl
      base-square i j =
        hcomp (\ k -> \ { (i = i0) -> left-square  j (~ k)
                        ; (i = i1) -> right-square j (~ k)
                        ; (j = i0) -> up-square    i (~ k)
                        ; (j = i1) -> down-square  i (~ k)})
              (top-square i j)

      -- Apply f to the base and push it back up to the top using s
      top-square2 : Square p1 p2 f-pa refl
      top-square2 i j =
        hcomp (\ k -> \ { (i = i0) -> s (p1 j)     k
                        ; (i = i1) -> s (p2 j)     k
                        ; (j = i0) -> s (f (pa i)) k
                        ; (j = i1) -> s y          k})
              (f (base-square i j))

      -- Finally construct the fiber path
      opaque
        fiber-path : Path (fiber f y) (a1 , p1) (a2 , p2)
        fiber-path i = (pa i , top-square2 i)

    contractible-fibers : ∀ (y : B) -> isContr (fiber f y)
    contractible-fibers y .fst .fst = (g y)
    contractible-fibers y .fst .snd = (s y)
    contractible-fibers y .snd (a2 , p2) = fiber-path y (g y) a2 (s y) p2

  isoToIsEquiv : isEquiv f
  isoToIsEquiv .equiv-proof = contractible-fibers

isoToEquiv : Iso A B -> A ≃ B
isoToEquiv i .fst = _
isoToEquiv i .snd = isoToIsEquiv i

isoToEquiv-id-iso : {A : Type ℓ} -> (isoToEquiv id-iso) == (idEquiv A)
isoToEquiv-id-iso = ΣProp-path isProp-isEquiv refl

equivToIso : A ≃ B -> Iso A B
equivToIso e .Iso.fun = eqFun e
equivToIso e .Iso.inv = eqInv e
equivToIso e .Iso.rightInv = eqSec e
equivToIso e .Iso.leftInv = eqRet e

pathToIso : A == B -> Iso A B
pathToIso p .Iso.fun = transport p
pathToIso p .Iso.inv = transport (sym p)
pathToIso p .Iso.rightInv b =
  transport-twice p (sym p) b
  >=> (\i -> transport (compPath-sym (sym p) i) b)
  >=> transportRefl b
pathToIso p .Iso.leftInv a =
  transport-twice (sym p) p a
  >=> (\i -> transport (compPath-sym p i) a)
  >=> transportRefl a

-- In sets isomorphisms with equal foward functions are equal
module _ (hA : isSet A) (hB : isSet B) {iso₁ iso₂ : Iso A B}
         (p-fun : (Iso.fun iso₁) == (Iso.fun iso₂)) where
  private
    p-inv : (Iso.inv iso₁) == (Iso.inv iso₂)
    p-inv i b =
      (cong (Iso.inv iso₁) (sym (Iso.rightInv iso₂ b))
       >=> (\ j -> (Iso.inv iso₁ (p-fun (~ j) (Iso.inv iso₂ b))))
       >=> (Iso.leftInv iso₁ (Iso.inv iso₂ b))) i

    p-rightInv : (b : B) -> PathP (\i -> (p-fun i (p-inv i b)) == b)
                                  (Iso.rightInv iso₁ b)
                                  (Iso.rightInv iso₂ b)
    p-rightInv b = isProp->PathP (\_ -> hB _ _)

    p-leftInv : (a : A) -> PathP (\i -> (p-inv i (p-fun i a)) == a)
                                 (Iso.leftInv iso₁ a)
                                 (Iso.leftInv iso₂ a)
    p-leftInv a = isProp->PathP (\_ -> hA _ _)

  isSet-iso-path : iso₁ == iso₂
  Iso.fun (isSet-iso-path i) = p-fun i
  Iso.inv (isSet-iso-path i) = p-inv i
  Iso.rightInv (isSet-iso-path i) b = p-rightInv b i
  Iso.leftInv  (isSet-iso-path i) a = p-leftInv a i


isProp->iso : (A -> B) -> (B -> A) -> isProp A -> isProp B -> Iso A B
isProp->iso f g ha hb = iso f g (\_ -> hb _ _) (\_ -> ha _ _)
