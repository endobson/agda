{-# OPTIONS --cubical --safe --exact-split #-}

module subset.subspace where

open import base
open import equality-path
open import equality.square
open import equivalence
open import functions
open import functions.embedding
open import hlevel
open import subset

module _ {ℓD ℓS : Level} {D : Type ℓD} (S : Subtype D ℓS) where
  record Subspace : Type (ℓ-max ℓD ℓS) where
    constructor _,_
    field
      value : D
      prop : ⟨ S value ⟩

module _ {ℓD ℓS : Level} {D : Type ℓD} {S : Subtype D ℓS} where

  Subspace-path : {s1 s2 : Subspace S} -> (Subspace.value s1) == (Subspace.value s2) -> s1 == s2
  Subspace-path           p i .Subspace.value = p i
  Subspace-path {s1} {s2} p i .Subspace.prop =
    isProp->PathPᵉ (\i -> snd (S (p i))) (Subspace.prop s1) (Subspace.prop s2) i

  opaque
    isProp-Subspace : isProp D -> isProp (Subspace S)
    isProp-Subspace isPropD (v1 , p1) (v2 , p2) = Subspace-path (isPropD v1 v2)

    isSet-Subspace : isSet D -> isSet (Subspace S)
    isSet-Subspace isSetD (v1 , p1) (v2 , p2) q1 q2 i j =
      value-square i j , prop-square i j
      where
      vq1 : v1 == v2
      vq1 = cong Subspace.value q1
      vq2 : v1 == v2
      vq2 = cong Subspace.value q2
      value-square : vq1 == vq2
      value-square = isSetD v1 v2 vq1 vq2
      prop-square : SquareP (\i j -> ⟨ S (value-square i j) ⟩)
                      (cong Subspace.prop q1) (cong Subspace.prop q2) refl refl
      prop-square = isSet->SquareP (\i j -> isProp->isSet (snd (S (value-square i j))))


    isEmbedding-Subspace-value : isEmbedding (Subspace.value {D = D} {S = S})
    isEmbedding-Subspace-value = eqInv isEmbedding-eq-hasPropFibers prop-fibers
      where
      prop-fibers : ∀ (d : D) -> isProp (fiber (Subspace.value {D = D} {S = S}) d)
      prop-fibers d (s1@(v1 , _) , q1) (s2@(v2 , _), q2) = \i -> s-path i , q-path i
        where
        q3 : v1 == v2
        q3 = q1 ∙∙ refl ∙∙ sym q2

        q3-filler : Square (sym q1) (sym q2) refl q3
        q3-filler = square-filler (sym q1) (sym q2) refl

        q-path : PathP (\i -> q3 i == d) q1 q2
        q-path i j = q3-filler i (~ j)

        s-path : s1 == s2
        s-path = Subspace-path q3
