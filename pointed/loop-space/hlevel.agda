{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.loop-space.hlevel where

open import base
open import cubical
open import equality-path
open import hlevel.base
open import pointed.base
open import pointed.loop-space

opaque
  isOfHLevel->isContr-Ωⁿ : {ℓ : Level} {A : Type ℓ}
    (i : Nat) -> isOfHLevel (suc i) A -> (a : A) -> isContr ⟨ Ωⁿ i (A , a) ⟩
  isOfHLevel->isContr-Ωⁿ zero h a = a , h a
  isOfHLevel->isContr-Ωⁿ {A = A} (suc n) h a =
    transport (\i -> isContr (fst (Ω-Ωⁿ-path {A∙ = (A , a)} n (~ i)))) rec
    where
    rec : isContr ⟨ Ωⁿ n (Ω (A , a)) ⟩
    rec = isOfHLevel->isContr-Ωⁿ n (h a a) refl

  isContr-Ωⁿ->isOfHLevel : {ℓ : Level} {A : Type ℓ}
    (i : Nat) -> ((a : A) -> isContr ⟨ Ωⁿ i (A , a) ⟩) ->
    isOfHLevel (suc i) A
  isContr-Ωⁿ->isOfHLevel zero f a b = sym (snd (f a) a) >=> (snd (f a) b)
  isContr-Ωⁿ->isOfHLevel {ℓ} {A} (suc i) f a b = isContr-Ωⁿ->isOfHLevel i loop-contr
    where
    loop-contr : (p : a == b) -> isContr ⟨ Ωⁿ i ((a == b) , p) ⟩
    loop-contr p =
      transport (\j -> isContr ⟨ Ωⁿ i (tp j) ⟩)
        (transport (\j -> isContr (fst (Ω-Ωⁿ-path {A∙ = (A , a)} i j)))
          (f a))
      where
      tp : Path (Type∙ ℓ) ((a == a) , refl) ((a == b) , p)
      tp i = (a == (p i)) , (\j -> p (i ∧ j))
