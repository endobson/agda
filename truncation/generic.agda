{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.generic where

open import base
open import equality-path
open import equality.square
open import funext
open import hlevel
open import hlevel.base
open import pointed.base
open import pointed.loop-space
open import pointed.loop-space.hlevel
open import pointed.spheres
open import pointed.suspension
open import pointed.suspension-loop-eq

-- Cribbed from Cubical.HITs.Truncation.Base in cubical library.

data HubAndSpokeₙ {ℓ : Level} (n : Nat) (A : Type ℓ) : Type ℓ where
  ∣_∣ : A -> HubAndSpokeₙ n A
  hub : (Sⁿ n -> HubAndSpokeₙ n A) -> HubAndSpokeₙ n A
  spoke : (f : (Sⁿ n -> HubAndSpokeₙ n A)) (x : Sⁿ n) -> hub f == f x

Squashₙ : {ℓ : Level} -> Nat -> Type ℓ -> Type ℓ
Squashₙ zero _ = Lift _ Top
Squashₙ (suc n) A = HubAndSpokeₙ n A

squashₙ : {ℓ : Level} {A : Type ℓ} -> (n : Nat) -> A -> Squashₙ n A
squashₙ zero _ = lift tt
squashₙ (suc _) a = ∣ a ∣

Squashₙ∙ : {ℓ : Level} (n : Nat) (A∙ : Type∙ ℓ) -> Type∙ ℓ
Squashₙ∙ n (A , ★A) = Squashₙ n A , squashₙ n ★A

n-loops==spheres : {ℓ : Level} (n : Nat) (A∙ : Type∙ ℓ) -> Ωⁿ n A∙ == Sⁿ∙ n ->∙∙ A∙
n-loops==spheres zero A∙ = sym (S⁰-maps-path A∙)
n-loops==spheres (suc i) A∙ =
  Ω-Ωⁿ-path i >=> n-loops==spheres i (Ω A∙) >=> sym (Susp∙-Ω-map-path _ _)


module _ {ℓ : Level} {A : Type ℓ} where
  private
    contr-squash-loops :
      ∀ (n : Nat) -> (v : Squashₙ (suc n) A) -> isContr ⟨ Ωⁿ n (Squashₙ (suc n) A , v) ⟩
    contr-squash-loops n v = subst isContr (cong fst (sym pT)) isContr-T₂
      where
      T₁ : Type∙ ℓ
      T₁ = Ωⁿ n (Squashₙ (suc n) A , v)
      T₂ : Type∙ ℓ
      T₂ = Sⁿ∙ n ->∙∙ (Squashₙ (suc n) A , v)
      pT : T₁ == T₂
      pT = n-loops==spheres n _

      isContr-T₂ : isContr ⟨ T₂ ⟩
      isContr-T₂ = (->∙-cons (\_ -> v) refl) , paths
        where
        paths : (f : (Sⁿ∙ n ->∙ (Squashₙ (suc n) A , v))) -> (->∙-cons (\_ -> v) refl) == f
        paths (->∙-cons f p) = \i -> ->∙-cons (f' (~ i)) (p' (~ i))
          where
          f' : Path (Sⁿ n -> Squashₙ (suc n) A) f (\_ -> v)
          f' = funExt (\s -> (sym (spoke f s) >=> spoke f north) >=> p)

          p' : PathP (\i -> f' i north == v) p refl
          p' = compPaths->Square _ _ _ _
            (compPath-refl-right p >=>
             sym (compPath-refl-left p) >=>
             cong (_>=> p) (sym (compPath-sym _)) >=>
             sym (compPath-refl-right _))


  isOfHLevel-Squashₙ : (n : Nat) -> isOfHLevel n (Squashₙ n A)
  isOfHLevel-Squashₙ zero = isContr-Lift isContrTop
  isOfHLevel-Squashₙ (suc n) = isContr-Ωⁿ->isOfHLevel n (contr-squash-loops n)

module _ {ℓ : Level} {A : Type ℓ} where
  contr-spheres : {n : Nat} -> isOfHLevel (suc n) A ->
                  (a : A) -> isContr (Sⁿ∙ n ->∙ (A , a))
  contr-spheres {n} h a =
    subst isContr (cong fst (n-loops==spheres n (A , a)))
          (isOfHLevel->isContr-Ωⁿ n h a)


module _ {ℓA : Level} {A : Type ℓA} {n : Nat} where
  fill-sphere :
    (h : isOfHLevel (suc n) A)
    (s : (Sⁿ n -> A)) -> Σ[ a ∈ A ] (∀ i -> s i == a)
  fill-sphere h s =
    _ , (\i j -> app∙ (isContr->isProp contr-sphere s₂ s₃ j) i)
    where
    contr-sphere : isContr (Sⁿ∙ n ->∙ (A , s north))
    contr-sphere = contr-spheres h (s north)

    s₂ : (Sⁿ∙ n ->∙ (A , s north))
    s₂ = ->∙-cons s refl
    s₃ : (Sⁿ∙ n ->∙ (A , s north))
    s₃ = ->∙-cons (\_ -> app∙ (fst contr-sphere) north) (->∙-path (fst contr-sphere))


module _
  {ℓA ℓP : Level} {A : Type ℓA}
  {n : Nat} {P : Squashₙ (suc n) A -> Type ℓP}
  (h : ∀ a -> isOfHLevel (suc n) (P a)) (f : ∀ a -> P ∣ a ∣)
  where

  ∥ₙ-elim : ∀ a -> P a
  private
    module shared (w : Sⁿ n -> Squashₙ (suc n) A) where
      w' : (i : Sⁿ n) -> P (w i)
      w' i = ∥ₙ-elim (w i)

      t : (i : Sⁿ n) -> P (hub w)
      t i = transport (\j -> P (spoke w i (~ j))) (∥ₙ-elim (w i))

      filled-sphere : Σ[ p ∈ P (hub w) ] (∀ i -> t i == p)
      filled-sphere = fill-sphere (h (hub w)) t

  ∥ₙ-elim ∣ a ∣ = f a
  ∥ₙ-elim (hub w) = fst filled-sphere
    where
    open shared w
  ∥ₙ-elim (spoke w s i) = transP-right hub' spoke' i
    where
    open shared w
    u : P (hub w)
    u = fst filled-sphere

    spoke' : PathP (\i -> P (spoke w s i)) (t s) (w' s)
    spoke' = symP (transport-filler _ _)

    hub' : Path (P (hub w)) u (t s)
    hub' = sym (snd filled-sphere s)

  private
    ∥ₙ-elim-path : ∀ a -> ∥ₙ-elim ∣ a ∣ == f a
    ∥ₙ-elim-path a = refl


module _
  {ℓA ℓB ℓP : Level} {A : Type ℓA} {B : Type ℓB}
  {n : Nat} {P : Squashₙ (suc n) A -> Squashₙ (suc n) B -> Type ℓP}
  (h : ∀ a b -> isOfHLevel (suc n) (P a b)) (f : ∀ a b -> P ∣ a ∣ ∣ b ∣)
  where

  ∥ₙ-elim2 : ∀ a b -> P a b
  ∥ₙ-elim2 = ∥ₙ-elim (\a -> isOfHLevelΠ (suc n) (\b -> h a b)) f'
    where
    f' : ∀ a b -> P ∣ a ∣ b
    f' a = ∥ₙ-elim (h ∣ a ∣) (f a)
