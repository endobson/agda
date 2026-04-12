{-# OPTIONS --cubical --safe --exact-split #-}

module pushout.spheres where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical hiding (glue)
open import equality-path
open import equivalence
open import isomorphism
open import nat
open import pointed.spheres
open import pointed.suspension
open import pushout
open import pushout.identites
open import pushout.suspension
open import univalence

private
  Sphere-Join-iso₀ : {ℓ : Level} (A : Type ℓ) -> Iso (Join (Sⁿ 0) A) (Susp A)
  Sphere-Join-iso₀ A = iso fwd bkw fb bf
    where
    fwd : (Join (Susp Bot) A) -> (Susp A)
    fwd (inj-l north) = north
    fwd (inj-l south) = south
    fwd (inj-r a) = south
    fwd (glue (north , a) i) = meridian a i
    fwd (glue (south , a) i) = south

    bkw : (Susp A) -> (Join (Susp Bot) A)
    bkw north = (inj-l north)
    bkw south = (inj-l south)
    bkw (meridian a i) = (glue (north , a) >=> sym (glue (south , a))) i

    fb : ∀ x -> fwd (bkw x) == x
    fb north = refl
    fb south = refl
    fb (meridian a i) j = ans j i
      where
      ans : cong fwd (glue (north , a) >=> sym (glue (south , a))) ==
            meridian a
      ans =
        cong-trans fwd (glue (north , a)) (sym (glue (south , a))) >=>
        compPath-refl-right (meridian a)

    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l north) = refl
    bf (inj-l south) = refl
    bf (inj-r a) = glue (south , a)
    bf (glue (south , a) i) = \j -> glue (south , a) (i ∧ j)
    bf (glue (north , a) i) j = (transP-left raw (compPath-refl-right _)) j i
      where
      raw : PathP (\i -> inj-l north == (glue (south , a) i))
                (glue (north , a) >=> sym (glue (south , a)))
                (glue (north , a) >=> refl)
      raw i = (glue (north , a)) >=> (\j -> glue (south , a) (i ∨ ~ j))


Sphere-Join-eq : ∀ m n -> (Join (Sⁿ m) (Sⁿ n)) ≃ (Sⁿ (suc (m + n)))
Sphere-Join-eq zero n = isoToEquiv (Sphere-Join-iso₀ (Sⁿ n))
Sphere-Join-eq (suc m) n = pathToEquiv step3
  where
  step1 : (Susp (Sⁿ m)) == Join Boolean (Sⁿ m)
  step1 = ua (Susp-Join-eq (Sⁿ m))
  step2 : Join Boolean (Sⁿ m) == Join (Sⁿ m) Boolean
  step2 = isoToPath Join-swap-iso
  step3 : (Join (Sⁿ (suc m)) (Sⁿ n)) == (Sⁿ (suc (suc (m + n))))
  step3 =
    cong (\x -> (Join x (Sⁿ n))) (step1 >=> step2) >=>
    ua (Join-assoc-eq _ _ _) >=>
    sym (cong (\x -> (Join (Sⁿ m) x)) (ua (Susp-Join-eq (Sⁿ n)))) >=>
    ua (Sphere-Join-eq m (suc n)) >=>
    cong Sⁿ (cong suc (+'-right-suc {m} {n}))
