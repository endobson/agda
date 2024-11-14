{-# OPTIONS --cubical --safe --exact-split #-}

module finset.instances.pi where

open import base
open import cubical
open import equality-path
open import equivalence
open import fin
open import fin-algebra
open import finset
open import finset.instances
open import finset.instances.sigma
open import functions
open import funext
open import hlevel
open import isomorphism
open import nat
open import truncation
open import type-algebra
open import univalence

isFinSet-Uninhabited : {ℓA : Level} {A : Type ℓA} -> ¬ A -> isFinSet A
isFinSet-Uninhabited ¬A = ∣ 0 , ¬-Bot-eq ¬A >eq> (equiv⁻¹ Fin-Bot-eq) ∣

private
  isFinSet-FinΠ : {ℓA : Level} {n : ℕ} {A : Fin n -> Type ℓA} ->
                  ((i : Fin n) -> isFinSet (A i)) ->
                  isFinSet (∀ i -> A i)
  isFinSet-FinΠ {n = 0} {A} _ = isFinSet-isContr isContr-0Π
    where
    isContr-0Π : isContr ((i : Fin 0) -> A i)
    isContr-0Π = center , isProp-0Π _
      where
      center : (i : Fin 0) -> A i
      center fz = bot-elim (¬fin-zero fz)
      isProp-0Π : isProp ((i : Fin 0) -> A i)
      isProp-0Π _ _ = funExt (\fz -> bot-elim (¬fin-zero fz))

  isFinSet-FinΠ {n = (suc n)} {A} isFinSet-A = subst isFinSet (isoToPath iso-A) ans⊎
    where
    rec0 : isFinSet (A zero-fin)
    rec0 = isFinSet-A zero-fin
    rec : isFinSet (∀ i -> A (suc-fin i))
    rec = isFinSet-FinΠ (\i -> isFinSet-A (suc-fin i))

    ans⊎ : isFinSet (A zero-fin × ∀ i -> A (suc-fin i))
    ans⊎ = isFinSet-× rec0 rec

    iso-A : Iso (A zero-fin × ∀ i -> A (suc-fin i)) (∀ i -> A i)
    iso-A = iso forward backward fb bf
      where
      forward : (A zero-fin × ∀ i -> A (suc-fin i)) -> (∀ i -> A i)
      forward (az , asuc) = fin-elim az asuc

      backward : (∀ i -> A i) -> (A zero-fin × ∀ i -> A (suc-fin i))
      backward as = as zero-fin , \i -> as (suc-fin i)

      fb : ∀ x -> forward (backward x) == x
      fb as = fin-elim-reduce as

      bf : ∀ x -> backward (forward x) == x
      bf (az , asuc) i =
        fin-elim-reduce-zero {P = A} az asuc i ,
        funExt (fin-elim-reduce-suc {P = A} az asuc) i


opaque
  isFinSet-Π : {ℓA ℓB : Level} {A : Type ℓA} {B : A -> Type ℓB} ->
               (isFinSet A) -> ((a : A) -> isFinSet (B a)) ->
               isFinSet (∀ a -> B a)
  isFinSet-Π {A = A} {B = B} fsA fsB = ∥-bind handle fsA
    where
    handle : Σ[ n ∈ ℕ ] (A ≃ Fin n) -> isFinSet (∀ a -> B a)
    handle (n , eq) = isFinSet-equiv eqΠ fsΠ'
      where
      fsB' : (i : Fin n) -> isFinSet (B (eqInv eq i))
      fsB' = fsB ∘ eqInv eq

      fsΠ' : isFinSet ((i : Fin n) -> B (eqInv eq i))
      fsΠ' = isFinSet-FinΠ fsB'

      eqΠ : ((i : Fin n) -> B (eqInv eq i)) ≃ (∀ a -> B a)
      eqΠ = isoToEquiv (iso f b fb bf)
        where
        f : ((i : Fin n) -> B (eqInv eq i)) -> (∀ a -> B a)
        f bs a = transport (cong B (eqRet eq a)) (bs (eqFun eq a))

        b : (∀ a -> B a) -> ((i : Fin n) -> B (eqInv eq i))
        b bs i = bs (eqInv eq i)

        fb : ∀ x -> f (b x) == x
        fb bs i a = transp (\j -> (B (eqRet eq a (i ∨ j)))) i (bs (eqRet eq a i))

        bf : ∀ x -> b (f x) == x
        bf bs = step1 >=> step2
          where
          ret=sec : ∀ i -> (eqRet eq (eqInv eq i)) == (cong (eqInv eq) (eqSec eq i))
          ret=sec i = isFinSet->isSet fsA _ _ _ _

          step1 : (\(i : Fin n) -> transport (cong B (eqRet eq (eqInv eq i)))
                                             (bs (eqFun eq (eqInv eq i)))) ==
                  (\(i : Fin n) -> transport (cong (B ∘ eqInv eq) (eqSec eq i))
                                             (bs (eqFun eq (eqInv eq i))))
          step1 ii i = transport (cong B (ret=sec i ii)) (bs (eqFun eq (eqInv eq i)))

          step2 : (\(i : Fin n) -> transport (cong (B ∘ eqInv eq) (eqSec eq i))
                                             (bs (eqFun eq (eqInv eq i)))) ==
                  bs
          step2 ii i = transp (\jj -> (B (eqInv eq (eqSec eq i (ii ∨ jj))))) ii (bs (eqSec eq i ii))
