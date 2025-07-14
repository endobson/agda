{-# OPTIONS --cubical --safe --exact-split #-}

module connected.n-type where

open import base
open import cubical
open import funext
open import hlevel.base
open import hlevel.pi
open import hlevel.sigma
open import hlevel.equivalence
open import connected
open import equality-path
open import equivalence
open import isomorphism
open import univalence
open import truncation.generic


precompose : {ℓA ℓB ℓP : Level} {A : Type ℓA} {B : Type ℓB}
             (f : A -> B) (P : B -> Type ℓP) ->
             (∀ b -> P b) -> (∀ a -> P (f a))
precompose f P s a = (s (f a))



module _ {ℓA ℓB ℓP : Level} {A : Type ℓA} {B : Type ℓB} {f : A -> B} where

  private
    isConnectedMap->isEquiv-precompose₀ :
      isConnectedMapₙ₋₂ 0 f -> (P : B -> Type ℓP) -> (∀ b -> isOfHLevel 0 (P b)) -> isEquiv (precompose f P)
    isConnectedMap->isEquiv-precompose₀ c P h = isoToIsEquiv (iso _ inv fb bf)
      where
      inv : (∀ a -> P (f a)) -> (∀ b -> P b)
      inv _ b = fst (h b)

      fb : ∀ g -> (precompose f P) (inv g) == g
      fb g = funExt (\a -> isContr->isProp (h (f a)) _ _)

      bf : ∀ pb -> inv ((precompose f P) pb) == pb
      bf g = funExt (\b -> isContr->isProp (h b) _ _)

    isConnectedMap->isEquiv-precompose⁺ : {n : Nat} ->
      isConnectedMapₙ₋₂ (suc n) f -> (P : B -> Type ℓP) -> (∀ b -> isOfHLevel (suc n) (P b)) -> isEquiv (precompose f P)
    isConnectedMap->isEquiv-precompose⁺ {n} c P h =
      isoToIsEquiv (iso _ inv fb bf) -- record { equiv-proof = ans' }
      where
      inv : (∀ a -> P (f a)) -> (∀ b -> P b)
      inv g b =
        ∥ₙ-elim (\_ -> h b)
          (\ (a , p) -> transport (\i -> P (p i)) (g a))
          (fst (c b))



      fb' : ∀ g a -> (precompose f P) (inv g) a == g a
      fb' g a = ans
        where
        ans : ∥ₙ-elim (\_ -> h (f a))
                (\ (a , p) -> transport (\i -> P (p i)) (g a))
                (fst (c (f a))) ==
              g a
        ans =
          ∥ₙ-elim (\sfib -> isOfHLevelSuc (suc n) (h (f a))
                              (∥ₙ-elim (\_ -> h (f a))
                                (\ (a , p) -> transport (\i -> P (p i)) (g a))
                                sfib)
                              (g a))
            step₂
            (fst (c (f a)))
          where
          step₂ : ∀ (fib@(a₂ , p) : fiber f (f a)) ->
            transport (\i -> P (p i)) (g a₂) == g a
          step₂ (a₂ , p) = g-path
            where
            fib-path : Path (Squashₙ (suc n) (fiber f (f a))) (∣ (a₂ , p) ∣) (∣ (a , refl) ∣)
            fib-path = isContr->isProp (c (f a)) _ _

            convert : fiber f (f a) -> P (f a)
            convert (a' , p') = transport (\i -> P (p' i)) (g a')

            sg-path : Path (Squashₙ (suc n) (P (f a)))
                           (∣ (transport (\i -> P (p i)) (g a₂)) ∣)
                           (∣ (transport (\i -> P (f a)) (g a)) ∣)
            sg-path = cong (∥ₙ-map convert) fib-path

            sg-path₂ : Path (Squashₙ (suc n) (P (f a)))
                            (∣ (transport (\i -> P (p i)) (g a₂)) ∣)
                            (∣ (g a) ∣)
            sg-path₂ = sg-path >=> cong ∣_∣ (transportRefl (g a))

            g-path : Path (P (f a)) (transport (\i -> P (p i)) (g a₂)) (g a)
            g-path = cong (∥ₙ-elim (\_ -> h (f a)) (\x -> x)) sg-path₂

      fb : ∀ g -> (precompose f P) (inv g) == g
      fb g = funExt (fb' g)

      bf' : ∀ pb b -> inv ((precompose f P) pb) b == pb b
      bf' pb b = ans
        where
        ans :
           ∥ₙ-elim (\_ -> h b)
             (\ (a , p) -> transport (\i -> P (p i)) (pb (f a)))
             (fst (c b)) ==
             pb b
        ans =
          ∥ₙ-elim (\sfib -> isOfHLevelSuc (suc n) (h b)
                              (∥ₙ-elim (\_ -> h b)
                                (\ (a , p) -> transport (\i -> P (p i)) (pb (f a)))
                                sfib)
                              (pb b))
            step₂
            (fst (c b))
          where
          step₂ : ∀ (fib@(a , p) : fiber f b) ->
            transport (\i -> P (p i)) (pb (f a)) == (pb b)
          step₂ (a , p) j = transp (\i -> P (p (i ∨ j))) j (pb (p j))


      bf : ∀ pb -> inv ((precompose f P) pb) == pb
      bf pb = funExt (bf' pb)

  isConnectedMap->isEquiv-precompose : {n : Nat} ->
    isConnectedMapₙ₋₂ n f -> (P : B -> Type ℓP) -> (∀ b -> isOfHLevel n (P b)) -> isEquiv (precompose f P)
  isConnectedMap->isEquiv-precompose {0} = isConnectedMap->isEquiv-precompose₀
  isConnectedMap->isEquiv-precompose {suc n} = isConnectedMap->isEquiv-precompose⁺



module _ {ℓA : Level} {A : Type ℓA} {n : Nat} where
  opaque
    isConnected->isConnectedMap : isConnectedₙ₋₂ n A -> isConnectedMapₙ₋₂ n (\(a : A) -> tt)
    isConnected->isConnectedMap c _ =
      ≃-isContr (pathToEquiv (cong (Squashₙ n) (isoToPath (iso for back (\_ -> refl) (\_ -> refl)))))
                c
      where
      for : A -> fiber (\(a : A) -> tt) tt
      for a  = a , refl
      back : fiber (\(a : A) -> tt) tt -> A
      back (a , p)  = a


module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} {n : Nat} where
  opaque
    isConnected->constant-map :
      isConnectedₙ₋₂ n A -> isOfHLevel n B -> (f : A -> B) -> ∀ a₁ a₂ -> f a₁ == f a₂
    isConnected->constant-map c h f a₁ a₂ = pf
      where
      g : A -> Top
      g _ = tt
      isConnected-g : isConnectedMapₙ₋₂ n g
      isConnected-g = isConnected->isConnectedMap c

      P : Top -> Type ℓB
      P _ = B

      eq : isEquiv (precompose g (\_ -> B))
      eq = isConnectedMap->isEquiv-precompose isConnected-g P (\_ -> h)

      f' : (Top -> B)
      f' = isEqInv eq f

      pf' : precompose g P f' == f
      pf' = isEqSec eq f

      pf : f a₁ == f a₂
      pf = (\i -> pf' (~ i) a₁) >=> (\i -> pf' i a₂)
