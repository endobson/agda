{-# OPTIONS --cubical --safe --exact-split #-}

module suspension.connected where

open import base
open import cubical
open import isomorphism
open import equality-path
open import equality.square
open import pointed.suspension
open import pushout
open import hlevel.base
open import hlevel
open import equivalence
open import connected
open import connected.n-type
open import truncation.generic

-- DO NOT SUBMIT

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} where
  Susp-map : (A -> B) -> Susp A -> Susp B
  Susp-map _ north = north
  Susp-map _ south = south
  Susp-map f (meridian x i) = meridian (f x) i


module _ {ℓ : Level} {A : Type ℓ} where
  module _ (n : Nat) where
    private
      Sₙ⁺ : Type ℓ -> Type ℓ
      Sₙ⁺ = Squashₙ (suc n)

    SquashSusp-eq⁺ : (Sₙ⁺ (Susp A)) ≃ (Sₙ⁺ (Susp (Sₙ⁺ A)))
    SquashSusp-eq⁺ = isoToEquiv (iso for back fb bf)
      where
      for : (Sₙ⁺ (Susp A)) -> (Sₙ⁺ (Susp (Sₙ⁺ A)))
      for = ∥ₙ-map (Susp-map ∣_∣)

      back' : (Susp (Sₙ⁺ A)) -> (Sₙ⁺ (Susp A))
      back' north = ∣ north ∣
      back' south = ∣ south ∣
      back' (meridian sa i) =
        ∥ₙ-elim (\_ -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n))
                                      (∣ north ∣) (∣ south ∣)) back'' sa i
        where
        back'' : A -> Path (Sₙ⁺ (Susp A)) (∣ north ∣) (∣ south ∣)
        back'' a i = ∣ meridian a i ∣

      back : (Sₙ⁺ (Susp (Sₙ⁺ A))) -> (Sₙ⁺ (Susp A))
      back = ∥ₙ-elim (\_ -> isOfHLevel-Squashₙ (suc n)) back'


      fb : ∀ x -> for (back x) == x
      fb =
        ∥ₙ-elim
          (\x -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n))
                                (for (back x)) x)
          fb'
        where
        fb' : ∀ (Σsa : Susp (Sₙ⁺ A)) -> for (back ∣ Σsa ∣) == ∣ Σsa ∣
        fb' north = refl
        fb' south = refl
        fb' (meridian sa j) =
          ∥ₙ-elim
          (\x -> isOfHLevelPathP' (suc n)
                  (\i -> isOfHLevelPath (suc (suc n))
                         (isOfHLevelSuc (suc n)
                              (isOfHLevel-Squashₙ (suc n)))
                         (for (back (∣ meridian x i ∣))) (∣ meridian x i ∣))
                  refl refl)
          (\_ _ -> refl) sa j


      bf : ∀ x -> back (for x) == x
      bf = ∥ₙ-elim
            (\x -> isOfHLevelPath (suc n) (isOfHLevel-Squashₙ (suc n))
                                  (back (for x)) x)
            bf'
        where
        bf' : ∀ (sa : Susp A) -> back (for ∣ sa ∣) == ∣ sa ∣
        bf' north = refl
        bf' south = refl
        bf' (meridian a i) = refl

  SquashSusp-eq : (n : Nat) -> (Squashₙ n (Susp A)) ≃ (Squashₙ n (Susp (Squashₙ n A)))
  SquashSusp-eq zero = idEquiv _
  SquashSusp-eq (suc n) = SquashSusp-eq⁺ n


module _ {ℓ : Level} {A : Type ℓ} where
  isContr-Susp : isContr A -> isContr (Susp A)
  isContr-Susp (a , a-center) = north , s-center
    where
    s-center : (sa : Susp A) -> north == sa
    s-center north = refl
    s-center south = meridian a
    s-center (meridian a₂ i) j =
      rotate-square-ARBC->ABRC (\i j -> meridian (a-center a₂ j) i) i j


private
  module _ {ℓ : Level} {A : Type ℓ} {n : Nat} (c : isConnectedₙ₋₂ (suc n) A) where

    isConnected-Susp⁺ : isConnectedₙ₋₂ (suc (suc n)) (Susp A)
    isConnected-Susp⁺ = ≃-isContr (equiv⁻¹ (step₁ >eq> step₂)) isContrTop
      where
      for : (Squashₙ (suc (suc n)) (Susp (Squashₙ (suc (suc n)) A))) -> Top
      for _ = tt

      back : Top -> (Squashₙ (suc (suc n)) (Susp (Squashₙ (suc (suc n)) A)))
      back _ = ∣ north ∣

      fb : ∀ x -> for (back x) == x
      fb _ = refl

      h : isOfHLevel (suc n)
            (Path (Squashₙ (suc (suc n)) (Susp (Squashₙ (suc (suc n)) A)))
                  (∣ north ∣) (∣ south ∣))
      h = isOfHLevel-Squashₙ (suc (suc n)) _ _

      extract : A -> Path (Squashₙ (suc (suc n)) (Susp (Squashₙ (suc (suc n)) A)))
                          (∣ north ∣) (∣ south ∣)
      extract a i = ∣ meridian (∣ a ∣) i ∣

      extract-same : ∀ a₁ a₂ -> extract a₁ == extract a₂
      extract-same = isConnected->constant-map c h extract


      bf' : ∀ x -> back (for ∣ x ∣) == ∣ x ∣
      bf' north = refl
      bf' south = ∥ₙ-elim (\_ -> h) extract (fst c)
      bf' (meridian ta i) = path i
        where
        path : PathP (\i -> (back (for (∣ meridian ta i ∣))) == (∣ meridian ta i ∣))
                     refl (∥ₙ-elim (\_ -> h) extract (fst c))
        path =
          ∥ₙ-elim
            (\ta₂ ->
              isOfHLevelPathP' (suc n) (\i -> isOfHLevelSuc (suc n) (isOfHLevel-Squashₙ (suc (suc n))
                                                (∣ north ∣) (∣ meridian ta i ∣)))
              _ (∥ₙ-elim (\_ -> h) extract ta₂))
            step₂
            (fst c)
          where
          step₂ : (a₂ : A) ->
                  PathP (\i -> (∣ north ∣) == (∣ meridian ta i ∣))
                        refl (\i -> ∣ meridian (∣ a₂ ∣) i ∣)
          step₂ a₂ =
            ∥ₙ-elim
              (\ta₁ ->
                 isOfHLevelSuc (suc n)
                   (isOfHLevelPathP' (suc n) (\i -> isOfHLevelSuc (suc n) (isOfHLevel-Squashₙ (suc (suc n))
                                                      (∣ north ∣) (∣ meridian ta₁ i ∣)))
                    _ (\i -> ∣ meridian (∣ a₂ ∣) i ∣)))
              step₃
              ta

            where
            step₃ : (a₁ : A) -> PathP (\i -> (∣ north ∣) == (∣ meridian (∣ a₁ ∣) i ∣))
                                      refl (\i -> ∣ meridian (∣ a₂ ∣) i ∣)
            step₃ a₁ = rotate-square-ARBC->ABRC (▪ᵀ m-path)
             where
             m-path : (\i -> ∣ meridian (∣ a₂ ∣) i ∣) == (\i -> ∣ meridian (∣ a₁ ∣) i ∣)
             m-path = extract-same a₂ a₁


      bf : ∀ x -> back (for x) == x
      bf = ∥ₙ-elim (\_ -> isOfHLevelPath (suc (suc n)) (isOfHLevel-Squashₙ (suc (suc n))) _ _) bf'

      step₂ : (Squashₙ (suc (suc n)) (Susp (Squashₙ (suc (suc n)) A))) ≃ Top
      step₂ = isoToEquiv (iso for back fb bf)


      step₁ : (Squashₙ (suc (suc n)) (Susp A)) ≃
              (Squashₙ (suc (suc n)) (Susp (Squashₙ (suc (suc n)) A)))
      step₁ = SquashSusp-eq (suc (suc n))


  module _ {ℓ : Level} {A : Type ℓ} where
    isConnected-Susp₀ : isConnectedₙ₋₂ 1 (Susp A)
    isConnected-Susp₀ = ∣ north ∣ , \y -> isOfHLevel-Squashₙ 1 _ _

module _ {ℓ : Level} {A : Type ℓ} where
  opaque
    isConnected-Susp : {n : Nat} (c : isConnectedₙ₋₂ n A) -> isConnectedₙ₋₂ (suc n) (Susp A)
    isConnected-Susp {zero} _ = isConnected-Susp₀
    isConnected-Susp {suc n} c = isConnected-Susp⁺ c
