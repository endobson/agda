{-# OPTIONS --cubical --safe --exact-split #-}

module truncation.generic.path where

open import base
open import cubical
open import hlevel
open import isomorphism
open import equivalence
open import equality-path
open import hlevel.htype
open import truncation.generic


private
  module _ {ℓ : Level} {A : Type ℓ} (a₁ a₂ : A) where
  
    squashed-path-eq₀ : (Squashₙ 0 (a₁ == a₂)) ≃
                        (squashₙ 1 a₁ == squashₙ 1 a₂)
    squashed-path-eq₀ = isContr->Equiv isContr₁ isContr₂
      where
      isContr₁ : isContr (Squashₙ 0 (a₁ == a₂))
      isContr₁ = isOfHLevel-Squashₙ {A = a₁ == a₂} 0
      isContr₂ : isContr (squashₙ 1 a₁ == squashₙ 1 a₂)
      isContr₂ = isProp->isContrPath (isOfHLevel-Squashₙ 1) _ _


  module _ {ℓ : Level} {A : Type ℓ} (a : A) where
    squashed-path-eq₀-refl : 
      eqFun (squashed-path-eq₀ a a) (squashₙ 0 (reflᵉ a)) == refl
    squashed-path-eq₀-refl = 
      isOfHLevelSuc 1 (isOfHLevel-Squashₙ 1) _ _ _ _




  module _ {ℓ : Level} {A : Type ℓ} (n : Nat) where
    S : Type ℓ
    S = Squashₙ (suc (suc n)) A
    hS : isOfHLevel (suc (suc n)) S
    hS = isOfHLevel-Squashₙ (suc (suc n))
    

    Encode : S -> S -> Σ (Type ℓ) (isOfHLevel (suc n))
    Encode =
      ∥ₙ-elim2
        (\_ _ -> isOfHLevel-hType (suc n))
        (\a₁ a₂ -> (Squashₙ (suc n) (a₁ == a₂)) , isOfHLevel-Squashₙ (suc n))

    Encode' : S -> S -> (Type ℓ)
    Encode' x y = fst (Encode x y)

    encoded-refl : ∀ (s : S) -> Encode' s s
    encoded-refl = ∥ₙ-elim
      (\s -> isOfHLevelSuc (suc n) (snd (Encode s s)))
      (\a -> squashₙ (suc n) refl)

    f : (s₁ s₂ : S) -> (Encode' s₁ s₂) -> (s₁ == s₂)
    f = ∥ₙ-elim2
      (\s₁ s₂ -> isOfHLevelΠ (suc (suc n)) (\e -> 
        isOfHLevelSuc (suc n) (isOfHLevel-Squashₙ (suc (suc n)) s₁ s₂)))
      (\a₁ a₂ -> ∥ₙ-elim
        (\_ -> isOfHLevel-Squashₙ (suc (suc n)) (∣ a₁ ∣) (∣ a₂ ∣))
        (\p i -> ∣ p i ∣))

    b : (s₁ s₂ : S) -> (s₁ == s₂) -> (Encode' s₁ s₂)
    b = ∥ₙ-elim2
      (\s₁ s₂ -> isOfHLevelΠ (suc (suc n)) (\e -> 
        isOfHLevelSuc (suc n) (snd (Encode s₁ s₂))))
      b' 
      where
      b' : (a₁ a₂ : A) -> (p : squashₙ (suc (suc n)) a₁ == squashₙ (suc (suc n)) a₂) -> 
           Squashₙ (suc n) (a₁ == a₂)
      b' a₁ _ = 
        J (\s₂ p -> Encode' (∣ a₁ ∣) s₂) (squashₙ (suc n) refl)

    b-refl : ∀ (s₁ : S) -> b s₁ s₁ refl == encoded-refl s₁
    b-refl =
      ∥ₙ-elim
        (\s₁ -> isOfHLevelSuc (suc n) (isOfHLevelPath (suc n) (snd (Encode s₁ s₁)) _ _))
        (\a -> JRefl {x = (∣ a ∣)} (\s₂ p -> Encode' (∣ a ∣) s₂) (squashₙ (suc n) refl))

    f-refl : ∀ (s₁ : S) -> f s₁ s₁ (encoded-refl s₁) == refl
    f-refl =
      ∥ₙ-elim
        (\s₁ -> isOfHLevelPath (suc (suc n)) (isOfHLevelPath (suc (suc n)) hS _ _) _ _)
        (\a i -> refl)

    fb-refl : ∀ (s₁ : S) -> (f s₁ s₁ (b s₁ s₁ refl)) == refl
    fb-refl s₁ = cong (f s₁ s₁) (b-refl s₁) >=> f-refl s₁

    bf : ∀ s₁ s₂ -> (e : Encode' s₁ s₂) -> b s₁ s₂ (f s₁ s₂ e) == e
    bf = ∥ₙ-elim2
      (\s₁ s₂ -> isOfHLevelΠ (suc (suc n)) (\e -> isOfHLevelPath (suc (suc n)) 
        (isOfHLevelSuc (suc n) (snd (Encode s₁ s₂))) _ _))
      bf'
      where
      module _ (a₁ a₂ : A) where
        s₁ s₂ : S
        s₁ = ∣ a₁ ∣
        s₂ = ∣ a₂ ∣
        handle : (p : a₁ == a₂) -> b s₁ s₂ (f s₁ s₂ (squashₙ (suc n) p)) == (squashₙ (suc n) p)
        handle p = ans
          where
          p' : _
          p' = (cong (squashₙ (suc (suc n))) p)

          ans : transport (\i -> Encode' s₁ (p' i)) (squashₙ (suc n) refl) == squashₙ (suc n) p
          ans j = transp (\i -> Encode' s₁ (p' (i ∨ j))) j (squashₙ (suc n) (\i -> p (i ∧ j)))

        bf' : (e : Squashₙ (suc n) (a₁ == a₂)) -> b s₁ s₂ (f s₁ s₂ e) == e
        bf' = ∥ₙ-elim
          (\e -> isOfHLevelPath (suc n) (snd (Encode s₁ s₂)) _ _)
          handle



    
    module _ (s₁ s₂ : S) where
      fb : ∀ p -> f s₁ s₂ (b s₁ s₂ p) == p
      fb p = transP-sides fbp (fb-refl s₁) pp
        where
        fbp : PathP (\i -> s₁ == (p (~ i))) (f s₁ s₂ (b s₁ s₂ p)) (f s₁ s₁ (b s₁ s₁ refl)) 
        fbp i = f s₁ (p (~ i)) (b s₁ (p (~ i)) (\j -> p (j ∧ (~ i))))
        pp : PathP (\i -> s₁ == (p i)) refl p
        pp i j = p (j ∧ i)
        

      encode-eq : (Encode' s₁ s₂) ≃ (s₁ == s₂)
      encode-eq = isoToEquiv (iso (f s₁ s₂) (b s₁ s₂) fb (bf s₁ s₂))


    squashed-path-eq⁺ : (a₁ a₂ : A) ->
      (Squashₙ (suc n) (a₁ == a₂)) ≃
      (squashₙ (suc (suc n)) a₁ == squashₙ (suc (suc n)) a₂)
    squashed-path-eq⁺ a₁ a₂ = encode-eq (∣ a₁ ∣) (∣ a₂ ∣)


    squashed-path-eq⁺-refl : (a : A) ->
      eqFun (squashed-path-eq⁺ a a) (squashₙ (suc n) refl) == refl
    squashed-path-eq⁺-refl a = f-refl (squashₙ (suc (suc n)) a)


squashed-path-eq : {ℓ : Level} {A : Type ℓ} (n : Nat) (a₁ a₂ : A) ->
  (Squashₙ n (a₁ == a₂)) ≃
  (squashₙ (suc n) a₁ == squashₙ (suc n) a₂)
squashed-path-eq zero = squashed-path-eq₀
squashed-path-eq (suc n) = squashed-path-eq⁺ n
  

squashed-path-eq-refl : {ℓ : Level} {A : Type ℓ} (n : Nat) (a : A) ->
  eqFun (squashed-path-eq n a a) (squashₙ n refl) == refl
squashed-path-eq-refl zero = squashed-path-eq₀-refl
squashed-path-eq-refl (suc n) = squashed-path-eq⁺-refl n
