{-# OPTIONS --cubical --safe --exact-split #-}

module finset.finitely-indexed where

open import base
open import cubical
open import discrete
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finset
open import finset.instances
open import finset.instances.base
open import finset.search
open import functions
open import hlevel
open import isomorphism
open import relation
open import sigma.base
open import sum
open import truncation
open import without-point

private
  incr-size : {ℓB : Level} {B : Type ℓB} -> (b : B) -> isFinSet (WithoutPoint B b) ->
              Discrete B -> isFinSet B
  incr-size {B = B} b fs discB = ∥-map handle fs
    where
    handle' : Σ[ n ∈ Nat ] (WithoutPoint B b ≃ FinT n) ->
              Σ[ n ∈ Nat ] (B ≃ FinT n)
    handle' (n , eqWb) = suc n , isoToEquiv (iso f g fg gf)
      where
      f : B -> FinT (suc n)
      f b2 with discB b2 b
      ... | (yes _) = inj-l tt
      ... | (no ¬p) = inj-r (eqFun eqWb (b2 , ¬p))

      g : FinT (suc n) -> B
      g (inj-l tt) = b
      g (inj-r i) = WithoutPoint.value (eqInv eqWb i)

      fg : isSectionOf f g
      fg (inj-l tt) with (discB b b)
      ... | (yes _) = refl
      ... | (no ¬p) = bot-elim (¬p refl)
      fg i'@(inj-r i) with (discB (g i') b)
      ... | (yes p) = bot-elim (WithoutPoint.¬point (eqInv eqWb i) p)
      ... | (no ¬p) = (cong inj-r (cong (eqFun eqWb) (WithoutPoint-path refl) >=>
                                   eqSec eqWb i))

      gf : isRetractionOf f g
      gf b2 with (discB b2 b)
      ... | (yes p) = sym p
      ... | (no ¬p) = cong WithoutPoint.value (eqRet eqWb (b2 , ¬p))


    handle : Σ[ n ∈ Nat ] (WithoutPoint B b ≃ Fin n) ->
             Σ[ n ∈ Nat ] (B ≃ Fin n)
    handle = subst (\F -> Σ[ n ∈ Nat ] (WithoutPoint B b ≃ F n) ->
                          Σ[ n ∈ Nat ] (B ≃ F n)) path
                   handle'
      where
      path : Path ((n : Nat) -> Type₀) _ _
      path = (\i n -> FinT=Fin n i)



  FinT-sur-dec : {ℓB : Level} {B : Type ℓB}
                 (n : Nat) -> (f : FinT n -> B) -> isSurjection f -> Discrete B ->
                 isFinSet B
  FinT-sur-dec {B = B} zero f sur-f discB = isFinSet-Uninhabited ¬B
    where
    ¬B : ¬ B
    ¬B b = unsquash isPropBot (∥-map fst (sur-f b))
  FinT-sur-dec {B = B} (suc n) f sur-f discB =
    either (unsquash isProp-isFinSet ∘ ∥-map point-case) avoid-case search-res
    where
    b = f (inj-l tt)

    f' : FinT n -> B
    f' = f ∘ inj-r

    search-res : ∃[ i ∈ FinT n ] (f' i == b) ⊎ ∀ i -> f' i != b
    search-res =
      finite-search-dec (FinSet-FinT n) (\i -> discB (f' i) b)

    module _ (f'-avoid : ∀ i -> f' i != b) where
      g : FinT n -> WithoutPoint B b
      g i = f' i , f'-avoid i

      sur-g : isSurjection g
      sur-g b2'@(b2 , b2!=b) = ∥-map sur-handle (sur-f b2)
        where
        sur-handle : Σ[ i ∈ FinT (suc n) ] (f i == b2) ->
                     Σ[ i ∈ FinT n ] (g i == b2')
        sur-handle (inj-l tt , p) = bot-elim (b2!=b (sym p))
        sur-handle (inj-r i , p) = i , WithoutPoint-path p

      rec-avoid : isFinSet (WithoutPoint B b)
      rec-avoid = FinT-sur-dec n g sur-g (Discrete-WithoutPoint discB b)

      avoid-case : isFinSet B
      avoid-case = incr-size b rec-avoid discB

    module _ (other-point : Σ[ i ∈ FinT n ] (f' i == b)) where
      sur-f' : isSurjection f'
      sur-f' b2 = ∥-map sur-handle (sur-f b2)
        where
        sur-handle : Σ[ i ∈ FinT (suc n) ] (f i == b2) ->
                     Σ[ i ∈ FinT n ] (f' i == b2)
        sur-handle (inj-l tt , p) =
          fst other-point , snd other-point >=> p
        sur-handle (inj-r i , p) = i , p

      point-case : isFinSet B
      point-case = FinT-sur-dec n f' sur-f' discB

  Fin-sur-dec : {ℓB : Level} {B : Type ℓB}
                (n : Nat) -> (f : Fin n -> B) -> isSurjection f -> Discrete B ->
                isFinSet B
  Fin-sur-dec {B = B} n =
    subst (\F -> (f : F -> B) -> isSurjection f -> Discrete B -> isFinSet B)
          (FinT=Fin n) (FinT-sur-dec n)


module _ {ℓA ℓB : Level} (FA : FinSet ℓA) {B : Type ℓB} (f : ⟨ FA ⟩ -> B)
         (sur-f : isSurjection f) (discB : Discrete B) where
  private
    A = fst FA
    module _ (ΣeqA : Σ[ n ∈ Nat ] (A ≃ Fin n)) where
      n = fst ΣeqA
      eqA = snd ΣeqA

      g : Fin n -> B
      g = f ∘ eqInv eqA

      sur-g : isSurjection g
      sur-g b = ∥-map convert (sur-f b)
        where
        convert : fiber f b -> fiber g b
        convert (a , p) = eqFun eqA a , cong f (eqRet eqA a) >=> p

      fsB : isFinSet B
      fsB = Fin-sur-dec n g sur-g discB

  FinitelyIndexed-Discrete->isFinSet : isFinSet B
  FinitelyIndexed-Discrete->isFinSet =
    unsquash isProp-isFinSet (∥-map fsB (snd FA))
