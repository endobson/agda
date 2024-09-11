{-# OPTIONS --cubical --safe --exact-split #-}

module finsum.order where

open import additive-group
open import base
open import commutative-monoid
open import commutative-monoid.binary-product
open import commutative-monoid.subtype
open import equality
open import equivalence
open import fin
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finsum
open import functions
open import nat
open import order
open import ordered-additive-group
open import relation
open import truncation

module _ {ℓD ℓ≤ : Level} {D : Type ℓD} {D≤ : Rel D ℓ≤}
         {ACM : AdditiveCommMonoid D} {O : isPartialOrder D≤}
         {{POA : PartiallyOrderedAdditiveStr ACM O}} where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      IACM = ACM
      IO = O

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    finiteSum-preserves-0≤ : {f : I -> D} ->
                             (lt : (i : I) -> 0# ≤ f i) ->
                             0# ≤ finiteSum f
    finiteSum-preserves-0≤ {f} lt =
      trans-≤-= (snd (finiteMerge CM-D⁺ f'))
                (sym (finiteMerge-homo-inject CommMonoidʰ-fst))
      where
      D⁺ : Type (ℓ-max ℓD ℓ≤)
      D⁺ = Σ D (0# ≤_)
      f' : (i : I) -> D⁺
      f' i = f i , lt i

      CM-D⁺ : CommMonoid D⁺
      CM-D⁺ = SubCommMonoidStr (\_ -> isProp-≤) CM refl-≤ +-preserves-0≤

    finiteSum-preserves-≤ : {f g : I -> D} ->
                            (lt : (i : I) -> f i ≤ g i) ->
                            finiteSum f ≤ finiteSum g
    finiteSum-preserves-≤ {f} {g} lt =
      subst2 _≤_ (sym (finiteMerge-homo-inject (CommMonoidʰ-proj₁ CM CM) >=> cong proj₁ path))
                 (sym (finiteMerge-homo-inject (CommMonoidʰ-proj₂ CM CM) >=> cong proj₂ path))
                 (snd (finiteMerge CM-2D⁺ fg))
      where
      2D : Type ℓD
      2D = D × D
      2D⁺ : Type (ℓ-max ℓD ℓ≤)
      2D⁺ = Σ[ d ∈ 2D ] (proj₁ d ≤ proj₂ d)

      fg : I -> 2D⁺
      fg i = (f i , g i) , lt i

      CM-2D : CommMonoid 2D
      CM-2D = CommMonoidStr-× CM CM

      CM-2D⁺ : CommMonoid 2D⁺
      CM-2D⁺ = SubCommMonoidStr (\_ -> isProp-≤) CM-2D refl-≤ +-preserves-≤

      path : finiteMerge CM-2D (\i -> f i , g i) ==
             fst (finiteMerge CM-2D⁺ fg)
      path = (finiteMerge-homo-inject CommMonoidʰ-fst)

module _ {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<}
         {ACM : AdditiveCommMonoid D} {LO : isLinearOrder D<}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}} where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      IACM = ACM
      ILO = LO

  private
    finsum-reflects-< : (n : ℕ) (f g : Fin n -> D) -> finMergeDep CM n f < finMergeDep CM n g ->
                        ∃[ i ∈ (Fin n) ] (f i < g i)
    finsum-reflects-< zero f g fs<gs = bot-elim (irrefl-< fs<gs)
    finsum-reflects-< (suc n) f g fs<gs = ∥-bind handle (+-reflects-< fs<gs)
      where

      handle : (f zero-fin < g zero-fin) ⊎
               (finMergeDep CM n (f ∘ suc-fin) < finMergeDep CM n (g ∘ suc-fin)) ->
               ∃[ i ∈ (Fin (suc n)) ] (f i < g i)
      handle (inj-l fz<gz) = ∣ zero-fin , fz<gz ∣
      handle (inj-r fs<gs) =
        ∥-map (\(i , lt) -> suc-fin i , lt)
              (finsum-reflects-< n (f ∘ suc-fin) (g ∘ suc-fin) fs<gs)

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    opaque
      finiteSum-reflects-< : {f g : I -> D} ->
                             finiteSum f < finiteSum g ->
                             ∃[ i ∈ I ] (f i < g i)
      finiteSum-reflects-< {f} {g} fs<gs = ∥-bind handle isFinSetⁱ
        where
        handle : Σ[ n ∈ ℕ ] (I ≃ Fin n) -> ∃[ i ∈ I ] (f i < g i)
        handle (n , eq) =
          ∥-map (\(i , lt) -> eqInv eq i , lt)
                (finsum-reflects-< n (f ∘ eqInv eq) (g ∘ eqInv eq) lt)
          where
          lt : equivMerge CM eq f < equivMerge CM eq g
          lt = subst2 _<_ (finiteMerge-eval CM eq f) (finiteMerge-eval CM eq g) fs<gs
