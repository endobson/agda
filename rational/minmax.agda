{-# OPTIONS --cubical --safe --exact-split #-}

module rational.minmax where

open import additive-group
open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-ring
open import ordered-semiring
open import rational
open import rational.order
open import relation
open import sign
open import sign.instances.rational

abstract
  r*₁-distrib-min : (x : ℚ⁰⁺) (y z : ℚ) ->
                    ⟨ x ⟩ r* (min y z) == min (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-distrib-min (x , nn-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> x r* (min y z) == min (x r* y) (x r* z)
    handle (inj-l y<z) =
      cong (x r*_) (min-≤-path y≤z) >=>
      sym (min-≤-path (*₁-preserves-≤ (NonNeg-0≤ x nn-x) y≤z))
      where
      module _ where
        y≤z = weaken-< y<z
    handle (inj-r z≤y) =
      cong (x r*_) (min-≥-path z≤y) >=>
      sym (min-≥-path (*₁-preserves-≤ (NonNeg-0≤ x nn-x) z≤y))


  r*₁-flip-distrib-min : (x : ℚ⁰⁻) (y z : ℚ) ->
                         ⟨ x ⟩ r* (min y z) == max (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-flip-distrib-min (x , np-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> x r* (min y z) == max (x r* y) (x r* z)
    handle (inj-l y<z) =
      cong (x r*_) (min-≤-path y≤z) >=>
      sym (max-≥-path (*₁-flips-≤ (NonPos-≤0 x np-x) y≤z))
      where
      module _ where
        y≤z = weaken-< y<z
    handle (inj-r z≤y) =
      cong (x r*_) (min-≥-path z≤y) >=>
      sym (max-≤-path (*₁-flips-≤ (NonPos-≤0 x np-x) z≤y))

  r*₁-distrib-max : (x : ℚ⁰⁺) (y z : ℚ) ->
                    ⟨ x ⟩ r* (max y z) == max (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-distrib-max (x , nn-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> x r* (max y z) == max (x r* y) (x r* z)
    handle (inj-l y<z) =
      cong (x r*_) (max-≤-path y≤z) >=>
      sym (max-≤-path (*₁-preserves-≤ (NonNeg-0≤ x nn-x) y≤z))
      where
      module _ where
        y≤z = weaken-< {d1 = y} y<z
    handle (inj-r z≤y) =
      cong (x r*_) (max-≥-path z≤y) >=>
      sym (max-≥-path (*₁-preserves-≤ (NonNeg-0≤ x nn-x) z≤y))


  r*₁-flip-distrib-max : (x : ℚ⁰⁻) (y z : ℚ) ->
                         ⟨ x ⟩ r* (max y z) == min (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-flip-distrib-max (x , np-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> x r* (max y z) == min (x r* y) (x r* z)
    handle (inj-l y<z) =
      cong (x r*_) (max-≤-path y≤z) >=>
      sym (min-≥-path (*₁-flips-≤ (NonPos-≤0 x np-x) y≤z))
      where
      module _ where
        y≤z = weaken-< {d1 = y} y<z
    handle (inj-r z≤y) =
      cong (x r*_) (max-≥-path z≤y) >=>
      sym (min-≤-path (*₁-flips-≤ (NonPos-≤0 x np-x) z≤y))

  minℚ-property : {ℓ : Level} {P : Pred ℚ ℓ} -> (q r : ℚ) -> P q -> P r -> P (min q r)
  minℚ-property {P = P} q r pq pr = handle split-min
    where
    handle : (min q r == q) ⊎ (min q r == r) -> P (min q r)
    handle (inj-l m=q) = subst P (sym m=q) pq
    handle (inj-r m=r) = subst P (sym m=r) pr


  maxℚ-property : {ℓ : Level} {P : Pred ℚ ℓ} -> (q r : ℚ) -> P q -> P r -> P (max q r)
  maxℚ-property {P = P} q r pq pr = handle split-max
    where
    handle : (max q r == q) ⊎ (max q r == r) -> P (max q r)
    handle (inj-l m=q) = subst P (sym m=q) pq
    handle (inj-r m=r) = subst P (sym m=r) pr


  maxℚ-r*₁-NonNeg : (a b c : ℚ) -> (NonNeg a) -> max (a r* b) (a r* c) == a r* (max b c)
  maxℚ-r*₁-NonNeg a b c nn-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> max (a r* b) (a r* c) == a r* (max b c)
    handle (inj-l b<c) =
      max-≤-path (*₁-preserves-≤ (NonNeg-0≤ a nn-a) (weaken-< b<c)) >=>
      cong (a r*_) (sym (max-≤-path (weaken-< b<c)))
    handle (inj-r c≤b) =
      max-≥-path (*₁-preserves-≤ (NonNeg-0≤ a nn-a) c≤b) >=>
      cong (a r*_) (sym (max-≥-path c≤b))

  maxℚ-r*₂-NonNeg : (a b c : ℚ) -> (NonNeg c) -> max (a r* c) (b r* c) == (max a b) r* c
  maxℚ-r*₂-NonNeg a b c nn-c =
    cong2 max (r*-commute a c) (r*-commute b c) >=>
    maxℚ-r*₁-NonNeg c a b nn-c >=>
    r*-commute c (max a b)

  maxℚ-r*₁-NonPos : (a b c : ℚ) -> (NonPos a) -> max (a r* b) (a r* c) == a r* (min b c)
  maxℚ-r*₁-NonPos a b c np-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> max (a r* b) (a r* c) == a r* (min b c)
    handle (inj-l b<c) =
      max-≥-path (*₁-flips-≤ (NonPos-≤0 a np-a) (weaken-< b<c)) >=>
      cong (a r*_) (sym (min-<-path b<c))
    handle (inj-r c≤b) =
      max-≤-path (*₁-flips-≤ (NonPos-≤0 a np-a) c≤b) >=>
      cong (a r*_) (sym (min-≥-path c≤b))

  minℚ-r*₁-NonNeg : (a b c : ℚ) -> (NonNeg a) -> min (a r* b) (a r* c) == a r* (min b c)
  minℚ-r*₁-NonNeg a b c nn-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> min (a r* b) (a r* c) == a r* (min b c)
    handle (inj-l b<c) =
      min-≤-path (*₁-preserves-≤ (NonNeg-0≤ a nn-a) (weaken-< b<c)) >=>
      cong (a r*_) (sym (min-<-path b<c))
    handle (inj-r c≤b) =
      min-≥-path (*₁-preserves-≤ (NonNeg-0≤ a nn-a) c≤b) >=>
      cong (a r*_) (sym (min-≥-path c≤b))

  minℚ-r*₂-NonNeg : (a b c : ℚ) -> (NonNeg c) -> min (a r* c) (b r* c) == (min a b) r* c
  minℚ-r*₂-NonNeg a b c nn-c =
    cong2 min (r*-commute a c) (r*-commute b c) >=>
    minℚ-r*₁-NonNeg c a b nn-c >=>
    r*-commute c (min a b)

  minℚ-r*₁-NonPos : (a b c : ℚ) -> (NonPos a) -> min (a r* b) (a r* c) == a r* (max b c)
  minℚ-r*₁-NonPos a b c np-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> min (a r* b) (a r* c) == a r* (max b c)
    handle (inj-l b<c) =
      min-≥-path (*₁-flips-≤ (NonPos-≤0 a np-a) (weaken-< b<c)) >=>
      cong (a r*_) (sym (max-<-path b<c))
    handle (inj-r c≤b) =
      min-≤-path (*₁-flips-≤ (NonPos-≤0 a np-a) c≤b) >=>
      cong (a r*_) (sym (max-≥-path c≤b))
