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


  minℚ₁-preserves-≤ : (a : ℚ) (b c : ℚ) -> (b ℚ≤ c) -> min a b ℚ≤ min a c
  minℚ₁-preserves-≤ a b c b≤c = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> min a b ℚ≤ min a c
    handle (inj-l a<b) =
      subst2 _ℚ≤_ (sym (min-<-path a<b))
                  (sym (min-<-path (trans-<-≤ a<b b≤c)))
             refl-≤
    handle (inj-r b≤a) =
      subst (_ℚ≤ (min a c)) (sym (min-≥-path b≤a)) (minℚ-property a c b≤a b≤c)


  maxℚ₁-preserves-≤ : (a : ℚ) (b c : ℚ) -> (b ℚ≤ c) -> max a b ℚ≤ max a c
  maxℚ₁-preserves-≤ a b c b≤c = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> max a b ℚ≤ max a c
    handle (inj-l a<b) =
      subst (_ℚ≤ (max a c)) (sym (max-<-path a<b))
                            (trans-ℚ≤ {b} {c} {max a c} b≤c max-≤-right)
    handle (inj-r b≤a) =
      subst (_ℚ≤ (max a c)) (sym (max-≥-path b≤a)) max-≤-left

  minℚ-preserves-< : (a b c d : ℚ) -> (a < b) -> (c < d) -> min a c < min b d
  minℚ-preserves-< a b c d a<b c<d = handle (split-< a c)
    where
    handle : (a < c ⊎ c ℚ≤ a) -> min a c < min b d
    handle (inj-l a<c) = subst (_< min b d) (sym (min-<-path a<c))
                               (minℚ-property b d a<b (trans-< {_} {_} {_} {a} {c} {d} a<c c<d))
    handle (inj-r c≤a) = subst (_< min b d) (sym (min-≥-path c≤a))
                               (minℚ-property b d (trans-≤-< {d1 = c} {a} {b} c≤a a<b) c<d)

  maxℚ-preserves-< : (a b c d : ℚ) -> (a < b) -> (c < d) -> max a c < max b d
  maxℚ-preserves-< a b c d a<b c<d = handle (split-< b d)
    where
    handle : (b < d ⊎ d ℚ≤ b) -> (max a c < max b d)
    handle (inj-l b<d) = subst (max a c <_) (sym (max-<-path b<d))
                               (maxℚ-property a c (trans-< a<b b<d) c<d)
    handle (inj-r d≤b) = subst (max a c <_) (sym (max-≥-path d≤b))
                               (maxℚ-property a c a<b (trans-<-≤ c<d d≤b))


  maxℚ-preserves-≤ : (a b c d : ℚ) -> (a ℚ≤ b) -> (c ℚ≤ d) -> max a c ℚ≤ max b d
  maxℚ-preserves-≤ a b c d a≤b c≤d = handle (split-< b d)
    where
    handle : (b < d ⊎ d ℚ≤ b) -> max a c ℚ≤ max b d
    handle (inj-l b<d) =
      subst (max a c ℚ≤_) (sym (max-<-path b<d))
            (maxℚ-property {P = _ℚ≤ d} a c (weaken-< {d1 = a} (trans-≤-< {d1 = a} {b} {d} a≤b b<d)) c≤d)
    handle (inj-r d≤b) =
      subst (max a c ℚ≤_) (sym (max-≥-path d≤b))
            (maxℚ-property {P = _ℚ≤ b} a c a≤b (trans-ℚ≤ {c} {d} {b} c≤d d≤b))


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

  r--maxℚ : (a b : ℚ) -> r- (max a b) == min (r- a) (r- b)
  r--maxℚ a b = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> r- (max a b) == min (r- a) (r- b)
    handle (inj-l a<b) =
      cong r-_ (max-<-path a<b) >=>
      sym (min->-path (minus-flips-< a<b))
    handle (inj-r b≤a) =
      cong r-_ (max-≥-path b≤a) >=>
      sym (min-≤-path (minus-flips-≤ b≤a))

  r--minℚ : (a b : ℚ) -> r- (min a b) == max (r- a) (r- b)
  r--minℚ a b = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> r- (min a b) == max (r- a) (r- b)
    handle (inj-l a<b) =
      cong r-_ (min-<-path a<b) >=>
      sym (max->-path (minus-flips-< a<b))
    handle (inj-r b≤a) =
      cong r-_ (min-≥-path b≤a) >=>
      sym (max-≤-path (minus-flips-≤ b≤a))


-- Absolute value

absℚ : ℚ -> ℚ
absℚ x = max x (r- x)

abs-diffℚ : ℚ -> ℚ -> ℚ
abs-diffℚ x y = absℚ (diff x y)

abstract
  maxℚ-weaken-<₁ : (x y z : ℚ) -> (max x y < z) -> x < z
  maxℚ-weaken-<₁ x y z lt = max₂-reflects-< (trans-<-≤ lt max-≤-left)

  absℚ-NonNeg : {q : ℚ} -> NonNeg q -> absℚ q == q
  absℚ-NonNeg {q} (inj-l pq) =
    max-≥-path (NonPos≤NonNeg (inj-l (r--flips-sign _ pos-sign pq)) (inj-l pq))
  absℚ-NonNeg {q} (inj-r zq) =
    max-≥-path (NonPos≤NonNeg (inj-r (r--flips-sign _ zero-sign zq)) (inj-r zq))

  absℚ-NonPos : {q : ℚ} -> NonPos q -> absℚ q == (r- q)
  absℚ-NonPos {q} (inj-l nq) =
    max-≤-path (NonPos≤NonNeg (inj-l nq) (inj-l (r--flips-sign _ neg-sign nq)))
  absℚ-NonPos {q} (inj-r zq) =
    max-≤-path (NonPos≤NonNeg (inj-r zq) (inj-r (r--flips-sign _ zero-sign zq)))

  absℚ-Zero : {q : ℚ} -> Zero (absℚ q) -> Zero q
  absℚ-Zero {q} zaq = handle (decide-sign q)
    where
    handle : Σ[ s ∈ Sign ] (isSign s q) -> Zero q
    handle (pos-sign  , pq) = subst Zero (absℚ-NonNeg (inj-l pq)) zaq
    handle (zero-sign , zq) = zq
    handle (neg-sign  , nq) =
      subst Zero (cong r-_ (absℚ-NonPos (inj-l nq)) >=>
                  minus-double-inverse) (r--flips-sign _ zero-sign zaq)

  NonNeg-absℚ : (q : ℚ) -> NonNeg (absℚ q)
  NonNeg-absℚ q = handle (decide-sign q)
    where
    handle : Σ[ s ∈ Sign ] (isSign s q) -> NonNeg (absℚ q)
    handle (pos-sign  , pq) = subst NonNeg (sym (absℚ-NonNeg (inj-l pq))) (inj-l pq)
    handle (zero-sign , zq) = subst NonNeg (sym (absℚ-NonNeg (inj-r zq))) (inj-r zq)
    handle (neg-sign  , nq) = subst NonNeg (sym (absℚ-NonPos (inj-l nq))) (r--NonPos (inj-l nq))

  absℚ-r*₁-NonNeg : (a b : ℚ) -> (NonNeg a) -> absℚ (a r* b) == a r* absℚ b
  absℚ-r*₁-NonNeg a b nn-a =
    cong (max (a r* b)) (sym (r*-minus-extract-right a b)) >=>
    maxℚ-r*₁-NonNeg a b (r- b) nn-a

  absℚ-r*₁-NonPos : (a b : ℚ) -> (NonPos a) -> absℚ (a r* b) == (r- a) r* absℚ b
  absℚ-r*₁-NonPos a b np-a =
    cong (max (a r* b)) (sym (r*-minus-extract-right a b)) >=>
    maxℚ-r*₁-NonPos a b (r- b) np-a >=>
    cong (\x -> (a r* (min x (r- b)))) (sym minus-double-inverse) >=>
    cong (a r*_) (sym (r--maxℚ (r- b) b) >=> cong r-_ max-commute) >=>
    r*-minus-extract-right a (absℚ b) >=>
    sym (r*-minus-extract-left a (absℚ b))

  absℚ-r* : (a b : ℚ) -> absℚ (a r* b) == absℚ a r* absℚ b
  absℚ-r* a b = handle (decide-sign a)
    where
    handle : Σ[ s ∈ Sign ] isSign s a -> absℚ (a r* b) == absℚ a r* absℚ b
    handle (pos-sign  , p-a) = absℚ-r*₁-NonNeg a b (inj-l p-a) >=>
                                 cong (_r* absℚ b) (sym (absℚ-NonNeg (inj-l p-a)))
    handle (zero-sign , z-a) = absℚ-r*₁-NonNeg a b (inj-r z-a) >=>
                                 cong (_r* absℚ b) (sym (absℚ-NonNeg (inj-r z-a)))
    handle (neg-sign  , n-a) = absℚ-r*₁-NonPos a b (inj-l n-a) >=>
                                 cong (_r* absℚ b) (sym (absℚ-NonPos (inj-l n-a)))
