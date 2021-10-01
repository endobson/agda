{-# OPTIONS --cubical --safe --exact-split #-}

module rational.minmax where

open import additive-group
open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import ordered-ring
open import ordered-semiring.instances.rational
open import rational
open import rational.difference
open import rational.order
open import relation
open import ring
open import ring.implementations.rational
open import sign
open import sign.instances.rational

private
  Triℚ< : Rel ℚ ℓ-zero
  Triℚ< x y = Tri (x < y) (x == y) (x > y)

  isProp-Triℚ< : (x y : ℚ) -> isProp (Triℚ< x y)
  isProp-Triℚ< x y = isProp-Tri (isProp-< x y) (isSetRational x y) (isProp-< y x)

  <->Tri : (x y : ℚ) -> x < y -> Triℚ< x y
  <->Tri x y x<y =
    tri< x<y
         (\x=y -> bot-elim (irrefl-< {_} {_} {_} {y} (subst (_< y) x=y x<y)))
         (\y<x -> bot-elim (asym-< {_} {_} {_} {x} {y} x<y y<x))

  >->Tri : (x y : ℚ) -> x > y -> Triℚ< x y
  >->Tri x y x>y =
    tri> (\x<y -> bot-elim (asym-< {_} {_} {_} {x} {y} x<y x>y))
         (\x=y -> bot-elim (irrefl-< {_} {_} {_} {y} (subst (y <_) x=y x>y)))
         x>y

  =->Tri : (x y : ℚ) -> x == y -> Triℚ< x y
  =->Tri x y x=y =
    tri= (\x<y -> bot-elim (irrefl-< {_} {_} {_} {y} (subst (_< y) x=y x<y)))
         x=y
         (\y<x -> bot-elim (irrefl-< {_} {_} {_} {y} (subst (y <_) x=y y<x)))


abstract
  private
    minℚ-helper : (x y : ℚ) -> Triℚ< x y -> ℚ
    minℚ-helper x y (tri< _ _ _) = x
    minℚ-helper x y (tri= _ _ _) = y
    minℚ-helper x y (tri> _ _ _) = y
  minℚ : ℚ -> ℚ -> ℚ
  minℚ x y = minℚ-helper x y (trichotomous-< x y)


abstract
  private
    maxℚ-helper : (x y : ℚ) -> Triℚ< x y -> ℚ
    maxℚ-helper x y (tri< _ _ _) = y
    maxℚ-helper x y (tri= _ _ _) = x
    maxℚ-helper x y (tri> _ _ _) = x
  maxℚ : ℚ -> ℚ -> ℚ
  maxℚ x y = maxℚ-helper x y (trichotomous-< x y)

abstract

  private
    minℚ-right-= : {x y : ℚ} -> y == x -> minℚ x y == y
    minℚ-right-= {x} {y} y=x =
      cong (minℚ-helper x y) (isProp-Triℚ< x y _ (=->Tri x y (sym y=x)))

    minℚ-left-= : {x y : ℚ} -> x == y -> minℚ x y == x
    minℚ-left-= x=y = minℚ-right-= (sym x=y) >=> sym x=y

    minℚ-right-< : {x y : ℚ} -> y < x -> minℚ x y == y
    minℚ-right-< {x} {y} y<x =
      cong (minℚ-helper x y) (isProp-Triℚ< x y _ (>->Tri x y y<x))

    minℚ-left-< : {x y : ℚ} -> x < y -> minℚ x y == x
    minℚ-left-< {x} {y} x<y =
      cong (minℚ-helper x y) (isProp-Triℚ< x y _ (<->Tri x y x<y))

  minℚ-left : (x y : ℚ) -> x ℚ≤ y -> minℚ x y == x
  minℚ-left = ℚ≤-elim (isSetRational _ _) minℚ-left-< minℚ-left-=

  minℚ-right : (x y : ℚ) -> y ℚ≤ x -> minℚ x y == y
  minℚ-right x y y≤x = ℚ≤-elim (isSetRational _ _) minℚ-right-< minℚ-right-= y x y≤x

  private
    maxℚ-left-= : {x y : ℚ} -> y == x -> maxℚ x y == x
    maxℚ-left-= {x} {y} y=x =
      cong (maxℚ-helper x y) (isProp-Triℚ< x y _ (=->Tri x y (sym y=x)))

    maxℚ-right-= : {x y : ℚ} -> x == y -> maxℚ x y == y
    maxℚ-right-= x=y = maxℚ-left-= (sym x=y) >=> x=y

    maxℚ-left-< : {x y : ℚ} -> y < x -> maxℚ x y == x
    maxℚ-left-< {x} {y} y<x =
      cong (maxℚ-helper x y) (isProp-Triℚ< x y _ (>->Tri x y y<x))

    maxℚ-right-< : {x y : ℚ} -> x < y -> maxℚ x y == y
    maxℚ-right-< {x} {y} x<y =
      cong (maxℚ-helper x y) (isProp-Triℚ< x y _ (<->Tri x y x<y))

  maxℚ-left : (x y : ℚ) -> y ℚ≤ x -> maxℚ x y == x
  maxℚ-left x y y≤x = ℚ≤-elim (isSetRational _ _) maxℚ-left-< maxℚ-left-= y x y≤x

  maxℚ-right : (x y : ℚ) -> x ℚ≤ y -> maxℚ x y == y
  maxℚ-right = ℚ≤-elim (isSetRational _ _) maxℚ-right-< maxℚ-right-=



  minℚ-same : {x : ℚ} -> minℚ x x == x
  minℚ-same {x} = minℚ-left _ _ refl-≤

  maxℚ-same : {x : ℚ} -> maxℚ x x == x
  maxℚ-same {x} = maxℚ-left _ _ refl-≤

  minℚ-commute : {x y : ℚ} -> minℚ x y == minℚ y x
  minℚ-commute {x} {y} = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) =
      (minℚ-left x y (weaken-< {d1 = x} x<y)) >=>
      sym (minℚ-right y x (weaken-< {d1 = x} x<y))
    handle (inj-r y≤x) = (minℚ-right x y y≤x) >=> sym (minℚ-left y x y≤x)

  maxℚ-commute : {x y : ℚ} -> maxℚ x y == maxℚ y x
  maxℚ-commute {x} {y} = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) = (maxℚ-right x y (weaken-< {d1 = x} x<y)) >=>
                         sym (maxℚ-left y x (weaken-< {d1 = x} x<y))
    handle (inj-r y≤x) = (maxℚ-left x y y≤x) >=> sym (maxℚ-right y x y≤x)


  minℚ-≤-left : (x y : ℚ) -> minℚ x y ℚ≤ x
  minℚ-≤-left x y = handle (split-< x y)
    where
    handle : (x < y ⊎ y ≤ x) -> _
    handle (inj-l x<y) = subst (minℚ x y ℚ≤_) (minℚ-left x y (weaken-< {d1 = x} x<y)) refl-≤
    handle (inj-r y≤x) = subst (_ℚ≤ x) (sym (minℚ-right x y y≤x)) y≤x

  minℚ-≤-right : (x y : ℚ) -> minℚ x y ℚ≤ y
  minℚ-≤-right x y = subst (_ℚ≤ y) (minℚ-commute {y} {x}) (minℚ-≤-left y x)

  maxℚ-≤-left : (x y : ℚ) -> x ℚ≤ maxℚ x y
  maxℚ-≤-left x y = handle (split-< y x)
    where
    handle : (y < x ⊎ x ≤ y) -> _
    handle (inj-l y<x) = subst (_ℚ≤ maxℚ x y) (maxℚ-left x y (weaken-< {d1 = y} y<x)) refl-≤
    handle (inj-r x≤y) = subst (x ℚ≤_) (sym (maxℚ-right x y x≤y)) x≤y

  maxℚ-≤-right : (x y : ℚ) -> y ℚ≤ maxℚ x y
  maxℚ-≤-right x y = subst (y ℚ≤_) (maxℚ-commute {y} {x}) (maxℚ-≤-left y x)

  split-minℚ : (x y : ℚ) -> (minℚ x y == x) ⊎ (minℚ x y == y)
  split-minℚ x y = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) = inj-l (minℚ-left x y (weaken-< {d1 = x} x<y))
    handle (inj-r y≤x) = inj-r (minℚ-right x y y≤x)

  split-maxℚ : (x y : ℚ) -> (maxℚ x y == x) ⊎ (maxℚ x y == y)
  split-maxℚ x y = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) = inj-r (maxℚ-right x y (weaken-< {d1 = x} x<y))
    handle (inj-r y≤x) = inj-l (maxℚ-left x y y≤x)

  r*₁-distrib-min : (x : ℚ⁰⁺) (y z : ℚ) ->
                    ⟨ x ⟩ r* (minℚ y z) == minℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-distrib-min (x , nn-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (minℚ-left y z y≤z) >=>
      sym (minℚ-left (x r* y) (x r* z) (*₁-preserves-≤ x y z (NonNeg-0≤ x nn-x) y≤z))
      where
      y≤z = weaken-< {d1 = y} y<z
    handle (inj-r z≤y) =
      cong (x r*_) (minℚ-right y z z≤y) >=>
      sym (minℚ-right (x r* y) (x r* z) (*₁-preserves-≤ x z y (NonNeg-0≤ x nn-x) z≤y))


  r*₁-flip-distrib-min : (x : ℚ⁰⁻) (y z : ℚ) ->
                         ⟨ x ⟩ r* (minℚ y z) == maxℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-flip-distrib-min (x , np-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (minℚ-left y z y≤z) >=>
      sym (maxℚ-left (x r* y) (x r* z) (*₁-flips-≤ x y z (NonPos-≤0 x np-x) y≤z))
      where
      y≤z = weaken-< {d1 = y} y<z
    handle (inj-r z≤y) =
      cong (x r*_) (minℚ-right y z z≤y) >=>
      sym (maxℚ-right (x r* y) (x r* z) (*₁-flips-≤ x z y (NonPos-≤0 x np-x) z≤y))

  r*₁-distrib-max : (x : ℚ⁰⁺) (y z : ℚ) ->
                    ⟨ x ⟩ r* (maxℚ y z) == maxℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-distrib-max (x , nn-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (maxℚ-right y z y≤z) >=>
      sym (maxℚ-right (x r* y) (x r* z) (*₁-preserves-≤ x y z (NonNeg-0≤ x nn-x) y≤z))
      where
      y≤z = weaken-< {d1 = y} y<z
    handle (inj-r z≤y) =
      cong (x r*_) (maxℚ-left y z z≤y) >=>
      sym (maxℚ-left (x r* y) (x r* z) (*₁-preserves-≤ x z y (NonNeg-0≤ x nn-x) z≤y))


  r*₁-flip-distrib-max : (x : ℚ⁰⁻) (y z : ℚ) ->
                         ⟨ x ⟩ r* (maxℚ y z) == minℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-flip-distrib-max (x , np-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (maxℚ-right y z y≤z) >=>
      sym (minℚ-right (x r* y) (x r* z) (*₁-flips-≤ x y z (NonPos-≤0 x np-x) y≤z))
      where
      y≤z = weaken-< {d1 = y} y<z
    handle (inj-r z≤y) =
      cong (x r*_) (maxℚ-left y z z≤y) >=>
      sym (minℚ-left (x r* y) (x r* z) (*₁-flips-≤ x z y (NonPos-≤0 x np-x) z≤y))

  minℚ-property : {ℓ : Level} {P : Pred ℚ ℓ} -> (q r : ℚ) -> P q -> P r -> P (minℚ q r)
  minℚ-property {P = P} q r pq pr = handle (split-minℚ q r)
    where
    handle : _ -> _
    handle (inj-l m=q) = subst P (sym m=q) pq
    handle (inj-r m=r) = subst P (sym m=r) pr


  maxℚ-property : {ℓ : Level} {P : Pred ℚ ℓ} -> (q r : ℚ) -> P q -> P r -> P (maxℚ q r)
  maxℚ-property {P = P} q r pq pr = handle (split-maxℚ q r)
    where
    handle : _ -> _
    handle (inj-l m=q) = subst P (sym m=q) pq
    handle (inj-r m=r) = subst P (sym m=r) pr


  minℚ₁-preserves-≤ : (a : ℚ) (b c : ℚ) -> (b ℚ≤ c) -> minℚ a b ℚ≤ minℚ a c
  minℚ₁-preserves-≤ a b c b≤c = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> _
    handle (inj-l a<b) =
      subst2 _ℚ≤_ (sym (minℚ-left a b (weaken-< {d1 = a} a<b)))
                  (sym (minℚ-left a c (weaken-< {d1 = a} (trans-<-≤ {d1 = a} {b} {c} a<b b≤c))))
             refl-≤
    handle (inj-r b≤a) =
      subst (_ℚ≤ (minℚ a c)) (sym (minℚ-right a b b≤a)) (minℚ-property a c b≤a b≤c)


  maxℚ₁-preserves-≤ : (a : ℚ) (b c : ℚ) -> (b ℚ≤ c) -> maxℚ a b ℚ≤ maxℚ a c
  maxℚ₁-preserves-≤ a b c b≤c = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> _
    handle (inj-l a<b) =
      subst (_ℚ≤ (maxℚ a c)) (sym (maxℚ-right a b (weaken-< {d1 = a} a<b)))
                             (trans-ℚ≤ {b} {c} {maxℚ a c} b≤c (maxℚ-≤-right a c))
    handle (inj-r b≤a) =
      subst (_ℚ≤ (maxℚ a c)) (sym (maxℚ-left a b b≤a)) (maxℚ-≤-left a c)

  minℚ-preserves-< : (a b c d : ℚ) -> (a < b) -> (c < d) -> minℚ a c < minℚ b d
  minℚ-preserves-< a b c d a<b c<d = handle (split-< a c)
    where
    handle : (a < c ⊎ c ℚ≤ a) -> _
    handle (inj-l a<c) = subst (_< minℚ b d) (sym (minℚ-left a c (weaken-< {d1 = a} a<c)))
                               (minℚ-property b d a<b (trans-< {_} {_} {_} {a} {c} {d} a<c c<d))
    handle (inj-r c≤a) = subst (_< minℚ b d) (sym (minℚ-right a c c≤a))
                               (minℚ-property b d (trans-≤-< {d1 = c} {a} {b} c≤a a<b) c<d)

  maxℚ-preserves-< : (a b c d : ℚ) -> (a < b) -> (c < d) -> maxℚ a c < maxℚ b d
  maxℚ-preserves-< a b c d a<b c<d = handle (split-< b d)
    where
    handle : (b < d ⊎ d ℚ≤ b) -> (maxℚ a c < maxℚ b d)
    handle (inj-l b<d) = subst (maxℚ a c <_) (sym (maxℚ-right b d (weaken-< b<d)))
                               (maxℚ-property a c (trans-< a<b b<d) c<d)
    handle (inj-r d≤b) = subst (maxℚ a c <_) (sym (maxℚ-left b d d≤b))
                               (maxℚ-property a c a<b (trans-<-≤ c<d d≤b))


  maxℚ-preserves-≤ : (a b c d : ℚ) -> (a ℚ≤ b) -> (c ℚ≤ d) -> maxℚ a c ℚ≤ maxℚ b d
  maxℚ-preserves-≤ a b c d a≤b c≤d = handle (split-< b d)
    where
    handle : (b < d ⊎ d ℚ≤ b) -> _
    handle (inj-l b<d) =
      subst (maxℚ a c ℚ≤_) (sym (maxℚ-right b d (weaken-< {d1 = b} b<d)))
            (maxℚ-property {P = _ℚ≤ d} a c (weaken-< {d1 = a} (trans-≤-< {d1 = a} {b} {d} a≤b b<d)) c≤d)
    handle (inj-r d≤b) =
      subst (maxℚ a c ℚ≤_) (sym (maxℚ-left b d d≤b))
            (maxℚ-property {P = _ℚ≤ b} a c a≤b (trans-ℚ≤ {c} {d} {b} c≤d d≤b))


  minℚ-assoc : (a b c : ℚ) -> minℚ (minℚ a b) c == minℚ a (minℚ b c)
  minℚ-assoc a b c = handle (split-< a b) (split-< a c)
    where
    handle : (a < b ⊎ b ℚ≤ a) -> (a < c ⊎ c ℚ≤ a) -> _
    handle (inj-l a<b) (inj-l a<c) =
      cong (\x -> minℚ x c) (minℚ-left a b (weaken-< {d1 = a} a<b)) >=>
      minℚ-left a c (weaken-< {d1 = a} a<c) >=>
      sym (minℚ-left a _ (weaken-< {d1 = a} (minℚ-property b c a<b a<c)))
    handle (inj-l a<b) (inj-r c≤a) =
      cong (\x -> minℚ x c) (minℚ-left a b (weaken-< {d1 = a} a<b)) >=>
      cong (minℚ a) (sym (minℚ-right b c c≤b))
      where
      c≤b = weaken-< {d1 = c} (trans-≤-< {d1 = c} {a} {b} c≤a a<b)
    handle (inj-r b≤a) (inj-l a<c) =
      cong (\x -> minℚ x c) (minℚ-right a b b≤a) >=>
      minℚ-left b c b≤c >=>
      sym (minℚ-right a b b≤a) >=>
      sym (cong (minℚ a) (minℚ-left b c b≤c))
      where
      b≤c = weaken-< {d1 = b} (trans-≤-< {d1 = b} {a} {c} b≤a a<c)
    handle (inj-r b≤a) (inj-r c≤a) =
      cong (\x -> minℚ x c) (minℚ-right a b b≤a) >=>
      sym (minℚ-right a (minℚ b c) (minℚ-property b c b≤a c≤a))


  maxℚ-assoc : (a b c : ℚ) -> maxℚ (maxℚ a b) c == maxℚ a (maxℚ b c)
  maxℚ-assoc a b c = handle (split-< a b) (split-< a c)
    where
    handle : (a < b ⊎ b ℚ≤ a) -> (a < c ⊎ c ℚ≤ a) -> _
    handle (inj-l a<b) (inj-l a<c) =
       cong (\x -> maxℚ x c) (maxℚ-right a b (weaken-< {d1 = a} a<b)) >=>
       sym (maxℚ-right a (maxℚ b c) (weaken-< {d1 = a} (maxℚ-property b c a<b a<c)))
    handle (inj-l a<b) (inj-r c≤a) =
      cong (\x -> maxℚ x c) (maxℚ-right a b (weaken-< {d1 = a} a<b)) >=>
      maxℚ-left b c c≤b >=>
      sym (maxℚ-right a b (weaken-< {d1 = a} a<b)) >=>
      sym (cong (maxℚ a) (maxℚ-left b c c≤b))
      where
      c≤b = weaken-< {d1 = c} (trans-≤-< {d1 = c} {a} {b} c≤a a<b)
    handle (inj-r b≤a) (inj-l a<c) =
      cong (\x -> maxℚ x c) (maxℚ-left a b b≤a) >=>
      cong (maxℚ a) (sym (maxℚ-right b c b≤c))
      where
      b≤c = weaken-< {d1 = b} (trans-≤-< {d1 = b} {a} {c} b≤a a<c)
    handle (inj-r b≤a) (inj-r c≤a) =
     cong (\x -> maxℚ x c) (maxℚ-left a b b≤a) >=>
     maxℚ-left a c c≤a >=>
     sym (maxℚ-left a _ (maxℚ-property b c b≤a c≤a))


  maxℚ-r*₁-NonNeg : (a b c : ℚ) -> (NonNeg a) -> maxℚ (a r* b) (a r* c) == a r* (maxℚ b c)
  maxℚ-r*₁-NonNeg a b c nn-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> maxℚ (a r* b) (a r* c) == a r* (maxℚ b c)
    handle (inj-l b<c) =
      maxℚ-right (a r* b) (a r* c) (*₁-preserves-≤ a b c (NonNeg-0≤ a nn-a) (weaken-< {d1 = b} b<c)) >=>
      cong (a r*_) (sym (maxℚ-right b c (weaken-< {d1 = b} b<c)))
    handle (inj-r c≤b) =
      maxℚ-left (a r* b) (a r* c) (*₁-preserves-≤ a c b (NonNeg-0≤ a nn-a) c≤b) >=>
      cong (a r*_) (sym (maxℚ-left b c c≤b))

  maxℚ-r*₂-NonNeg : (a b c : ℚ) -> (NonNeg c) -> maxℚ (a r* c) (b r* c) == (maxℚ a b) r* c
  maxℚ-r*₂-NonNeg a b c nn-c =
    cong2 maxℚ (r*-commute a c) (r*-commute b c) >=>
    maxℚ-r*₁-NonNeg c a b nn-c >=>
    r*-commute c (maxℚ a b)

  maxℚ-r*₁-NonPos : (a b c : ℚ) -> (NonPos a) -> maxℚ (a r* b) (a r* c) == a r* (minℚ b c)
  maxℚ-r*₁-NonPos a b c np-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> maxℚ (a r* b) (a r* c) == a r* (minℚ b c)
    handle (inj-l b<c) =
      maxℚ-left (a r* b) (a r* c) (*₁-flips-≤ a b c (NonPos-≤0 a np-a) (weaken-< {d1 = b} b<c)) >=>
      cong (a r*_) (sym (minℚ-left b c (weaken-< {d1 = b} b<c)))
    handle (inj-r c≤b) =
      maxℚ-right (a r* b) (a r* c) (*₁-flips-≤ a c b (NonPos-≤0 a np-a) c≤b) >=>
      cong (a r*_) (sym (minℚ-right b c c≤b))

  minℚ-r*₁-NonNeg : (a b c : ℚ) -> (NonNeg a) -> minℚ (a r* b) (a r* c) == a r* (minℚ b c)
  minℚ-r*₁-NonNeg a b c nn-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> minℚ (a r* b) (a r* c) == a r* (minℚ b c)
    handle (inj-l b<c) =
      minℚ-left (a r* b) (a r* c) (*₁-preserves-≤ a b c (NonNeg-0≤ a nn-a) (weaken-< {d1 = b} b<c)) >=>
      cong (a r*_) (sym (minℚ-left b c (weaken-< {d1 = b} b<c)))
    handle (inj-r c≤b) =
      minℚ-right (a r* b) (a r* c) (*₁-preserves-≤ a c b (NonNeg-0≤ a nn-a) c≤b) >=>
      cong (a r*_) (sym (minℚ-right b c c≤b))

  minℚ-r*₂-NonNeg : (a b c : ℚ) -> (NonNeg c) -> minℚ (a r* c) (b r* c) == (minℚ a b) r* c
  minℚ-r*₂-NonNeg a b c nn-c =
    cong2 minℚ (r*-commute a c) (r*-commute b c) >=>
    minℚ-r*₁-NonNeg c a b nn-c >=>
    r*-commute c (minℚ a b)

  minℚ-r*₁-NonPos : (a b c : ℚ) -> (NonPos a) -> minℚ (a r* b) (a r* c) == a r* (maxℚ b c)
  minℚ-r*₁-NonPos a b c np-a = handle (split-< b c)
    where
    handle : (b < c) ⊎ (c ℚ≤ b) -> minℚ (a r* b) (a r* c) == a r* (maxℚ b c)
    handle (inj-l b<c) =
      minℚ-right (a r* b) (a r* c) (*₁-flips-≤ a b c (NonPos-≤0 a np-a) (weaken-< {d1 = b} b<c)) >=>
      cong (a r*_) (sym (maxℚ-right b c (weaken-< {d1 = b} b<c)))
    handle (inj-r c≤b) =
      minℚ-left (a r* b) (a r* c) (*₁-flips-≤ a c b (NonPos-≤0 a np-a) c≤b) >=>
      cong (a r*_) (sym (maxℚ-left b c c≤b))

  r--maxℚ : (a b : ℚ) -> r- (maxℚ a b) == minℚ (r- a) (r- b)
  r--maxℚ a b = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> r- (maxℚ a b) == minℚ (r- a) (r- b)
    handle (inj-l a<b) =
      cong r-_ (maxℚ-right a b (weaken-< {d1 = a} a<b)) >=>
      sym (minℚ-right (r- a) (r- b) (minus-flips-≤ a b (weaken-< {d1 = a} a<b)))
    handle (inj-r b≤a) =
      cong r-_ (maxℚ-left a b b≤a) >=>
      sym (minℚ-left (r- a) (r- b) (minus-flips-≤ b a b≤a))

  r--minℚ : (a b : ℚ) -> r- (minℚ a b) == maxℚ (r- a) (r- b)
  r--minℚ a b = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> r- (minℚ a b) == maxℚ (r- a) (r- b)
    handle (inj-l a<b) =
      cong r-_ (minℚ-left a b (weaken-< {d1 = a} a<b)) >=>
      sym (maxℚ-left (r- a) (r- b) (minus-flips-≤ a b (weaken-< {d1 = a} a<b)))
    handle (inj-r b≤a) =
      cong r-_ (minℚ-right a b b≤a) >=>
      sym (maxℚ-right (r- a) (r- b) (minus-flips-≤ b a b≤a))


-- Absolute value

absℚ : ℚ -> ℚ
absℚ x = maxℚ x (r- x)

abs-diffℚ : ℚ -> ℚ -> ℚ
abs-diffℚ x y = absℚ (diffℚ x y)

abstract
  maxℚ-weaken-<₁ : (x y z : ℚ) -> (maxℚ x y < z) -> x < z
  maxℚ-weaken-<₁ x y z lt = handle (trichotomous-< x y) (maxℚ x y) refl lt
    where
    handle : (t : Tri (x < y) (x == y) (x > y)) -> (w : ℚ) -> (w == maxℚ-helper x y t) -> w < z
             -> x < z
    handle (tri< x<y  _ _) w p w<z = trans-< {_} {_} {_} {x} {y} {z} x<y (subst (_< z) p w<z)
    handle (tri= _ _ _) w p w<z = (subst (_< z) p w<z)
    handle (tri> _ _ _) w p w<z = (subst (_< z) p w<z)

  absℚ-NonNeg : {q : ℚ} -> NonNeg q -> absℚ q == q
  absℚ-NonNeg {q} (inj-l pq) =
    maxℚ-left q (r- q) (NonPos≤NonNeg (inj-l (r--flips-sign _ pos-sign pq)) (inj-l pq))
  absℚ-NonNeg {q} (inj-r zq) =
    maxℚ-left q (r- q) (NonPos≤NonNeg (inj-r (r--flips-sign _ zero-sign zq)) (inj-r zq))

  absℚ-NonPos : {q : ℚ} -> NonPos q -> absℚ q == (r- q)
  absℚ-NonPos {q} (inj-l nq) =
    maxℚ-right q (r- q) (NonPos≤NonNeg (inj-l nq) (inj-l (r--flips-sign _ neg-sign nq)))
  absℚ-NonPos {q} (inj-r zq) =
    maxℚ-right q (r- q) (NonPos≤NonNeg (inj-r zq) (inj-r (r--flips-sign _ zero-sign zq)))

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
    cong (maxℚ (a r* b)) (sym (r*-minus-extract-right a b)) >=>
    maxℚ-r*₁-NonNeg a b (r- b) nn-a

  absℚ-r*₁-NonPos : (a b : ℚ) -> (NonPos a) -> absℚ (a r* b) == (r- a) r* absℚ b
  absℚ-r*₁-NonPos a b np-a =
    cong (maxℚ (a r* b)) (sym (r*-minus-extract-right a b)) >=>
    maxℚ-r*₁-NonPos a b (r- b) np-a >=>
    cong (\x -> (a r* (minℚ x (r- b)))) (sym minus-double-inverse) >=>
    cong (a r*_) (sym (r--maxℚ (r- b) b) >=> cong r-_ maxℚ-commute) >=>
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
