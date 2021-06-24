{-# OPTIONS --cubical --safe --exact-split #-}

module rational.minmax where

open import base
open import equality
open import hlevel
open import rational
open import rational.order
open import relation
open import ring.implementations.rational
open import sign
open import sign.instances.rational

private
  Triℚ< : Rel ℚ ℓ-zero
  Triℚ< x y = Tri (x < y) (x == y) (x > y)

  isProp-Triℚ< : (x y : ℚ) -> isProp (Triℚ< x y)
  isProp-Triℚ< x y = isProp-Tri (isProp-< {x} {y})(isSetRational x y) (isProp-< {y} {x})

  <->Tri : (x y : ℚ) -> x < y -> Triℚ< x y
  <->Tri x y x<y =
    tri< x<y
         (\x=y -> bot-elim (irrefl-< {y} (subst (_< y) x=y x<y)))
         (\y<x -> bot-elim (asym-< {x} {y} x<y y<x))

  >->Tri : (x y : ℚ) -> x > y -> Triℚ< x y
  >->Tri x y x>y =
    tri> (\x<y -> bot-elim (asym-< {x} {y} x<y x>y))
         (\x=y -> bot-elim (irrefl-< {y} (subst (y <_) x=y x>y)))
         x>y

  =->Tri : (x y : ℚ) -> x == y -> Triℚ< x y
  =->Tri x y x=y =
    tri= (\x<y -> bot-elim (irrefl-< {y} (subst (_< y) x=y x<y)))
         x=y
         (\y<x -> bot-elim (irrefl-< {y} (subst (y <_) x=y y<x)))


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
  minℚ-left : (x y : ℚ) -> x ℚ≤ y -> minℚ x y == x
  minℚ-left x y (inj-l x<y) = cong (minℚ-helper x y) (isProp-Triℚ< x y _ (<->Tri x y x<y))
  minℚ-left x y (inj-r zd) =
    cong (minℚ-helper x y) (isProp-Triℚ< x y _ (=->Tri x y x=y)) >=> (sym x=y)
    where
    x=y : x == y
    x=y = sym (r+-right-zero x) >=> (cong (x r+_) (sym (Zero-path _ zd))) >=> diffℚ-step x y

  minℚ-right : (x y : ℚ) -> y ℚ≤ x -> minℚ x y == y
  minℚ-right x y (inj-l y<x) = cong (minℚ-helper x y) (isProp-Triℚ< x y _ (>->Tri x y y<x))
  minℚ-right x y (inj-r zd) = cong (minℚ-helper x y) (isProp-Triℚ< x y _ (=->Tri x y (sym y=x)))
    where
    y=x : y == x
    y=x = sym (r+-right-zero y) >=> (cong (y r+_) (sym (Zero-path _ zd))) >=> diffℚ-step y x

  maxℚ-left : (x y : ℚ) -> y ℚ≤ x -> maxℚ x y == x
  maxℚ-left x y (inj-l y<x) = cong (maxℚ-helper x y) (isProp-Triℚ< x y _ (>->Tri x y y<x))
  maxℚ-left x y (inj-r zd) = cong (maxℚ-helper x y) (isProp-Triℚ< x y _ (=->Tri x y (sym y=x)))
    where
    y=x : y == x
    y=x = sym (r+-right-zero y) >=> (cong (y r+_) (sym (Zero-path _ zd))) >=> diffℚ-step y x

  maxℚ-right : (x y : ℚ) -> x ℚ≤ y -> maxℚ x y == y
  maxℚ-right x y (inj-l x<y) = cong (maxℚ-helper x y) (isProp-Triℚ< x y _ (<->Tri x y x<y))
  maxℚ-right x y (inj-r zd) =
    cong (maxℚ-helper x y) (isProp-Triℚ< x y _ (=->Tri x y x=y)) >=> x=y
    where
    x=y : x == y
    x=y = sym (r+-right-zero x) >=> (cong (x r+_) (sym (Zero-path _ zd))) >=> diffℚ-step x y


  minℚ-same : {x : ℚ} -> minℚ x x == x
  minℚ-same {x} = minℚ-left _ _ (refl-ℚ≤ {x})

  maxℚ-same : {x : ℚ} -> maxℚ x x == x
  maxℚ-same {x} = maxℚ-left _ _ (refl-ℚ≤ {x})

  minℚ-commute : {x y : ℚ} -> minℚ x y == minℚ y x
  minℚ-commute {x} {y} = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) = (minℚ-left x y (inj-l x<y)) >=> sym (minℚ-right y x (inj-l x<y))
    handle (inj-r y≤x) = (minℚ-right x y y≤x) >=> sym (minℚ-left y x y≤x)

  maxℚ-commute : {x y : ℚ} -> maxℚ x y == maxℚ y x
  maxℚ-commute {x} {y} = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) = (maxℚ-right x y (inj-l x<y)) >=> sym (maxℚ-left y x (inj-l x<y))
    handle (inj-r y≤x) = (maxℚ-left x y y≤x) >=> sym (maxℚ-right y x y≤x)


  minℚ-≤-left : (x y : ℚ) -> minℚ x y ℚ≤ x
  minℚ-≤-left x y = handle (split-< x y)
    where
    handle : _ -> _
    handle (inj-l x<y) = subst (minℚ x y ℚ≤_) (minℚ-left x y (inj-l x<y)) (refl-ℚ≤ {minℚ x y})
    handle (inj-r y≤x) = subst (_ℚ≤ x) (sym (minℚ-right x y y≤x)) y≤x

  minℚ-≤-right : (x y : ℚ) -> minℚ x y ℚ≤ y
  minℚ-≤-right x y = subst (_ℚ≤ y) (minℚ-commute {y} {x}) (minℚ-≤-left y x)

  maxℚ-≤-left : (x y : ℚ) ->  x ℚ≤ maxℚ x y
  maxℚ-≤-left x y = handle (split-< y x)
    where
    handle : _ -> _
    handle (inj-l y<x) = subst (_ℚ≤ maxℚ x y) (maxℚ-left x y (inj-l y<x)) (refl-ℚ≤ {maxℚ x y})
    handle (inj-r x≤y) = subst (x ℚ≤_) (sym (maxℚ-right x y x≤y)) x≤y

  maxℚ-≤-right : (x y : ℚ) -> y ℚ≤ maxℚ x y
  maxℚ-≤-right x y = subst (y ℚ≤_) (maxℚ-commute {y} {x}) (maxℚ-≤-left y x)

  split-minℚ : (x y : ℚ) -> (minℚ x y == x) ⊎ (minℚ x y == y)
  split-minℚ x y = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) = inj-l (minℚ-left x y (inj-l x<y))
    handle (inj-r y≤x) = inj-r (minℚ-right x y y≤x)

  split-maxℚ : (x y : ℚ) -> (maxℚ x y == x) ⊎ (maxℚ x y == y)
  split-maxℚ x y = handle (split-< x y)
    where
    handle : (x < y) ⊎ (y ℚ≤ x) -> _
    handle (inj-l x<y) = inj-r (maxℚ-right x y (inj-l x<y))
    handle (inj-r y≤x) = inj-l (maxℚ-left x y y≤x)

  r*₁-distrib-min : (x : ℚ⁰⁺) (y z : ℚ) ->
                    ⟨ x ⟩ r* (minℚ y z) == minℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-distrib-min (x , nn-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (minℚ-left y z y≤z) >=>
      sym (minℚ-left (x r* y) (x r* z) (r*₁-preserves-≤ (x , nn-x) y z y≤z))
      where
      y≤z = inj-l y<z
    handle (inj-r z≤y) =
      cong (x r*_) (minℚ-right y z z≤y) >=>
      sym (minℚ-right (x r* y) (x r* z) (r*₁-preserves-≤ (x , nn-x) z y z≤y))


  r*₁-flip-distrib-min : (x : ℚ⁰⁻) (y z : ℚ) ->
                         ⟨ x ⟩ r* (minℚ y z) == maxℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-flip-distrib-min (x , np-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (minℚ-left y z y≤z) >=>
      sym (maxℚ-left (x r* y) (x r* z) (r*₁-flips-≤ (x , np-x) y z y≤z))
      where
      y≤z = inj-l y<z
    handle (inj-r z≤y) =
      cong (x r*_) (minℚ-right y z z≤y) >=>
      sym (maxℚ-right (x r* y) (x r* z) (r*₁-flips-≤ (x , np-x) z y z≤y))

  r*₁-distrib-max : (x : ℚ⁰⁺) (y z : ℚ) ->
                    ⟨ x ⟩ r* (maxℚ y z) == maxℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-distrib-max (x , nn-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (maxℚ-right y z y≤z) >=>
      sym (maxℚ-right (x r* y) (x r* z) (r*₁-preserves-≤ (x , nn-x) y z y≤z))
      where
      y≤z = inj-l y<z
    handle (inj-r z≤y) =
      cong (x r*_) (maxℚ-left y z z≤y) >=>
      sym (maxℚ-left (x r* y) (x r* z) (r*₁-preserves-≤ (x , nn-x) z y z≤y))


  r*₁-flip-distrib-max : (x : ℚ⁰⁻) (y z : ℚ) ->
                         ⟨ x ⟩ r* (maxℚ y z) == minℚ (⟨ x ⟩ r* y) (⟨ x ⟩ r* z)
  r*₁-flip-distrib-max (x , np-x) y z = handle (split-< y z)
    where
    handle : (y < z) ⊎ (z ℚ≤ y) -> _
    handle (inj-l y<z) =
      cong (x r*_) (maxℚ-right y z y≤z) >=>
      sym (minℚ-right (x r* y) (x r* z) (r*₁-flips-≤ (x , np-x) y z y≤z))
      where
      y≤z = inj-l y<z
    handle (inj-r z≤y) =
      cong (x r*_) (maxℚ-left y z z≤y) >=>
      sym (minℚ-left (x r* y) (x r* z) (r*₁-flips-≤ (x , np-x) z y z≤y))

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
    handle (inj-l a<b) = subst2 _ℚ≤_ (sym (minℚ-left a b (inj-l a<b)))
                                     (sym (minℚ-left a c (inj-l (trans-<-≤ {a} {b} {c} a<b b≤c))))
                                     (refl-ℚ≤ {a})
    handle (inj-r b≤a) =
      subst (_ℚ≤ (minℚ a c)) (sym (minℚ-right a b b≤a)) (minℚ-property a c b≤a b≤c)


  maxℚ₁-preserves-≤ : (a : ℚ) (b c : ℚ) -> (b ℚ≤ c) -> maxℚ a b ℚ≤ maxℚ a c
  maxℚ₁-preserves-≤ a b c b≤c = handle (split-< a b)
    where
    handle : (a < b) ⊎ (b ℚ≤ a) -> _
    handle (inj-l a<b) =
      subst (_ℚ≤ (maxℚ a c)) (sym (maxℚ-right a b (inj-l a<b)))
                             (trans-ℚ≤ {b} {c} {maxℚ a c} b≤c (maxℚ-≤-right a c))
    handle (inj-r b≤a) =
      subst (_ℚ≤ (maxℚ a c)) (sym (maxℚ-left a b b≤a)) (maxℚ-≤-left a c)

  minℚ-preserves-< : (a b c d : ℚ) -> (a < b) -> (c < d) -> minℚ a c < minℚ b d
  minℚ-preserves-< a b c d a<b c<d = handle (split-< a c)
    where
    handle : (a < c ⊎ c ℚ≤ a) -> _
    handle (inj-l a<c) = subst (_< minℚ b d) (sym (minℚ-left a c (inj-l a<c)))
                               (minℚ-property b d a<b (trans-< {a} {c} {d} a<c c<d))
    handle (inj-r c≤a) = subst (_< minℚ b d) (sym (minℚ-right a c c≤a))
                               (minℚ-property b d (trans-≤-< {c} {a} {b} c≤a a<b) c<d)

  maxℚ-preserves-< : (a b c d : ℚ) -> (a < b) -> (c < d) -> maxℚ a c < maxℚ b d
  maxℚ-preserves-< a b c d a<b c<d = handle (split-< b d)
    where
    handle : (b < d ⊎ d ℚ≤ b) -> _
    handle (inj-l b<d) = subst (maxℚ a c <_) (sym (maxℚ-right b d (inj-l b<d)))
                               (maxℚ-property a c (trans-< {a} {b} {d} a<b b<d) c<d)
    handle (inj-r d≤b) = subst (maxℚ a c <_) (sym (maxℚ-left b d d≤b))
                               (maxℚ-property a c a<b (trans-<-≤ {c} {d} {b} c<d d≤b))


  minℚ-assoc : (a b c : ℚ) -> minℚ (minℚ a b) c == minℚ a (minℚ b c)
  minℚ-assoc a b c = handle (split-< a b) (split-< a c)
    where
    handle : (a < b ⊎ b ℚ≤ a) -> (a < c ⊎ c ℚ≤ a) -> _
    handle (inj-l a<b) (inj-l a<c) =
      cong (\x -> minℚ x c) (minℚ-left a b (inj-l a<b)) >=>
      minℚ-left a c (inj-l a<c) >=>
      sym (minℚ-left a _ (inj-l (minℚ-property b c a<b a<c)))
    handle (inj-l a<b) (inj-r c≤a) =
      cong (\x -> minℚ x c) (minℚ-left a b (inj-l a<b)) >=>
      cong (minℚ a) (sym (minℚ-right b c c≤b))
      where
      c≤b = inj-l (trans-≤-< {c} {a} {b} c≤a a<b)
    handle (inj-r b≤a) (inj-l a<c) =
      cong (\x -> minℚ x c) (minℚ-right a b b≤a) >=>
      minℚ-left b c b≤c >=>
      sym (minℚ-right a b b≤a) >=>
      sym (cong (minℚ a) (minℚ-left b c b≤c))
      where
      b≤c = inj-l (trans-≤-< {b} {a} {c} b≤a a<c)
    handle (inj-r b≤a) (inj-r c≤a) =
      cong (\x -> minℚ x c) (minℚ-right a b b≤a) >=>
      sym (minℚ-right a (minℚ b c) (minℚ-property b c b≤a c≤a))


  maxℚ-assoc : (a b c : ℚ) -> maxℚ (maxℚ a b) c == maxℚ a (maxℚ b c)
  maxℚ-assoc a b c = handle (split-< a b) (split-< a c)
    where
    handle : (a < b ⊎ b ℚ≤ a) -> (a < c ⊎ c ℚ≤ a) -> _
    handle (inj-l a<b) (inj-l a<c) =
       cong (\x -> maxℚ x c) (maxℚ-right a b (inj-l a<b)) >=>
       sym (maxℚ-right a (maxℚ b c) (inj-l (maxℚ-property b c a<b a<c)))
    handle (inj-l a<b) (inj-r c≤a) =
      cong (\x -> maxℚ x c) (maxℚ-right a b (inj-l a<b)) >=>
      maxℚ-left b c c≤b >=>
      sym (maxℚ-right a b (inj-l a<b)) >=>
      sym (cong (maxℚ a) (maxℚ-left b c c≤b))
      where
      c≤b = inj-l (trans-≤-< {c} {a} {b} c≤a a<b)
    handle (inj-r b≤a) (inj-l a<c) =
      cong (\x -> maxℚ x c) (maxℚ-left a b b≤a) >=>
      cong (maxℚ a) (sym (maxℚ-right b c b≤c))
      where
      b≤c = inj-l (trans-≤-< {b} {a} {c} b≤a a<c)
    handle (inj-r b≤a) (inj-r c≤a) =
     cong (\x -> maxℚ x c) (maxℚ-left a b b≤a) >=>
     maxℚ-left a c c≤a >=>
     sym (maxℚ-left a _ (maxℚ-property b c b≤a c≤a))



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
    handle (tri< x<y  _ _) w p w<z = trans-< {x} {y} {z} x<y (subst (_< z) p w<z)
    handle (tri= _ _ _) w p w<z = (subst (_< z) p w<z)
    handle (tri> _ _ _) w p w<z = (subst (_< z) p w<z)

absℚ-NonNeg : {q : ℚ} -> NonNeg q -> absℚ q == q
absℚ-NonNeg {q} (inj-l pq) = maxℚ-left q (r- q) (NonPos≤NonNeg (inj-l (r--flips-sign _ _ pq)) (inj-l pq))
absℚ-NonNeg {q} (inj-r zq) = maxℚ-left q (r- q) (NonPos≤NonNeg (inj-r (r--flips-sign _ _ zq)) (inj-r zq))

absℚ-NonPos : {q : ℚ} -> NonPos q -> absℚ q == (r- q)
absℚ-NonPos {q} (inj-l nq) =
  maxℚ-right q (r- q) (NonPos≤NonNeg (inj-l nq) (inj-l (r--flips-sign _ _ nq)))
absℚ-NonPos {q} (inj-r zq) =
  maxℚ-right q (r- q) (NonPos≤NonNeg (inj-r zq) (inj-r (r--flips-sign _ _ zq)))

absℚ-Zero : {q : ℚ} -> Zero (absℚ q) -> Zero q
absℚ-Zero {q} zaq = handle (isSign-self q)
  where
  handle : {s : Sign} -> (isSign s q) -> Zero q
  handle {pos-sign} pq = subst Zero (absℚ-NonNeg (inj-l pq)) zaq
  handle {zero-sign} zq = zq
  handle {neg-sign} nq =
    subst Zero (cong r-_ (absℚ-NonPos (inj-l nq)) >=>
                RationalRing.minus-double-inverse) (r--flips-sign _ _ zaq)

NonNeg-absℚ : (q : ℚ) -> NonNeg (absℚ q)
NonNeg-absℚ q = handle _ (isSign-self q)
  where
  handle : (s : Sign) -> isSign s q -> NonNeg (absℚ q)
  handle pos-sign pq = subst NonNeg (sym (absℚ-NonNeg (inj-l pq))) (inj-l pq)
  handle zero-sign zq = subst NonNeg (sym (absℚ-NonNeg (inj-r zq))) (inj-r zq)
  handle neg-sign nq = subst NonNeg (sym (absℚ-NonPos (inj-l nq))) (r--NonPos (inj-l nq))
