{-# OPTIONS --cubical --safe --exact-split #-}

module rational.minmax where

open import base
open import equality
open import hlevel
open import rational
open import rational.order
open import relation

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

minℚ-≤-left : (x y : ℚ) -> minℚ x y ℚ≤ x
minℚ-≤-left x y = handle (split-< x y)
  where
  handle : _ -> _
  handle (inj-l x<y) = subst (minℚ x y ℚ≤_) (minℚ-left x y (inj-l x<y)) (refl-ℚ≤ {minℚ x y})
  handle (inj-r y≤x) = subst (_ℚ≤ x) (sym (minℚ-right x y y≤x)) y≤x

minℚ-same : {x : ℚ} -> minℚ x x == x
minℚ-same {x} = minℚ-left _ _ (refl-ℚ≤ {x})

maxℚ-same : {x : ℚ} -> maxℚ x x == x
maxℚ-same {x} = maxℚ-left _ _ (refl-ℚ≤ {x})

split-minℚ : (x y : ℚ) -> (minℚ x y == x) ⊎ (minℚ x y == y)
split-minℚ x y = handle (split-< x y)
  where
  handle : (x < y) ⊎ (y ℚ≤ x) -> _
  handle (inj-l x<y) = inj-l (minℚ-left x y (inj-l x<y))
  handle (inj-r y≤x) = inj-r (minℚ-right x y y≤x)

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

minℚ-property : {ℓ : Level} {P : Pred ℚ ℓ} -> (q r : ℚ) -> P q -> P r -> P (minℚ q r)
minℚ-property {P = P} q r pq pr = handle (split-minℚ q r)
  where
  handle : _ -> _
  handle (inj-l m=q) = subst P (sym m=q) pq
  handle (inj-r m=r) = subst P (sym m=r) pr





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
