{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.line where

open import additive-group
open import apartness
open import apartness.instances.rational
open import base
open import decision
open import discrete
open import equality-path
open import hlevel.base
open import hlevel.htype
open import hlevel.pi
open import order
open import order.instances.rational
open import order.minmax.instances.rational
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import rational
open import rational-geometry.direction
open import rational-geometry.point
open import rational-geometry.region
open import rational-geometry.translation
open import relation
open import ring
open import semidomain
open import semidomain.instances.rational
open import semiring
open import set-quotient
open import sigma.base

record Line' : Type ℓ-zero where
  constructor line'
  field
    p : Point
    dir : Direction


OnLine' : Point -> Line' -> Type ℓ-zero
OnLine' p (line' p₀ d) =
  Σ[ k ∈ ℚ ] (shift-point (scale-direction k d) p₀ == p)

direction#0 : ((direction dx dy _) : Direction) -> (dx # 0#) ⊎ (dy # 0#)
direction#0 (direction dx dy p) = handle (decide-= dx 0#) (decide-= dy 0#)
  where
  handle : Dec (dx == 0#) -> Dec (dy == 0#) -> (dx # 0#) ⊎ (dy # 0#)
  handle (no  x#0) _         = inj-l x#0
  handle (yes x=0) (no  y#0) = inj-r y#0
  handle (yes x=0) (yes y=0) = bot-elim (1r!=0r 1=0)
    -- TODO make this not rational specific
    where
    1=0 : 1# == 0#
    1=0 =
      sym p >=>
      +-cong (cong abs x=0 >=> abs-0≤-path refl-≤)
             (cong abs y=0 >=> abs-0≤-path refl-≤) >=>
      +-right-zero


isProp-OnLine' : ∀ p l -> isProp (OnLine' p l)
isProp-OnLine' p (line' (x , y) d@(direction dx dy _)) (k₁ , s₁) (k₂ , s₂) =
  ΣProp-path (isSet-Point _ _) (handle (direction#0 d))
  where
  path-x : k₁ * dx == k₂ * dx
  path-x = sym diff-step >=> sym +-assoc >=>
           (cong (_+ (- x)) (cong Point.x (s₁ >=> sym s₂))) >=>
           +-assoc >=> diff-step

  path-y : k₁ * dy == k₂ * dy
  path-y = sym diff-step >=> sym +-assoc >=>
           (cong (_+ (- y)) (cong Point.y (s₁ >=> sym s₂))) >=>
           +-assoc >=> diff-step


  handle : (dx # 0#) ⊎ (dy # 0#) -> k₁ == k₂
  handle (inj-l dx#0) = *₂-reflects-= dx#0 path-x
  handle (inj-r dy#0) = *₂-reflects-= dy#0 path-y



line'->region : Line' -> Region ℓ-zero
line'->region l = record { predicate = \p -> OnLine' p l , isProp-OnLine' p l }


SameLine : Rel Line' ℓ-zero
SameLine l₁@(line' p₁ d₁) l₂@(line' p₂ d₂) =
  (OnLine' p₁ l₂) × (OnLine' p₂ l₁) × (SameSemiDirection d₁ d₂)

sym-SameLine : Symmetric SameLine
sym-SameLine (o₁ , o₂ , p) = (o₂ , o₁ , sym-SameSemiDirection p)

Line : Type ℓ-zero
Line = Line' / SameLine

isSet-Line : isSet Line
isSet-Line = squash/

line->semi-direction : Line -> SemiDirection
line->semi-direction =
  SetQuotientElim.rec isSet-SemiDirection
    (\ (line' _ d) -> [ d ] )
    (\ (line' _ d₁) (line' _ d₂) (_ , _ , sd) -> eq/ d₁ d₂ sd)


isSet-Region : {ℓ : Level} -> isSet (Region ℓ)
isSet-Region r₁ r₂ p₁ p₂ i j =
  record { predicate =
    isSetΠ (\p -> isSet-hProp)
      (Region.predicate r₁) (Region.predicate r₂)
      (cong Region.predicate p₁) (cong Region.predicate p₂) i j }

line->region : Line -> Region ℓ-zero
line->region =
  SetQuotientElim.rec isSet-Region line'->region same-region
  where
  opaque
    same-region' : ∀ l₁ l₂ p -> SameLine l₁ l₂ ->
                   Region.contains (line'->region l₁) p ->
                   Region.contains (line'->region l₂) p
    same-region' (line' p₁ d₁) (line' p₂ d₂) p ((k₁ , q₁) , (k₂ , q₂) , inj-l dp) (k₃ , q₃) =
      (k₃ + k₁) ,
      cong2 _,_ (+-right *-distrib-+-right) (+-right *-distrib-+-right) >=>
      shift-point-+ >=>
      (\i -> shift-point (scale-direction k₃ (dp (~ i))) (q₁ i)) >=>
      q₃
    same-region' (line' p₁ d₁) (line' p₂ d₂) p ((k₁ , q₁) , (k₂ , q₂) , inj-r dp) (k₃ , q₃) =
      ((- k₃) + k₁) ,
      cong2 _,_ (+-right *-distrib-+-right) (+-right *-distrib-+-right) >=>
      shift-point-+ >=>
      (\i -> shift-point (scale-direction-minus {k₃} {d₂} i) (q₁ i)) >=>
      (\i -> shift-point (scale-direction k₃ (dp (~ i)))  p₁) >=>
      q₃

    same-region : ∀ l₁ l₂ -> SameLine l₁ l₂ -> line'->region l₁ == line'->region l₂
    same-region l₁ l₂ same-l = region-ext
      (\p -> same-region' l₁ l₂ p same-l ,
             same-region' l₂ l₁ p (sym-SameLine same-l))

OnLine : Point -> Line -> Type ℓ-zero
OnLine p l = Region.contains (line->region l) p

isProp-OnLine : (p : Point) (l : Line) -> isProp (OnLine p l)
isProp-OnLine p l = snd (Region.predicate (line->region l) p)
