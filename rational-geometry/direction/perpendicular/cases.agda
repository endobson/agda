{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.direction.perpendicular.cases where

open import base
open import equivalence
open import apartness
open import apartness.instances.rational
open import additive-group
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.rational
open import order.minmax.instances.rational
open import order.instances.rational
open import semiring
open import ordered-semiring
open import ordered-ring.absolute-value
open import ordered-ring
open import ordered-semiring.instances.rational
open import order
open import ring
open import relation
open import sum
open import equality-path
open import rational
open import rational.order
open import rational-geometry.direction
open import rational-geometry.direction.perpendicular


private
  cases-isPerpendicular-x=0×y=1 : ∀ d₁ d₂ ->
    (Direction.dx d₁ == 0#) ->
    (Direction.dy d₁ == 1#) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-x=0×y=1
    d₁@(direction x₁ y₁ a₁) d₂@(direction x₂ y₂ a₂) x₁=0 y₁=1 (is-perpendicular-direction p) =
    ⊎-map caseˡ caseʳ (⊎-swap x-cases)
    where
    y₂=0 : y₂ == 0#
    y₂=0 = sym *-left-one >=> *-left (sym y₁=1) >=>
           sym +-left-zero >=> +-left (sym *-left-zero >=> *-left (sym x₁=0)) >=>
           p

    ax₂=1 : abs x₂ == 1#
    ax₂=1 = sym +-right-zero >=>
            (+-right (sym (abs-0≤-path (path-≤ (sym y₂=0)) >=> y₂=0))) >=>
            a₂

    x-cases : (x₂ == 1#) ⊎ (x₂ == (- 1#))
    x-cases = abs-cases x₂ 1# (inj-r 0<1) ax₂=1

    caseˡ : (x₂ == (- 1#)) -> (d₂ == perpendicularˡ d₁)
    caseˡ xp = direction-coord-path (xp >=> cong -_ (sym y₁=1)) (y₂=0 >=> sym x₁=0)

    caseʳ : (x₂ == 1#) -> (d₂ == perpendicularʳ d₁)
    caseʳ xp = direction-coord-path (xp >=> (sym y₁=1)) (y₂=0 >=> sym minus-zero >=> cong -_ (sym x₁=0))


  cases-isPerpendicular-x=0×y=-1 : ∀ d₁ d₂ ->
    (Direction.dx d₁ == 0#) ->
    (Direction.dy d₁ == (- 1#)) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-x=0×y=-1 d₁ d₂ xp yp perp = ⊎-map caseˡ caseʳ (⊎-swap rec)
    where
    d₁' : Direction
    d₁' = reverse-direction d₁

    perp' : isPerpendicularDirection d₁' d₂
    perp' = sym-isPerpendicular
      (reverse-direction-preserves-isPerpendicular
        (sym-isPerpendicular perp))

    rec : (d₂ == perpendicularˡ d₁') ⊎ (d₂ == perpendicularʳ d₁')
    rec = cases-isPerpendicular-x=0×y=1 d₁' d₂
            (cong -_ xp >=> minus-zero)
            (cong -_ yp >=> minus-double-inverse)
            perp'

    caseˡ : d₂ == perpendicularʳ d₁' -> d₂ == perpendicularˡ d₁
    caseˡ p =
      p >=>
      cong perpendicularʳ (sym (perpendicularˡˡ d₁)) >=>
      perpendicularʳˡ _

    caseʳ : d₂ == perpendicularˡ d₁' -> d₂ == perpendicularʳ d₁
    caseʳ p =
      p >=>
      cong perpendicularˡ (sym (perpendicularʳʳ d₁)) >=>
      perpendicularˡʳ _


  cases-isPerpendicular-x=0 : ∀ d₁ d₂ ->
    (Direction.dx d₁ == 0#) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-x=0 d₁@(direction x₁ y₁ a₁) d₂ xp perp =
    either
      (\yp -> cases-isPerpendicular-x=0×y=1 d₁ d₂ xp yp perp)
      (\yp -> cases-isPerpendicular-x=0×y=-1 d₁ d₂ xp yp perp)
      (abs-cases y₁ 1# (inj-r 0<1) ay₁=1)
    where
    ay₁=1 : abs y₁ == 1#
    ay₁=1 = sym +-left-zero >=> +-left (sym (abs-0≤-path (path-≤ (sym xp)) >=> xp)) >=> a₁


  cases-isPerpendicular-y=0 : ∀ d₁ d₂ ->
    (Direction.dy d₁ == 0#) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-y=0 d₁ d₂ yp perp = ⊎-map caseˡ caseʳ rec
    where
    d₁' : Direction
    d₁' = perpendicularʳ d₁
    d₂' : Direction
    d₂' = perpendicularʳ d₂
    perp' : isPerpendicularDirection d₁' d₂'
    perp' = perpendicularʳ-preserves-isPerpendicular perp

    rec : (d₂' == perpendicularˡ d₁') ⊎ (d₂' == perpendicularʳ d₁')
    rec = cases-isPerpendicular-x=0 d₁' d₂' yp perp'

    caseˡ : (d₂' == perpendicularˡ d₁') -> (d₂ == perpendicularˡ d₁)
    caseˡ p =
      sym (perpendicularˡʳ _) >=>
      cong perpendicularˡ (p >=> perpendicularˡʳ _)

    caseʳ : (d₂' == perpendicularʳ d₁') -> (d₂ == perpendicularʳ d₁)
    caseʳ p =
      sym (perpendicularˡʳ _) >=>
      cong perpendicularˡ p >=>
      (perpendicularˡʳ _)



  cases-isPerpendicular-0<x×0<y : ∀ d₁ d₂ ->
    (0# < Direction.dx d₁) ->
    (0# < Direction.dy d₁) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-0<x×0<y
    d₁@(direction x₁ y₁ a₁) d₂@(direction x₂ y₂ a₂) 0<x₁ 0<y₁ (is-perpendicular-direction perp) =
    handle (trichotomous-< x₂ 0#)
    where
    y₁#0 : y₁ # 0#
    y₁#0 p = irrefl-path-< (sym p) 0<y₁
    1/y₁ : ℚ
    1/y₁ = r1/ y₁ y₁#0

    x₁y₁-path : x₁ + y₁ == 1#
    x₁y₁-path = +-cong (sym (abs-0≤-path (weaken-< 0<x₁))) (sym (abs-0≤-path (weaken-< 0<y₁))) >=> a₁

    yy-path : y₁ * y₂ == (- (x₁ * x₂))
    yy-path = sym diff-step >=> sym +-assoc >=> cong (_+ (- (x₁ * x₂))) perp >=> +-left-zero


    case-0<x₂ : (0# < x₂) -> d₂ == perpendicularʳ d₁
    case-0<x₂ 0<x₂ = direction-coord-path x₂-path y₂-path
      where
      y₂<0 : y₂ < 0#
      y₂<0 = *₁-reflects-<0 (asym-< 0<y₁)
               (trans-=-< yy-path (minus-flips-0< (*-preserves-0< 0<x₁ 0<x₂)))

      x₂=1+y₂ : x₂ == 1# + y₂
      x₂=1+y₂ =
        sym diff-step >=>
        +-commute >=>
        +-left (+-cong (sym (abs-0≤-path (weaken-< 0<x₂)))
                       (sym (abs-≤0-path (weaken-< y₂<0)))) >=>
        cong (_+ y₂) a₂

      y₂-path : y₂ == - x₁
      y₂-path =
        sym +-right-zero >=>
        +-right (sym minus-zero >=> cong -_ step₂ >=> minus-distrib-plus) >=>
        diff-step
        where
        step₁ : (x₁ * x₂) == x₁ + (x₁ * y₂)
        step₁ = *-right x₂=1+y₂ >=> *-distrib-+-left >=> +-left *-right-one

        step₂ : 0# == x₁ + y₂
        step₂ =
          sym perp >=>
          +-left step₁ >=>
          +-assoc >=>
          +-right (sym *-distrib-+-right >=>
                   *-left x₁y₁-path >=>
                   *-left-one)

      x₂-path : x₂ == y₁
      x₂-path = x₂=1+y₂ >=> +-cong (sym x₁y₁-path) y₂-path >=> +-assoc >=> diff-step

    case-x₂<0 : (x₂ < 0#) -> d₂ == perpendicularˡ d₁
    case-x₂<0 x₂<0 = direction-coord-path x₂-path y₂-path
      where
      0<y₂ : 0# < y₂
      0<y₂ = *₁-reflects-0< (asym-< 0<y₁)
               (trans-<-= (minus-flips-<0 (*₁-preserves-<0 0<x₁ x₂<0)) (sym yy-path))

      y₂=1+x₂ : y₂ == 1# + x₂
      y₂=1+x₂ =
        sym diff-step >=>
        +-commute >=>
        +-left (+-cong (sym (abs-0≤-path (weaken-< 0<y₂)))
                       (sym (abs-≤0-path (weaken-< x₂<0))) >=>
                +-commute) >=>
        cong (_+ x₂) a₂


      x₂-path : x₂ == - y₁
      x₂-path =
        sym +-right-zero >=>
        +-right (sym minus-zero >=> cong -_ step₂ >=> minus-distrib-plus) >=>
        diff-step
        where
        step₁ : (y₁ * y₂) == y₁ + (y₁ * x₂)
        step₁ = *-right y₂=1+x₂ >=> *-distrib-+-left >=> +-left *-right-one

        step₂ : 0# == y₁ + x₂
        step₂ =
          sym perp >=>
          +-right step₁ >=>
          +-commute >=>
          +-assoc >=>
          +-right (sym *-distrib-+-right >=>
                   *-left (+-commute >=> x₁y₁-path) >=>
                   *-left-one)

      y₂-path : y₂ == x₁
      y₂-path = y₂=1+x₂ >=> +-cong (sym x₁y₁-path >=> +-commute) x₂-path >=> +-assoc >=> diff-step



    case-x₂=0 : x₂ != 0#
    case-x₂=0 x₂=0 = irrefl-path-< (sym ay₁=0) 0<ay₁
      where
      0<ay₁ : 0# < abs y₁
      0<ay₁ = eqFun abs-#0-eq (inj-r 0<y₁)

      ay₂=1 : abs y₂ == 1#
      ay₂=1 = sym +-left-zero >=> +-left (sym (abs-0≤-path refl-≤) >=> cong abs (sym x₂=0)) >=> a₂

      ay₁=0 : abs y₁ == 0#
      ay₁=0 =
        sym *-right-one >=> *-right (sym ay₂=1) >=> sym abs-distrib-* >=>
        cong abs yy-path >=>
        abs-minus >=>
        cong abs (*-right x₂=0 >=> *-right-zero) >=>
        abs-0≤-path refl-≤

    handle : Tri< x₂ 0# -> (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
    handle (tri< x₂<0 _ _) = inj-l (case-x₂<0 x₂<0)
    handle (tri= _ x₂=0 _) = bot-elim (case-x₂=0 x₂=0)
    handle (tri> _ _ 0<x₂) = inj-r (case-0<x₂ 0<x₂)



  cases-isPerpendicular-0<x×y<0 : ∀ d₁ d₂ ->
    (0# < Direction.dx d₁) ->
    (Direction.dy d₁ < 0#) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-0<x×y<0 d₁ d₂ 0<x y<0 perp = ⊎-map caseˡ caseʳ rec
    where
    d₁' : Direction
    d₁' = perpendicularˡ d₁
    d₂' : Direction
    d₂' = perpendicularˡ d₂
    perp' : isPerpendicularDirection d₁' d₂'
    perp' = perpendicularˡ-preserves-isPerpendicular perp

    rec : (d₂' == perpendicularˡ d₁') ⊎ (d₂' == perpendicularʳ d₁')
    rec = cases-isPerpendicular-0<x×0<y d₁' d₂' (minus-flips-<0 y<0) 0<x perp'

    caseˡ : (d₂' == perpendicularˡ d₁') -> (d₂ == perpendicularˡ d₁)
    caseˡ p =
      sym (perpendicularʳˡ _) >=>
      cong perpendicularʳ p >=>
      (perpendicularʳˡ _)

    caseʳ : (d₂' == perpendicularʳ d₁') -> (d₂ == perpendicularʳ d₁)
    caseʳ p =
      sym (perpendicularʳˡ _) >=>
      cong perpendicularʳ (p >=> perpendicularʳˡ _)

  cases-isPerpendicular-0<x : ∀ d₁ d₂ ->
    (0# < Direction.dx d₁) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-0<x d₁@(direction _ y _) d₂ 0<x perp = handle (trichotomous-< y 0#)
    where
    handle : Tri< y 0# -> (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
    handle (tri< y<0 _ _) = cases-isPerpendicular-0<x×y<0 d₁ d₂ 0<x y<0 perp
    handle (tri= _ y=0 _) = cases-isPerpendicular-y=0 d₁ d₂ y=0 perp
    handle (tri> _ _ 0<y) = cases-isPerpendicular-0<x×0<y d₁ d₂ 0<x 0<y perp

  cases-isPerpendicular-x<0 : ∀ d₁ d₂ ->
    (Direction.dx d₁ < 0#) ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicular-x<0 d₁@(direction _ y _) d₂ x<0 perp =
    ⊎-map caseˡ caseʳ (⊎-swap rec)
    where
    d₁' : Direction
    d₁' = reverse-direction d₁
    perp' : isPerpendicularDirection d₁' d₂
    perp' = sym-isPerpendicular
      (reverse-direction-preserves-isPerpendicular
        (sym-isPerpendicular perp))

    rec : (d₂ == perpendicularˡ d₁') ⊎ (d₂ == perpendicularʳ d₁')
    rec = cases-isPerpendicular-0<x d₁' d₂ (minus-flips-<0 x<0) perp'

    caseˡ : d₂ == perpendicularʳ d₁' -> d₂ == perpendicularˡ d₁
    caseˡ p =
      p >=>
      cong perpendicularʳ (sym (perpendicularˡˡ d₁)) >=>
      perpendicularʳˡ _

    caseʳ : d₂ == perpendicularˡ d₁' -> d₂ == perpendicularʳ d₁
    caseʳ p =
      p >=>
      cong perpendicularˡ (sym (perpendicularʳʳ d₁)) >=>
      perpendicularˡʳ _


opaque
  cases-isPerpendicularDirection : ∀ d₁ d₂ ->
    isPerpendicularDirection d₁ d₂ ->
    (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
  cases-isPerpendicularDirection d₁@(direction x₁ y₁ _) d₂ perp =
    handle (trichotomous-< x₁ 0#)
    where
    handle : Tri< x₁ 0# -> (d₂ == perpendicularˡ d₁) ⊎ (d₂ == perpendicularʳ d₁)
    handle (tri< x<0 _ _) = cases-isPerpendicular-x<0 d₁ d₂ x<0 perp
    handle (tri= _ x=0 _) = cases-isPerpendicular-x=0 d₁ d₂ x=0 perp
    handle (tri> _ _ 0<x) = cases-isPerpendicular-0<x d₁ d₂ 0<x perp
