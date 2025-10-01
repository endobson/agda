{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.line.off-line where

open import base
open import additive-group
open import apartness
open import apartness.instances.rational
open import equality-path
open import rational
open import hlevel.pi
open import hlevel.base
open import order
open import semiring
open import semidomain
open import semidomain.instances.rational
open import rational-geometry.direction
open import rational-geometry.direction.perpendicular
open import rational-geometry.direction.perpendicular.cases
open import rational-geometry.line
open import rational-geometry.line.point-semidirection
open import rational-geometry.point
open import rational-geometry.translation
open import rational.order
open import set-quotient
open import truncation


record OffLine (p : Point) (l : Line) : Type₀ where
  constructor off-line
  field
    p₀ : Point
    dir : Direction
    k⁺ : ℚ⁺

    on-line : OnLine p₀ l
    perpendicular : isPerpendicularDirectionSemiDirection dir (line->semi-direction l)
    point-path : shift-point (scale-direction ⟨ k⁺ ⟩ dir) p₀ == p

  k : ℚ
  k = ⟨ k⁺ ⟩
  0<k : 0# < k
  0<k = snd k⁺

private
  OffLine->distinct-points : {p : Point} {l : Line} ->
    (o : OffLine p l) -> OffLine.p₀ o != p
  OffLine->distinct-points {p} {l} o = handle (direction-#0 o.dir)
    where
    module o = OffLine o
    module d = Direction o.dir

    contradict : (z : ℚ) (d : ℚ) -> d # 0# -> (z + o.k * d) != z
    contradict z d d#0 z-path = irrefl-path-< (sym k=0) o.0<k
      where
      k*d=0*d : o.k * d == 0# * d
      k*d=0*d =
        sym diff-step >=>
        sym +-assoc >=>
        cong (_+ (- z)) z-path >=>
        +-inverse >=>
        sym *-left-zero

      k=0 : o.k == 0#
      k=0 = *₂-reflects-= d#0 k*d=0*d

    handle : (d.dx # 0#) ⊎ (d.dy # 0#) -> o.p₀ != p
    handle (inj-l dx#0) point-path =
      contradict _ d.dx dx#0 (cong Point.x (o.point-path >=> sym point-path))
    handle (inj-r dy#0) point-path =
      contradict _ d.dy dy#0 (cong Point.y (o.point-path >=> sym point-path))


  same-semi-lemma : ∀ d₁ d₂ sd ->
    isPerpendicularDirectionSemiDirection d₁ sd ->
    isPerpendicularDirectionSemiDirection d₂ sd ->
    SameSemiDirection d₁ d₂
  same-semi-lemma d₁ d₂ =
    SetQuotientElim.elimProp
      (\sd -> isPropΠ2 (\_ _ -> isProp-SameSemiDirection))
      f
    where
    f' : (d₃ : Direction) ->
         (d₃ == perpendicularˡ d₁) ⊎ (d₃ == perpendicularʳ d₁) ->
         (d₃ == perpendicularˡ d₂) ⊎ (d₃ == perpendicularʳ d₂) ->
         SameSemiDirection d₁ d₂
    f' d₃ (inj-l p₁) (inj-l p₂) =
      inj-l (sym (perpendicularʳˡ _) >=> cong perpendicularʳ (sym p₁ >=> p₂) >=> perpendicularʳˡ _)
    f' d₃ (inj-l p₁) (inj-r p₂) =
      inj-r (sym (perpendicularʳˡ _) >=> cong perpendicularʳ (sym p₁ >=> p₂) >=> perpendicularʳʳ _)
    f' d₃ (inj-r p₁) (inj-l p₂) =
      inj-r (sym (perpendicularˡʳ _) >=> cong perpendicularˡ (sym p₁ >=> p₂) >=> perpendicularˡˡ _)
    f' d₃ (inj-r p₁) (inj-r p₂) =
      inj-l (sym (perpendicularˡʳ _) >=> cong perpendicularˡ (sym p₁ >=> p₂) >=> perpendicularˡʳ _)


    f : (d₃ : Direction) ->
        isPerpendicularDirection d₁ d₃ ->
        isPerpendicularDirection d₂ d₃ ->
        SameSemiDirection d₁ d₂
    f d₃ p₁ p₂ = f' d₃ (cases-isPerpendicularDirection _ _ p₁)
                       (cases-isPerpendicularDirection _ _ p₂)



module _ {p : Point} {l : Line} (o₁ o₂ : OffLine p l) (magic : Magic) where
  module o₁ = OffLine o₁
  module o₂ = OffLine o₂

  sd₁ : SemiDirection
  sd₁ = [ o₁.dir ]
  sd₂ : SemiDirection
  sd₂ = [ o₂.dir ]

  sd-path : sd₁ == sd₂
  sd-path = eq/ _ _ (same-semi-lemma _ _ (line->semi-direction l) o₁.perpendicular o₂.perpendicular)

  l₁ : Line
  l₁ = point-semi-direction->line p sd₁
  l₂ : Line
  l₂ = point-semi-direction->line p sd₂

  l-path : l₁ == l₂
  l-path i = point-semi-direction->line p (sd-path i)

  unique-point : ∀ i -> ∃![ pᵢ ∈ Point ] (OnLine pᵢ l × OnLine pᵢ (l-path i))
  unique-point = magic

  p₁-center : Σ[ pᵢ ∈ Point ] (OnLine pᵢ l × OnLine pᵢ l₁)
  p₁-center = o₁.p₀ , o₁.on-line , (- o₁.k , cong (point-shift p) (scale-direction-minus' {o₁.k} {o₁.dir}) >=>
                                             shift-point-swap o₁.point-path)

  p₂-center : Σ[ pᵢ ∈ Point ] (OnLine pᵢ l × OnLine pᵢ l₂)
  p₂-center = o₂.p₀ , o₂.on-line , (- o₂.k , cong (point-shift p) (scale-direction-minus' {o₂.k} {o₂.dir}) >=>
                                             shift-point-swap o₂.point-path)

  center-path : PathP (\i -> Σ[ pᵢ ∈ Point ] (OnLine pᵢ l × OnLine pᵢ (l-path i))) p₁-center p₂-center
  center-path = isProp->PathP (\i -> isContr->isProp (unique-point i))

  p-path : o₁.p₀ == o₂.p₀
  p-path i = fst (center-path i)




  opaque
    isProp-OffLine : o₁ == o₂
    isProp-OffLine = magic
