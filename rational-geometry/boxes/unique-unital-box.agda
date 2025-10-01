{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.unique-unital-box where

open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import hlevel.base
open import hlevel.sigma
open import int.base
open import int.add1
open import int.addition
open import order
open import order.instances.int
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.archimedean.instances.rational
open import rational
open import rational-geometry.boxes.box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.unital
open import rational-geometry.point
open import rational-geometry.region
open import rational.order
open import rational.quotient
open import ring.implementations.int
open import semiring
open import sigma.base
open import truncation

private
  ℤ<->ℤ≤ : ∀ {a b : ℤ} -> a < b -> add1 a ≤ b
  ℤ<->ℤ≤ ((suc n , _) , p) = (n , (add1-extract-right >=> sym add1-extract-left >=> p))

module _ (u⁺@(u , 0<u) : ℚ⁺) where
  private
    unitalBox-path :
      (b₁ b₂ : Box) -> (isUnitalBox u⁺ b₁) -> (isUnitalBox u⁺ b₂) ->
      (Box.left b₁ == Box.left b₂) ->
      (Box.bottom b₁ == Box.bottom b₂) ->
      b₁ == b₂
    unitalBox-path b₁ b₂ (ux₁ , uy₁) (ux₂ , uy₂) lp bp =
      Box-coord-path b₁ b₂ lp rp bp tp
      where
      rp : Box.right b₁ == Box.right b₂
      rp = sym diff-step >=> +-right ux₁ >=>
           +-left lp >=>
           +-right (sym ux₂) >=> diff-step
      tp : Box.top b₁ == Box.top b₂
      tp = sym diff-step >=> +-right uy₁ >=>
           +-left bp >=>
           +-right (sym uy₂) >=> diff-step

    unitalGridBox-path :
      (b₁ b₂ : Box) ->
      (isUnitalBox u⁺ b₁) -> (isUnitalBox u⁺ b₂) ->
      (g₁ : isGridAlignedBox u⁺ b₁) -> (g₂ : isGridAlignedBox u⁺ b₂) ->
      fst (proj₁ g₁) == fst (proj₁ g₂) ->
      fst (proj₁ (proj₂ (proj₂ g₁))) == fst (proj₁ (proj₂ (proj₂ g₂))) ->
      b₁ == b₂
    unitalGridBox-path b₁ b₂ u₁ u₂
      ((_ , pl₁) , _ , (_ , pb₁) , _)
      ((_ , pl₂) , _ , (_ , pb₂) , _)
      nlp nbp =
      unitalBox-path b₁ b₂ u₁ u₂
        (sym pl₁ >=> *-left (cong ℤ->ℚ nlp) >=> pl₂)
        (sym pb₁ >=> *-left (cong ℤ->ℚ nbp) >=> pb₂)


    coord-contradiction : (x : ℚ) (y₁ y₂ y₃ : ℚ)
      (dy₁y₂=u= : diff y₁ y₂ == u) (x<y₂ : x < y₂) (y₃≤x : y₃ ≤ x) ->
      (g₁ : isGridAlignedℚ u⁺ y₁) -> (g₂ : isGridAlignedℚ u⁺ y₃) ->
      fst g₁ < fst g₂ ->
      Bot
    coord-contradiction x y₁ y₂ y₃ dy₁y₂=u x<y₂ y₃≤x (n₁ , p₁) (n₂ , p₂) n₁<n₂ =
      irrefl-< x<x
      where
      x<y₁+u : x < (y₁ + u)
      x<y₁+u = trans-<-= x<y₂ (sym diff-step >=> +-right dy₁y₂=u)
      n₁+1≤n₂ : (n₁ + 1#) ≤ n₂
      n₁+1≤n₂ =
        trans-=-≤ (add1-extract-right >=> cong add1 +-right-zero)
                  (ℤ<->ℤ≤ n₁<n₂)
      y₁+u≤y₃ : (y₁ + u) ≤ y₃
      y₁+u≤y₃ =
        trans-=-≤
          (+-cong (sym p₁) (sym *-left-one) >=>
           sym *-distrib-+-right >=>
           *-left (sym (ℤ->ℚ-preserves-+ _ _)))
          (trans-≤-=
            (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ n₁+1≤n₂) (weaken-< 0<u))
            p₂)
      x<x : x < x
      x<x = trans-<-≤ x<y₁+u (trans-≤ y₁+u≤y₃ y₃≤x)


    unitalGridBox-contains-path :
      (b₁ b₂ : Box) ->
      (isUnitalBox u⁺ b₁) -> (isUnitalBox u⁺ b₂) ->
      (g₁ : isGridAlignedBox u⁺ b₁) -> (g₂ : isGridAlignedBox u⁺ b₂) ->
      (p : Point) -> Box.contains b₁ p -> Box.contains b₂ p ->
      b₁ == b₂
    unitalGridBox-contains-path b₁ b₂ U₁@(u₁ , u₃) U₂@(u₂ , u₄)
      G₁@(g₁@(n₁ , _) , _ , g₃@(n₃ , _) , _)
      G₂@(g₂@(n₂ , _) , _ , g₄@(n₄ , _) , _)
      (x , y)
      (left₁≤x , x<right₁ , bottom₁≤y , y<top₁)
      (left₂≤x , x<right₂ , bottom₂≤y , y<top₂) =
      unitalGridBox-path b₁ b₂ U₁ U₂ G₁ G₂ n₁=n₂ n₃=n₄
      where
      module b₁ = Box b₁
      module b₂ = Box b₂

      n₁=n₂ : n₁ == n₂
      n₁=n₂ = connected-<
        (coord-contradiction x b₁.left b₁.right b₂.left u₁ x<right₁ left₂≤x g₁ g₂)
        (coord-contradiction x b₂.left b₂.right b₁.left u₂ x<right₂ left₁≤x g₂ g₁)
      n₃=n₄ : n₃ == n₄
      n₃=n₄ = connected-<
        (coord-contradiction y b₁.bottom b₁.top b₂.bottom u₃ y<top₁ bottom₂≤y g₃ g₄)
        (coord-contradiction y b₂.bottom b₂.top b₁.bottom u₄ y<top₂ bottom₁≤y g₄ g₃)




  private
    isGridAligned-+u : {x : ℚ} -> isGridAlignedℚ u⁺ x -> isGridAlignedℚ u⁺ (x + u)
    isGridAligned-+u (z , p) = (z + 1#) ,
      *-left (ℤ->ℚ-preserves-+ z 1#) >=>
      *-distrib-+-right >=>
      +-left p >=>
      +-right *-left-one

    grid-point->grid-unital-box : Σ[ p ∈ Point ] (isGridAlignedPoint u⁺ p) ->
      Σ[ b ∈ Box ] (isGridAlignedBox u⁺ b × isUnitalBox u⁺ b)
    grid-point->grid-unital-box ((x , y) , (ax , ay)) = b , isGrid-b , isUnital-b
      where
      b : Box
      b = record
        { left = x
        ; bottom = y
        ; right = x + u
        ; top = y + u
        ; left<right = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<u)
        ; bottom<top = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<u)
        }

      isGrid-b : isGridAlignedBox u⁺ b
      isGrid-b = (ax , isGridAligned-+u ax , ay , isGridAligned-+u ay)

      isUnital-b : isUnitalBox u⁺ b
      isUnital-b = (+-assoc >=> diff-step , +-assoc >=> diff-step)


    point->grid-point : Point -> Σ[ p ∈ Point ] (isGridAlignedPoint u⁺ p)
    point->grid-point (x , y) = ans , isGridPoint-ans
      where
      qx : ℤ
      qx = quotientℚ x u⁺
      rx : ℚ
      rx = remainderℚ x u⁺
      qy : ℤ
      qy = quotientℚ y u⁺
      ry : ℚ
      ry = remainderℚ y u⁺

      ans : Point
      ans = ℤ->ℚ qx * u , ℤ->ℚ qy * u

      isGridPoint-ans : isGridAlignedPoint u⁺ ans
      isGridPoint-ans = (qx , refl) , (qy , refl)

    point->box : Point -> Box
    point->box p = fst (grid-point->grid-unital-box (point->grid-point p))

    point∈box : (p : Point) -> Region.contains (Box.region (point->box p)) p
    point∈box p = gpx≤px , px<gpx' , gpy≤py , py<gpy'
      where
      gp : Point
      gp = fst (point->grid-point p)

      module p = Point p
      module gp = Point gp

      gpx≤px : gp.x ≤ p.x
      gpx≤px =
        trans-=-≤ (sym +-right-zero)
          (trans-≤-= (+₁-preserves-≤ (0≤remainderℚ p.x u⁺))
                     (quotient-remainderℚ p.x u⁺))
      gpy≤py : gp.y ≤ p.y
      gpy≤py =
        trans-=-≤ (sym +-right-zero)
          (trans-≤-= (+₁-preserves-≤ (0≤remainderℚ p.y u⁺))
                     (quotient-remainderℚ p.y u⁺))

      px<gpx' : p.x < (gp.x + u)
      px<gpx' =
        trans-=-< (sym (quotient-remainderℚ p.x u⁺))
          (+₁-preserves-< (small-remainderℚ p.x u⁺))
      py<gpy' : p.y < (gp.y + u)
      py<gpy' =
        trans-=-< (sym (quotient-remainderℚ p.y u⁺))
          (+₁-preserves-< (small-remainderℚ p.y u⁺))


    isProp-grid-unital : (p : Point) (b : Box) ->
      isProp (isGridAlignedBox u⁺ b ×
              isUnitalBox u⁺ b ×
              Region.contains (Box.region b) p)
    isProp-grid-unital p b =
      isProp× (isProp-isGridAlignedBox u⁺ b)
        (isProp× (isProp-isUnitalBox u⁺ b)
                 (snd (Region.predicate (Box.region b) p)))

  point->∃!grid-unital-box : (p : Point) -> ∃![ b ∈ Box ] (
    isGridAlignedBox u⁺ b ×
    isUnitalBox u⁺ b ×
    Region.contains (Box.region b) p)
  point->∃!grid-unital-box p = center , isProp-T _
    where
    gu = snd (grid-point->grid-unital-box (point->grid-point p))
    T : Type _
    T = Σ[ b ∈ Box ] (isGridAlignedBox u⁺ b ×
                      isUnitalBox u⁺ b ×
                      Region.contains (Box.region b) p)

    center : T
    center = (point->box p , fst gu , snd gu , point∈box p)

    isProp-T : isProp T
    isProp-T (b₁ , g₁ , u₁ , p∈b₁) (b₂ , g₂ , u₂ , p∈b₂) =
      ΣProp-path (\{b} -> isProp-grid-unital p b)
        (unitalGridBox-contains-path
          b₁ b₂ u₁ u₂ g₁ g₂ p p∈b₁ p∈b₂)
