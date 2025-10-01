{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.subdivide-box where

open import abs
open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality-path
open import fin
open import finset
open import finset.instances
open import finset.instances.sigma
open import finsum
open import finsum.cardinality
open import hlevel.base
open import hlevel.isomorphism
open import int.base
open import int.nat
open import int.order
open import isomorphism
open import nat
open import nat.order
open import order
open import order.instances.fin
open import order.instances.int
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-semiring
open import ordered-semiring.instances.rational
open import ordered-semiring.natural-reciprocal
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.area.raw
open import rational-geometry.boxes.unital
open import rational-geometry.point
open import rational-geometry.region
open import rational.order
open import rational.quotient
open import ring
open import ring.implementations.int
open import ring.implementations.rational
open import semiring
open import semiring.natural-reciprocal
open import semiring.initial
open import semiring.instances.nat
open import truncation


_/ℕ_ : ℚ⁺ -> Nat⁺ -> ℚ⁺
(q , 0<q) /ℕ n = (q * 1/ℕ n , *-preserves-0< 0<q (0<1/ℕ n))

subdivide-Box : Box -> Nat⁺ -> Nat⁺ -> Boxes ℓ-zero
subdivide-Box b nx⁺@(nx , pnx) ny⁺@(ny , pny) = record
  { Index = (I , isFinSet-× isFinSetⁱ isFinSetⁱ)
  ; box = boxes
  }
  where
  I : Type ℓ-zero
  I = Fin nx × Fin ny

  module b = Box b

  dx : ℚ
  dx = (diff b.left b.right) * 1/ℕ nx⁺
  dy : ℚ
  dy = (diff b.bottom b.top) * 1/ℕ ny⁺
  0<dx : 0# < dx
  0<dx = *-preserves-0< (diff-0<⁺ b.left<right) (0<1/ℕ nx⁺)
  0<dy : 0# < dy
  0<dy = *-preserves-0< (diff-0<⁺ b.bottom<top) (0<1/ℕ ny⁺)

  boxes : I -> Box
  boxes ((x , _) , (y , _)) = record
   { left = b.left + (ℕ->ℚ x * dx)
   ; right = b.left + (ℕ->ℚ (suc x) * dx)
   ; bottom = b.bottom + (ℕ->ℚ y * dy)
   ; top = b.bottom + (ℕ->ℚ (suc y) * dy)
   ; left<right = +₁-preserves-< (*₂-preserves-< (ℕ->ℚ-preserves-< refl-≤) 0<dx)
   ; bottom<top = +₁-preserves-< (*₂-preserves-< (ℕ->ℚ-preserves-< refl-≤) 0<dy)
   }


module _ (b : Box) (nx ny : Nat⁺) where
  private
    B : Boxes ℓ-zero
    B = subdivide-Box b nx ny
    module B = Boxes B
    module b = Box b

    x-coord : ∀ (i₁ i₂ : B.I) (p : Point) ->
      (Box.contains (B.box i₁) p) ->
      (Box.contains (B.box i₂) p) -> proj₁ i₁ == proj₁ i₂
    x-coord i₁ i₂ p p₁ p₂ =
      connected-< (x-coord≮ i₁ i₂ p p₁ p₂) (x-coord≮ i₂ i₁ p p₂ p₁)
      where
      dx : ℚ
      dx = (diff b.left b.right) * 1/ℕ nx

      0<dx : 0# < dx
      0<dx = *-preserves-0< (diff-0<⁺ b.left<right) (0<1/ℕ nx)

      x-coord≮ : ∀ (i₁ i₂ : B.I) (p : Point) ->
        (Box.contains (B.box i₁) p) ->
        (Box.contains (B.box i₂) p) -> proj₁ i₁ ≮ proj₁ i₂
      x-coord≮ ((i₁ , _) , _) ((i₂ , _) , _) p
        (_ , px<b₁r , _ , _) (b₂l≤px , _ , _ , _) (fin< i₁<i₂) =
          (convert-≤ i₂≤i₁ i₁<i₂)
        where
        i₂≤i₁ : i₂ ≤ i₁
        i₂≤i₁ =
          pred-≤ (ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _
           (*₂-reflects-< (+₁-reflects-< (trans-≤-< b₂l≤px px<b₁r)) (asym-< 0<dx))))

    y-coord : ∀ (i₁ i₂ : B.I) (p : Point) ->
      (Box.contains (B.box i₁) p) ->
      (Box.contains (B.box i₂) p) -> proj₂ i₁ == proj₂ i₂
    y-coord i₁ i₂ p p₁ p₂ =
      connected-< (y-coord≮ i₁ i₂ p p₁ p₂) (y-coord≮ i₂ i₁ p p₂ p₁)
      where
      dy : ℚ
      dy = (diff b.bottom b.top) * 1/ℕ ny

      0<dy : 0# < dy
      0<dy = *-preserves-0< (diff-0<⁺ b.bottom<top) (0<1/ℕ ny)

      y-coord≮ : ∀ (i₁ i₂ : B.I) (p : Point) ->
        (Box.contains (B.box i₁) p) ->
        (Box.contains (B.box i₂) p) -> proj₂ i₁ ≮ proj₂ i₂
      y-coord≮ (_ , (i₁ , _)) (_ , (i₂ , _)) p
        (_ , _ , _ , py<b₁t) (_ , _ , b₂b≤py , _) (fin< i₁<i₂) =
          (convert-≤ i₂≤i₁ i₁<i₂)
        where
        i₂≤i₁ : i₂ ≤ i₁
        i₂≤i₁ =
          pred-≤ (ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _
           (*₂-reflects-< (+₁-reflects-< (trans-≤-< b₂b≤py py<b₁t)) (asym-< 0<dy))))

  opaque
    hasNoOverlap-subdivide-Box : hasNoOverlap B
    hasNoOverlap-subdivide-Box p i₁ i₂ p₁ p₂ k =
      x-coord i₁ i₂ p p₁ p₂ k , y-coord i₁ i₂ p p₁ p₂ k

opaque
  subdivide-Box-same-Region : (b : Box) (nx ny : Nat⁺) -> Boxes.region (subdivide-Box b nx ny) == Box.region b
  subdivide-Box-same-Region b nx ny = region-ext (\p -> contains-back p , contains-for p)
    where
    B : Boxes ℓ-zero
    B = subdivide-Box b nx ny
    module B = Boxes B

    contains-for : ∀ p -> Box.contains b p -> Boxes.contains B p
    contains-for (px , py) (bl≤px , px<br , bb≤py , py<bt) =
      ∣ i , (bᵢl≤px , px<bᵢr , bᵢb≤py , py<bᵢt) ∣
      where
      module b = Box b
      dx : ℚ
      dx = diff b.left px
      dy : ℚ
      dy = diff b.bottom py

      ux : ℚ
      ux = (diff b.left b.right) * 1/ℕ nx
      0<ux : 0# < ux
      0<ux = *-preserves-0< (diff-0<⁺ b.left<right) (0<1/ℕ nx)
      ux⁺ : ℚ⁺
      ux⁺ = ux , 0<ux

      uy : ℚ
      uy = (diff b.bottom b.top) * 1/ℕ ny
      0<uy : 0# < uy
      0<uy = *-preserves-0< (diff-0<⁺ b.bottom<top) (0<1/ℕ ny)
      uy⁺ : ℚ⁺
      uy⁺ = uy , 0<uy

      qx : ℤ
      qx = quotientℚ dx ux⁺
      ix : ℕ
      ix = abs' qx
      rx : ℚ
      rx = remainderℚ dx ux⁺
      0≤qx : 0# ≤ qx
      0≤qx = quotientℚ-preserves-0≤ _ _ (diff-0≤⁺ bl≤px)

      qy : ℤ
      qy = quotientℚ dy uy⁺
      iy : ℕ
      iy = abs' qy
      ry : ℚ
      ry = remainderℚ dy uy⁺
      0≤qy : 0# ≤ qy
      0≤qy = quotientℚ-preserves-0≤ _ _ (diff-0≤⁺ bb≤py)


      ix*ux≤dx : (ℕ->ℚ ix * ux) ≤ dx
      ix*ux≤dx =
        trans-≤-=
          (trans-=-≤ (sym +-right-zero)
            (+-preserves-≤ (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ (path-≤ (sym (nonneg-abs' 0≤qx))))
                                           (weaken-< 0<ux))
                           (0≤remainderℚ dx ux⁺)))
          (quotient-remainderℚ dx ux⁺)

      nx*ux=Dx : ℕ->ℚ ⟨ nx ⟩ * ux == diff b.left b.right
      nx*ux=Dx = *-commute >=> *-assoc >=> *-right (1/ℕ-ℕ-path nx) >=> *-right-one

      ix<nx : ix < ⟨ nx ⟩
      ix<nx = ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _ (*₂-reflects-< ixu<wu (asym-< 0<ux)))
        where
        ixu<wu : (ℤ->ℚ (int (abs' qx)) * ux) < (ℕ->ℚ ⟨ nx ⟩ * ux)
        ixu<wu = trans-≤-< ix*ux≤dx (trans-<-= (+₂-preserves-< px<br) (sym nx*ux=Dx))


      iy*uy≤dy : (ℕ->ℚ iy * uy) ≤ dy
      iy*uy≤dy =
        trans-≤-=
          (trans-=-≤ (sym +-right-zero)
            (+-preserves-≤ (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ (path-≤ (sym (nonneg-abs' 0≤qy))))
                                           (weaken-< 0<uy))
                           (0≤remainderℚ dy uy⁺)))
          (quotient-remainderℚ dy uy⁺)

      ny*uy=Dy : ℕ->ℚ ⟨ ny ⟩ * uy == diff b.bottom b.top
      ny*uy=Dy = *-commute >=> *-assoc >=> *-right (1/ℕ-ℕ-path ny) >=> *-right-one

      iy<ny : iy < ⟨ ny ⟩
      iy<ny = ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _ (*₂-reflects-< iyu<wu (asym-< 0<uy)))
        where
        iyu<wu : (ℤ->ℚ (int (abs' qy)) * uy) < (ℕ->ℚ ⟨ ny ⟩ * uy)
        iyu<wu = trans-≤-< iy*uy≤dy (trans-<-= (+₂-preserves-< py<bt) (sym ny*uy=Dy))

      i : B.I
      i = (ix , ix<nx) , (iy , iy<ny)

      bᵢ : Box
      bᵢ = B.box i
      module bᵢ = Box bᵢ


      left-path : bᵢ.left + rx == px
      left-path =
        +-left (+-right (*-left (cong ℤ->ℚ (sym (nonneg-abs' 0≤qx))))) >=>
        +-assoc >=>
        +-right (quotient-remainderℚ dx ux⁺) >=>
        diff-step
      bottom-path : bᵢ.bottom + ry == py
      bottom-path =
        +-left (+-right (*-left (cong ℤ->ℚ (sym (nonneg-abs' 0≤qy))))) >=>
        +-assoc >=>
        +-right (quotient-remainderℚ dy uy⁺) >=>
        diff-step

      right-path : bᵢ.left + ux == bᵢ.right
      right-path =
        +-assoc >=>
        +-right (+-right (sym *-left-one) >=>
                 sym *-distrib-+-right >=>
                 *-left (sym (Semiringʰ.preserves-+ Semiringʰ-ℕ->ℚ _ 1) >=>
                         cong ℕ->ℚ (+-commuteᵉ _ 1)))

      top-path : bᵢ.bottom + uy == bᵢ.top
      top-path =
        +-assoc >=>
        +-right (+-right (sym *-left-one) >=>
                 sym *-distrib-+-right >=>
                 *-left (sym (Semiringʰ.preserves-+ Semiringʰ-ℕ->ℚ _ 1) >=>
                         cong ℕ->ℚ (+-commuteᵉ _ 1)))


      bᵢl≤px : bᵢ.left ≤ px
      bᵢl≤px = trans-=-≤ (sym +-right-zero) (trans-≤-= (+₁-preserves-≤ (0≤remainderℚ dx ux⁺)) left-path)
      bᵢb≤py : bᵢ.bottom ≤ py
      bᵢb≤py = trans-=-≤ (sym +-right-zero) (trans-≤-= (+₁-preserves-≤ (0≤remainderℚ dy uy⁺)) bottom-path)


      px<bᵢr : px < bᵢ.right
      px<bᵢr = trans-=-< (sym left-path) (trans-<-= (+₁-preserves-< (small-remainderℚ dx ux⁺)) right-path)
      py<bᵢt : py < bᵢ.top
      py<bᵢt = trans-=-< (sym bottom-path) (trans-<-= (+₁-preserves-< (small-remainderℚ dy uy⁺)) top-path)


    contains-back' : ∀ p -> Σ[ i ∈ B.I ] (Box.contains (B.box i) p) -> Box.contains b p
    contains-back' p (i@(ix , iy) , (bᵢl≤px , px<bᵢr , bᵢb≤py , py<bᵢt)) =
      trans-≤   bl≤bᵢl bᵢl≤px ,
      trans-<-≤ px<bᵢr bᵢr≤br ,
      trans-≤   bb≤bᵢb bᵢb≤py ,
      trans-<-≤ py<bᵢt bᵢt≤bt
      where
      bᵢ : Box
      bᵢ = B.box i
      module b = Box b
      module bᵢ = Box bᵢ

      ix*dx≤d : (ℕ->ℚ (suc (Fin.i ix)) * ((diff b.left b.right) * 1/ℕ nx)) ≤ (diff b.left b.right)
      ix*dx≤d =
        trans-=-≤
          (sym *-assoc >=> *-left *-commute >=> *-assoc)
          (trans-≤-=
            (*₁-preserves-≤
              (weaken-< (diff-0<⁺ b.left<right))
              (trans-≤-=
                (*₂-preserves-≤ (ℕ->ℚ-preserves-≤ (Fin.i<n ix)) (0≤1/ℕ nx))
                (ℕ-1/ℕ-path nx)))
            *-right-one)
      iy*dy≤d : (ℕ->ℚ (suc (Fin.i iy)) * ((diff b.bottom b.top) * 1/ℕ ny)) ≤ (diff b.bottom b.top)
      iy*dy≤d =
        trans-=-≤
          (sym *-assoc >=> *-left *-commute >=> *-assoc)
          (trans-≤-=
            (*₁-preserves-≤
              (weaken-< (diff-0<⁺ b.bottom<top))
              (trans-≤-=
                (*₂-preserves-≤ (ℕ->ℚ-preserves-≤ (Fin.i<n iy)) (0≤1/ℕ ny))
                (ℕ-1/ℕ-path ny)))
            *-right-one)

      bl≤bᵢl : b.left ≤ bᵢ.left
      bl≤bᵢl =
        trans-=-≤
          (sym +-right-zero)
          (+₁-preserves-≤ (*-preserves-0≤
            (ℕ->ℚ-preserves-≤ zero-≤)
            (weaken-< (*-preserves-0< (diff-0<⁺ b.left<right) (0<1/ℕ nx)))))
      bᵢr≤br : bᵢ.right ≤ b.right
      bᵢr≤br = trans-≤-= (+₁-preserves-≤ ix*dx≤d) diff-step
      bb≤bᵢb : b.bottom ≤ bᵢ.bottom
      bb≤bᵢb =
        trans-=-≤
          (sym +-right-zero)
          (+₁-preserves-≤ (*-preserves-0≤
            (ℕ->ℚ-preserves-≤ zero-≤)
            (weaken-< (*-preserves-0< (diff-0<⁺ b.bottom<top) (0<1/ℕ ny)))))
      bᵢt≤bt : bᵢ.top ≤ b.top
      bᵢt≤bt = trans-≤-= (+₁-preserves-≤ iy*dy≤d) diff-step


    contains-back : ∀ p -> Boxes.contains B p -> Box.contains b p
    contains-back p p∈B =
      unsquash (snd (Region.predicate (Box.region b) p))
               (∥-map (contains-back' p) p∈B)


opaque
  subdivide-Box-same-raw-area : (b : Box) (nx ny : Nat⁺) -> boxes-raw-area (subdivide-Box b nx ny) == Box.area b
  subdivide-Box-same-raw-area b nx ny =
    (\j -> finiteSum (\i -> subbox-area i j)) >=>
    finiteSum-constant >=>
    *-left (cong ℕ->Semiring card-path >=>
            Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ ⟨ nx ⟩ ⟨ ny ⟩) >=>
    *-commute >=>
    *-assoc >=>
    *-right (*-swap >=> *-cong (1/ℕ-ℕ-path _) (1/ℕ-ℕ-path _) >=> *-left-one) >=>
    *-right-one
    where
    module b = Box b
    B : Boxes ℓ-zero
    B = subdivide-Box b nx ny
    module B = Boxes B

    subbox-area : ∀ i -> Box.area (B.box i) == Box.area b * (1/ℕ nx * 1/ℕ ny)
    subbox-area i@(ix , iy) = *-cong width-path height-path >=> *-swap
      where
      module bᵢ = Box (B.box i)

      width-path : (diff bᵢ.left bᵢ.right) == (diff b.left b.right) * 1/ℕ nx
      width-path =
        sym +₁-preserves-diff >=>
        +-right (sym minus-extract-left) >=>
        sym *-distrib-+-right >=>
        *-commute >=>
        *-right (sym (ℤ->ℚ-preserves-diff _ _) >=>
                 cong ℤ->ℚ (sym (ℕ->ℤ-minus refl-≤) >=>
                            cong ℕ->ℤ (+'-minus-right (Fin.i ix)))) >=>
        *-right-one

      height-path : (diff bᵢ.bottom bᵢ.top) == (diff b.bottom b.top) * 1/ℕ ny
      height-path =
        sym +₁-preserves-diff >=>
        +-right (sym minus-extract-left) >=>
        sym *-distrib-+-right >=>
        *-commute >=>
        *-right (sym (ℤ->ℚ-preserves-diff _ _) >=>
                 cong ℤ->ℚ (sym (ℕ->ℤ-minus refl-≤) >=>
                            cong ℕ->ℤ (+'-minus-right (Fin.i iy)))) >=>
        *-right-one

    card-path : (cardinalityⁱ B.I) == (⟨ nx ⟩ * ⟨ ny ⟩)
    card-path = cardinality-× (Fin ⟨ nx ⟩ , isFinSetⁱ) (Fin ⟨ ny ⟩ , isFinSetⁱ)


opaque
  isGridAlignedℚ-self : (u : ℚ⁺)-> isGridAlignedℚ u ⟨ u ⟩
  isGridAlignedℚ-self (u , 0<u) = 1# , *-left-one


  isGridAlignedℚ-+ : (u : ℚ⁺) {a b : ℚ} ->
    isGridAlignedℚ u a -> isGridAlignedℚ u b -> isGridAlignedℚ u (a + b)
  isGridAlignedℚ-+ _ (na , pa) (nb , pb) =
    na + nb , *-left (ℤ->ℚ-preserves-+ _ _) >=> *-distrib-+-right >=> +-cong pa pb

  isGridAlignedℚ-minus : (u : ℚ⁺) {a : ℚ} ->
    isGridAlignedℚ u a -> isGridAlignedℚ u (- a)
  isGridAlignedℚ-minus _ (na , pa) =
    - na , *-left (ℤ->ℚ-preserves-minus _) >=> minus-extract-left >=> cong -_ pa

  isGridAlignedℚ-/ℕ : (u : ℚ⁺) (n : Nat⁺) {a : ℚ} ->
    isGridAlignedℚ u a -> isGridAlignedℚ (u /ℕ n) (a * 1/ℕ n)
  isGridAlignedℚ-/ℕ _ n (na , pa) =
    na , sym *-assoc >=> cong (_* 1/ℕ n) pa

  isGridAlignedℚ-/ℕ' : (u : ℚ⁺) (n : Nat⁺) {a : ℚ} ->
    isGridAlignedℚ u a -> isGridAlignedℚ (u /ℕ n) a
  isGridAlignedℚ-/ℕ' _ n⁺@(n , _) (na , pa) =
    na * (ℕ->ℤ n) ,
    *-left (ℤ->ℚ-preserves-* _ _) >=> *-assoc >=>
    *-right (*-commute >=> *-assoc >=> *-right (1/ℕ-ℕ-path n⁺) >=> *-right-one) >=>
    pa

  isGridAlignedℚ-ℤ* : (u : ℚ⁺) (n : ℤ) {a : ℚ} ->
    isGridAlignedℚ u a -> isGridAlignedℚ u (ℤ->ℚ n * a)
  isGridAlignedℚ-ℤ* _ n (na , pa) =
    n * na , *-left (ℤ->ℚ-preserves-* _ _) >=> *-assoc >=> *-right pa

  isGridAlignedℚ-diff : (u : ℚ⁺) {a b : ℚ} ->
    isGridAlignedℚ u a -> isGridAlignedℚ u b -> isGridAlignedℚ u (diff a b)
  isGridAlignedℚ-diff u ga gb =
    isGridAlignedℚ-+ u gb (isGridAlignedℚ-minus u ga)

  subdivide-Box-isGridAligned₂ : (b : Box) (nx ny : Nat⁺) (ux uy : ℚ⁺) ->
    isGridAligned₂Box ux uy b -> isGridAligned₂Boxes (ux /ℕ nx) (uy /ℕ ny) (subdivide-Box b nx ny)
  subdivide-Box-isGridAligned₂ b nx ny ux uy (gl , gr , gb , gt) _ =
    isGridAlignedℚ-+ (ux /ℕ nx) (isGridAlignedℚ-/ℕ' ux nx gl)
      (isGridAlignedℚ-ℤ* (ux /ℕ nx) _ (isGridAlignedℚ-/ℕ ux nx (isGridAlignedℚ-diff ux gl gr))) ,
    isGridAlignedℚ-+ (ux /ℕ nx) (isGridAlignedℚ-/ℕ' ux nx gl)
      (isGridAlignedℚ-ℤ* (ux /ℕ nx) _ (isGridAlignedℚ-/ℕ ux nx (isGridAlignedℚ-diff ux gl gr))) ,
    isGridAlignedℚ-+ (uy /ℕ ny) (isGridAlignedℚ-/ℕ' uy ny gb)
      (isGridAlignedℚ-ℤ* (uy /ℕ ny) _ (isGridAlignedℚ-/ℕ uy ny (isGridAlignedℚ-diff uy gb gt))) ,
    isGridAlignedℚ-+ (uy /ℕ ny) (isGridAlignedℚ-/ℕ' uy ny gb)
      (isGridAlignedℚ-ℤ* (uy /ℕ ny) _ (isGridAlignedℚ-/ℕ uy ny (isGridAlignedℚ-diff uy gb gt)))


  subdivide-Box-isGridAligned : (b : Box) (n : Nat⁺) (u : ℚ⁺) ->
    isGridAlignedBox u b -> isGridAlignedBoxes (u /ℕ n) (subdivide-Box b n n)
  subdivide-Box-isGridAligned b n u g =
    subdivide-Box-isGridAligned₂ b n n u u g


module _ (b : Box) (nx ny : Nat⁺) where
  private
    B : Boxes ℓ-zero
    B = subdivide-Box b nx ny
    module B = Boxes B

  opaque
    subdivide-Box-side-lengths : (i : B.I) ->
      (diff (Box.left (B.box i)) (Box.right (B.box i)) ==
       diff (Box.left b) (Box.right b) * 1/ℕ nx) ×
      (diff (Box.bottom (B.box i)) (Box.top (B.box i)) ==
       diff (Box.bottom b) (Box.top b) * 1/ℕ ny)
    subdivide-Box-side-lengths i@(ix , iy) =
      path-x , path-y
      where
      module bᵢ = Box (B.box i)
      path-x : diff bᵢ.left bᵢ.right == diff (Box.left b) (Box.right b) * 1/ℕ nx
      path-x =
        sym +₁-preserves-diff >=>
        sym *-distrib-diff-right >=>
        *-left (sym (ℤ->ℚ-preserves-diff _ _) >=>
                cong ℤ->ℚ (sym (ℕ->ℤ-minus refl-≤) >=>
                           cong ℕ->ℤ (+'-minus-right (Fin.i ix)))) >=>
        *-left-one

      path-y : diff bᵢ.bottom bᵢ.top == diff (Box.bottom b) (Box.top b) * 1/ℕ ny
      path-y =
        sym +₁-preserves-diff >=>
        sym *-distrib-diff-right >=>
        *-left (sym (ℤ->ℚ-preserves-diff _ _) >=>
                cong ℤ->ℚ (sym (ℕ->ℤ-minus refl-≤) >=>
                           cong ℕ->ℤ (+'-minus-right (Fin.i iy)))) >=>
        *-left-one

opaque
  subdivide-Box-isUnital : (b : Box) (n : Nat⁺) (u : ℚ⁺) ->
    isUnitalBox u b -> isUnitalBoxes (u /ℕ n) (subdivide-Box b n n)
  subdivide-Box-isUnital b n u (Dx=u , Dy=u) i =
    fst (subdivide-Box-side-lengths b n n i) >=> *-left Dx=u ,
    snd (subdivide-Box-side-lengths b n n i) >=> *-left Dy=u
