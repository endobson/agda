{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.old.unital-subdivide-box where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import fin
open import finset
open import finset.instances
open import finset.instances.sigma
open import int.add1
open import int.addition
open import int.base
open import int.nat
open import int.order
open import nat
open import nat.order
open import order
open import order.instances.int
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.int
open import ordered-semiring
open import ordered-semiring.archimedean.instances.rational -- TODO fix
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.unital
open import rational-geometry.point
open import rational-geometry.region
open import rational.order
open import rational.quotient
open import ring
open import semiring
open import sigma.base
open import truncation

opaque
  subdivide-boxΣ :
    (u : ℚ⁺) (b : Box) -> isGridAlignedBox u b ->
    Σ[ B ∈ Boxes ℓ-zero ] (isGridAlignedBoxes u B × isUnitalBoxes u B × Boxes.region B == Box.region b)
  subdivide-boxΣ u⁺@(u , 0<u) b (ga-l , ga-r , ga-b , ga-t) =
    B ,
    isGridAligned-boxes ,
    isUnital-boxes ,
    region-path
    where
    module b = Box b

    widthℤ : ℤ
    widthℤ = diff ⟨ ga-l ⟩ ⟨ ga-r ⟩
    width : ℕ
    width = abs' widthℤ
    heightℤ : ℤ
    heightℤ = diff ⟨ ga-b ⟩ ⟨ ga-t ⟩
    height : ℕ
    height = abs' heightℤ

    0<widthℤ : 0# < widthℤ
    0<widthℤ = diff-0<⁺ (ℤ->ℚ-reflects-< _ _
      (*₂-reflects-< (subst2 _<_ (sym (snd ga-l)) (sym (snd ga-r)) (Box.left<right b))
                     (asym-< 0<u)))

    0<heightℤ : 0# < heightℤ
    0<heightℤ = diff-0<⁺ (ℤ->ℚ-reflects-< _ _
      (*₂-reflects-< (subst2 _<_ (sym (snd ga-b)) (sym (snd ga-t)) (Box.bottom<top b))
                     (asym-< 0<u)))


    widthℤ-path : ℕ->ℤ width == widthℤ
    widthℤ-path = sym (nonneg-abs' (weaken-< 0<widthℤ))

    width-path : ℕ->ℚ width * u == diff b.left b.right
    width-path =
      *-left (cong ℤ->ℚ widthℤ-path >=> ℤ->ℚ-preserves-diff _ _) >=>
      *-distrib-diff-right >=>
      cong2 diff (snd ga-l) (snd ga-r)


    heightℤ-path : ℕ->ℤ height == heightℤ
    heightℤ-path = sym (nonneg-abs' (weaken-< 0<heightℤ))

    height-path : ℕ->ℚ height * u == diff b.bottom b.top
    height-path =
      *-left (cong ℤ->ℚ heightℤ-path >=> ℤ->ℚ-preserves-diff _ _) >=>
      *-distrib-diff-right >=>
      cong2 diff (snd ga-b) (snd ga-t)





    I : Type₀
    I = Fin width × Fin height

    Index : FinSet ℓ-zero
    Index = I , isFinSetⁱ

    box : I -> Box
    box ((x , _) , (y , _)) = record
     { left = Box.left b + (ℕ->ℚ x * u)
     ; right = Box.left b + (ℕ->ℚ (suc x) * u)
     ; bottom = Box.bottom b + (ℕ->ℚ y * u)
     ; top = Box.bottom b + (ℕ->ℚ (suc y) * u)
     ; left<right = +₁-preserves-< (*₂-preserves-< (ℕ->ℚ-preserves-< refl-≤) 0<u)
     ; bottom<top = +₁-preserves-< (*₂-preserves-< (ℕ->ℚ-preserves-< refl-≤) 0<u)
     }

    B : Boxes ℓ-zero
    B = record { Index = Index ; box = box }

    isUnital-boxes : ∀ i -> isUnitalBox u⁺ (box i)
    isUnital-boxes ((x , _) , (y , _)) =
      sym +₁-preserves-diff >=> sym *-distrib-diff-right >=> *-left px >=> *-left-one ,
      sym +₁-preserves-diff >=> sym *-distrib-diff-right >=> *-left py >=> *-left-one
      where
      px : diff (ℕ->ℚ x) (ℕ->ℚ (suc x)) == 1#
      px = sym (ℤ->ℚ-preserves-diff _ _) >=>
           cong ℤ->ℚ (add1-extract-left >=> cong add1 +-inverse)
      py : diff (ℕ->ℚ y) (ℕ->ℚ (suc y)) == 1#
      py = sym (ℤ->ℚ-preserves-diff _ _) >=>
           cong ℤ->ℚ (add1-extract-left >=> cong add1 +-inverse)

    isGridAligned-boxes : ∀ i -> isGridAlignedBox u⁺ (box i)
    isGridAligned-boxes i@((x , _) , (y , _)) = ga-l' , ga-r' , ga-b' , ga-t'
      where
      ga-l' : isGridAlignedℚ u⁺ (Box.left (box i))
      ga-l' = ⟨ ga-l ⟩ + int x ,
        *-left (ℤ->ℚ-preserves-+ _ _) >=>
        *-distrib-+-right >=>
        +-left (snd ga-l)

      ga-r' : isGridAlignedℚ u⁺ (Box.right (box i))
      ga-r' = ⟨ ga-l ⟩ + int (suc x) ,
        *-left (ℤ->ℚ-preserves-+ _ _) >=>
        *-distrib-+-right >=>
        +-left (snd ga-l)

      ga-b' : isGridAlignedℚ u⁺ (Box.bottom (box i))
      ga-b' = ⟨ ga-b ⟩ + int y ,
        *-left (ℤ->ℚ-preserves-+ _ _) >=>
        *-distrib-+-right >=>
        +-left (snd ga-b)

      ga-t' : isGridAlignedℚ u⁺ (Box.top (box i))
      ga-t' = ⟨ ga-b ⟩ + int (suc y) ,
        *-left (ℤ->ℚ-preserves-+ _ _) >=>
        *-distrib-+-right >=>
        +-left (snd ga-b)


    contained' : ∀ p -> Σ[ i ∈ I ] (Box.contains (box i) p) -> Box.contains b p
    contained' (px , py) (((x , x<width) , (y , y<height)) , (il , ir , ib , it)) =
      al , ar , ab , at
      where
      al : Box.left b ≤ px
      al = trans-≤ (trans-=-≤ (sym +-right-zero)
                     (+₁-preserves-≤ (*-preserves-0≤ (ℕ->ℚ-preserves-≤ zero-≤)
                                                     (weaken-< 0<u))))
                   il

      ar : px < Box.right b
      ar = trans-<-≤ ir (trans-≤-=
        (+-preserves-≤
          (path-≤ (sym (snd ga-l)))
          (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ ar') (weaken-< 0<u)))
        (+-right (*-left (ℤ->ℚ-preserves-diff _ _) >=> *-distrib-diff-right) >=>
         diff-step >=> snd ga-r))
        where
        ar' : int (suc x) ≤ widthℤ
        ar' = trans-≤-= (ℕ->ℤ-preserves-≤ x<width)
                        (sym (nonneg-abs' (weaken-< 0<widthℤ)))



      ab : Box.bottom b ≤ py
      ab = trans-≤ (trans-=-≤ (sym +-right-zero)
                     (+₁-preserves-≤ (*-preserves-0≤ (ℕ->ℚ-preserves-≤ zero-≤)
                                                     (weaken-< 0<u))))
                   ib

      at : py < Box.top b
      at = trans-<-≤ it (trans-≤-=
        (+-preserves-≤
          (path-≤ (sym (snd ga-b)))
          (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ at') (weaken-< 0<u)))
        (+-right (*-left (ℤ->ℚ-preserves-diff _ _) >=> *-distrib-diff-right) >=>
         diff-step >=> snd ga-t))
        where
        at' : int (suc y) ≤ heightℤ
        at' = trans-≤-= (ℕ->ℤ-preserves-≤ y<height)
                        (sym (nonneg-abs' (weaken-< 0<heightℤ)))



    contained : ∀ p -> Boxes.contains B p -> Box.contains b p
    contained p i =
      unsquash (snd (Region.predicate (Box.region b) p))
               (∥-map (contained' p) i)


    covers : ∀ p -> Box.contains b p -> Boxes.contains B p
    covers (px , py) (il , ir , ib , it) =
      ∣ ((ix , ix<width) , (iy , iy<height)) , (ol≤px , px<or , ob≤py , py<or) ∣
      where
      dx : ℚ
      dx = diff (Box.left b) px
      dy : ℚ
      dy = diff (Box.bottom b) py

      qx : ℤ
      qx = quotientℚ dx u⁺
      ix : ℕ
      ix = abs' qx
      rx : ℚ
      rx = remainderℚ dx u⁺

      qy : ℤ
      qy = quotientℚ dy u⁺
      iy : ℕ
      iy = abs' qy
      ry : ℚ
      ry = remainderℚ dy u⁺

      0≤qx : 0# ≤ qx
      0≤qx = quotientℚ-preserves-0≤ _ _ (diff-0≤⁺ il)

      ix*u≤dx : (ℕ->ℚ ix * u) ≤ dx
      ix*u≤dx =
        trans-≤-=
          (trans-=-≤ (sym +-right-zero)
            (+-preserves-≤ (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ (path-≤ (sym (nonneg-abs' 0≤qx))))
                                           (weaken-< 0<u))
                           (0≤remainderℚ dx u⁺)))
          (quotient-remainderℚ dx u⁺)

      ix<width : ix < width
      ix<width = ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _ (*₂-reflects-< ixu<wu (asym-< 0<u)))
        where
        ixu<wu : (ℤ->ℚ (int (abs' qx)) * u) < (ℕ->ℚ width * u)
        ixu<wu = trans-≤-< ix*u≤dx (trans-<-= (+₂-preserves-< ir) (sym width-path))

      dx-path : dx == ℤ->ℚ qx * u + rx
      dx-path = sym (quotient-remainderℚ dx u⁺)
      px-path : px == b.left + dx
      px-path = sym diff-step
      rx<u : rx < u
      rx<u = small-remainderℚ dx u⁺
      dx< : dx < (ℕ->ℚ (suc ix) * u)
      dx< = trans-=-< dx-path (trans-<-= (+₁-preserves-< rx<u)
        (+-right (sym *-left-one) >=>
         sym *-distrib-+-right >=>
         *-left (sym (ℤ->ℚ-preserves-+ _ _) >=>
                 cong ℤ->ℚ (+-commute >=>
                            +-right (nonneg-abs' 0≤qx) >=>
                            sym ℕ->ℤ-+))))

      0≤qy : 0# ≤ qy
      0≤qy = quotientℚ-preserves-0≤ _ _ (diff-0≤⁺ ib)

      iy*u≤dy : (ℕ->ℚ iy * u) ≤ dy
      iy*u≤dy =
        trans-≤-=
          (trans-=-≤ (sym +-right-zero)
            (+-preserves-≤ (*₂-preserves-≤ (ℤ->ℚ-preserves-≤ (path-≤ (sym (nonneg-abs' 0≤qy))))
                                           (weaken-< 0<u))
                           (0≤remainderℚ dy u⁺)))
          (quotient-remainderℚ dy u⁺)

      iy<height : iy < height
      iy<height = ℕ->ℤ-reflects-< (ℤ->ℚ-reflects-< _ _ (*₂-reflects-< iyu<wu (asym-< 0<u)))
        where
        iyu<wu : (ℤ->ℚ (int (abs' qy)) * u) < (ℕ->ℚ height * u)
        iyu<wu = trans-≤-< iy*u≤dy (trans-<-= (+₂-preserves-< it) (sym height-path))

      dy-path : dy == ℤ->ℚ qy * u + ry
      dy-path = sym (quotient-remainderℚ dy u⁺)
      py-path : py == b.bottom + dy
      py-path = sym diff-step
      ry<u : ry < u
      ry<u = small-remainderℚ dy u⁺
      dy< : dy < (ℕ->ℚ (suc iy) * u)
      dy< = trans-=-< dy-path (trans-<-= (+₁-preserves-< ry<u)
        (+-right (sym *-left-one) >=>
         sym *-distrib-+-right >=>
         *-left (sym (ℤ->ℚ-preserves-+ _ _) >=>
                 cong ℤ->ℚ (+-commute >=>
                            +-right (nonneg-abs' 0≤qy) >=>
                            sym ℕ->ℤ-+))))



      ol≤px : (Box.left b + (ℕ->ℚ ix) * u) ≤ px
      ol≤px = trans-≤-= (+₁-preserves-≤ ix*u≤dx) diff-step
      px<or : px < (Box.left b + (ℕ->ℚ (suc ix)) * u)
      px<or = trans-=-< px-path (+₁-preserves-< dx<)
      ob≤py : (Box.bottom b + (ℕ->ℚ iy) * u) ≤ py
      ob≤py = trans-≤-= (+₁-preserves-≤ iy*u≤dy) diff-step
      py<or : py < (Box.bottom b + (ℕ->ℚ (suc iy)) * u)
      py<or = trans-=-< py-path (+₁-preserves-< dy<)


    region-path : Boxes.region B == Box.region b
    region-path = region-ext (\p -> (contained p , covers p))
