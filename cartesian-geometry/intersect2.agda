{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.intersect2 where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry
open import cartesian-geometry.line
open import cartesian-geometry.semi-direction
open import cartesian-geometry.semi-direction.apartness
open import cartesian-geometry.vector
open import cartesian-geometry.matrix
open import equality
open import equivalence
open import functions
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import order
open import order.instances.real
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.arithmetic.sqrt
open import real.heyting-field
open import ring
open import ring.implementations.real
open import semiring
open import set-quotient
open import sigma.base
open import solver
open import sum
open import truncation
open import vector-space

private
  module _ (p1 p2 : Point) (d1 d2 : Direction)
           (different-directions : [ d1 ] # [ d2 ])
           where
    private
      v1 = ⟨ d1 ⟩
      v2 = ⟨ d2 ⟩
      d1-path = eqInv (isUnitVector'-equiv v1) (snd d1)
      d2-path = eqInv (isUnitVector'-equiv v2) (snd d2)

      dir-m : Matrix
      dir-m = matrix-transpose (matrix (\ { x-axis -> vector-index v1 ; y-axis -> vector-index v2 }))

      v1#v2 : v1 # v2
      v1#v2 = proj₁ (split-semi-direction-# different-directions)

      v1#-v2 : v1 # (v- v2)
      v1#-v2 = proj₂ (split-semi-direction-# different-directions)

      a = matrix-index dir-m x-axis x-axis
      b = matrix-index dir-m x-axis y-axis
      c = matrix-index dir-m y-axis x-axis
      d = matrix-index dir-m y-axis y-axis

      det-path1 : determinant dir-m == a * d + (- (b * c))
      det-path1 = refl

      4det-1 : ℝ
      4det-1 =
       ((a + (- b)) * (a + (- b)) +
        (d + (- c)) * (d + (- c))) *
       ((a + b) * (a + b) +
        (d + c) * (d + c))

      4det-1#0 : 4det-1 # 0#
      4det-1#0 = *-preserves-#0 left-#0 right-#0
        where
        left-val = ((a + (- b)) * (a + (- b)) + (d + (- c)) * (d + (- c)))
        left-ans = left-val # 0#
        left-#0 : left-ans
        left-#0 = unsquash isProp-# (∥-map handle v1#v2)
          where
          handle : Σ[ ax ∈ Axis ] (vector-index v1 ax # vector-index v2 ax) -> left-ans
          handle (x-axis , a#b) = eqFun (<>-equiv-# _ _) (inj-r 0<left-val)
            where
            0≤cd : 0# ≤ ((diff c d) * (diff c d))
            0≤cd = ≮0-square (diff c d)

            ba#0 : diff b a # 0#
            ba#0 = subst2 _#_ refl +-inverse (+₂-preserves-# a#b)

            0<ba : 0# < ((diff b a) * (diff b a))
            0<ba = handle2 (eqInv (<>-equiv-# _ _) ba#0)
              where
              handle2 : (diff b a < 0#) ⊎ (0# < diff b a) -> _
              handle2 (inj-l ba<0) = *-flips-<0 ba<0 ba<0
              handle2 (inj-r 0<ba) = *-preserves-0< 0<ba 0<ba

            ba≤left-val : ((diff b a) * (diff b a)) ≤ left-val
            ba≤left-val = subst2 _≤_ +-right-zero refl (+₁-preserves-≤ 0≤cd)

            0<left-val = trans-<-≤ 0<ba ba≤left-val
          handle (y-axis , c#d) = eqFun (<>-equiv-# _ _) (inj-r 0<left-val)
            where
            0≤ba : 0# ≤ ((diff b a) * (diff b a))
            0≤ba = ≮0-square (diff b a)

            cd#0 : diff c d # 0#
            cd#0 = subst2 _#_ refl +-inverse (+₂-preserves-# (sym-# c#d))

            0<cd : 0# < ((diff c d) * (diff c d))
            0<cd = handle2 (eqInv (<>-equiv-# _ _) cd#0)
              where
              handle2 : (diff c d < 0#) ⊎ (0# < diff c d) -> _
              handle2 (inj-l cd<0) = *-flips-<0 cd<0 cd<0
              handle2 (inj-r 0<cd) = *-preserves-0< 0<cd 0<cd

            cd≤left-val : ((diff c d) * (diff c d)) ≤ left-val
            cd≤left-val = subst2 _≤_ +-left-zero refl (+₂-preserves-≤ 0≤ba)

            0<left-val = trans-<-≤ 0<cd cd≤left-val

        right-val = ((a + b) * (a + b) + (d + c) * (d + c))
        right-ans = right-val # 0#
        right-#0 : right-ans
        right-#0 = unsquash isProp-# (∥-map handle v1#-v2)
          where
          handle : Σ[ ax ∈ Axis ] (vector-index v1 ax # vector-index (v- v2) ax) -> right-ans
          handle (x-axis , a#-b) = eqFun (<>-equiv-# _ _) (inj-r 0<right-val)
            where
            0≤dc : 0# ≤ ((d + c) * (d + c))
            0≤dc = ≮0-square (d + c)

            ab#0 : (a + b) # 0#
            ab#0 = subst2 _#_ +-commute +-inverse (+₁-preserves-# a#-b)

            0<ab : 0# < ((a + b) * (a + b))
            0<ab = handle2 (eqInv (<>-equiv-# _ _) ab#0)
              where
              handle2 : ((a + b) < 0#) ⊎ (0# < (a + b)) -> _
              handle2 (inj-l ab<0) = *-flips-<0 ab<0 ab<0
              handle2 (inj-r 0<ab) = *-preserves-0< 0<ab 0<ab

            ab≤right-val : ((a + b) * (a + b)) ≤ right-val
            ab≤right-val = subst2 _≤_ +-right-zero refl (+₁-preserves-≤ 0≤dc)

            0<right-val = trans-<-≤ 0<ab ab≤right-val
          handle (y-axis , c#-d) = eqFun (<>-equiv-# _ _) (inj-r 0<right-val)
            where
            0≤ab : 0# ≤ ((a + b) * (a + b))
            0≤ab = ≮0-square (a + b)

            dc#0 : (d + c) # 0#
            dc#0 = subst2 _#_ refl +-inverse (+₁-preserves-# c#-d)

            0<dc : 0# < ((d + c) * (d + c))
            0<dc = handle2 (eqInv (<>-equiv-# _ _) dc#0)
              where
              handle2 : ((d + c) < 0#) ⊎ (0# < (d + c)) -> _
              handle2 (inj-l dc<0) = *-flips-<0 dc<0 dc<0
              handle2 (inj-r 0<dc) = *-preserves-0< 0<dc 0<dc

            dc≤right-val : ((d + c) * (d + c)) ≤ right-val
            dc≤right-val = subst2 _≤_ +-left-zero refl (+₂-preserves-≤ 0≤ab)

            0<right-val = trans-<-≤ 0<dc dc≤right-val

      4det-2 : ℝ
      4det-2 =
        ((((a * a) + (c * c)) + ((b * b) + (d * d))) +
         (- (((a * b) + (a * b)) + ((c * d) + (c * d))))) *
        ((((a * a) + (c * c)) + ((b * b) + (d * d))) +
         (((a * b) + (a * b)) + ((c * d) + (c * d))))


      4det-1=4det-2 : 4det-1 == 4det-2
      4det-1=4det-2 = RingSolver.solve ℝRing 4
        (\a b c d ->
          ((a ⊕ (⊖ b)) ⊗ (a ⊕ (⊖ b)) ⊕
           (d ⊕ (⊖ c)) ⊗ (d ⊕ (⊖ c))) ⊗
          ((a ⊕ b) ⊗ (a ⊕ b) ⊕
           (d ⊕ c) ⊗ (d ⊕ c)) ,
          ((((a ⊗ a) ⊕ (c ⊗ c)) ⊕ ((b ⊗ b) ⊕ (d ⊗ d))) ⊕
           (⊖ (((a ⊗ b) ⊕ (a ⊗ b)) ⊕ ((c ⊗ d) ⊕ (c ⊗ d))))) ⊗
          ((((a ⊗ a) ⊕ (c ⊗ c)) ⊕ ((b ⊗ b) ⊕ (d ⊗ d))) ⊕
           (((a ⊗ b) ⊕ (a ⊗ b)) ⊕ ((c ⊗ d) ⊕ (c ⊗ d)))))
        refl a b c d


      4det-3 : ℝ
      4det-3 =
        ((1# + 1#) + (- (((a * b) + (a * b)) + ((c * d) + (c * d))))) *
        ((1# + 1#) + (((a * b) + (a * b)) + ((c * d) + (c * d))))

      4det-2=4det-3 : 4det-2 == 4det-3
      4det-2=4det-3 =
        *-cong (+-left (+-cong d1-path d2-path))
               (+-left (+-cong d1-path d2-path))

      ℝx² : ℝ -> ℝ
      ℝx² x = (x * x)
      ℝ2x : ℝ -> ℝ
      ℝ2x x = (x + x)
      ℝ4x : ℝ -> ℝ
      ℝ4x = ℝ2x ∘ ℝ2x
      Sx² : {n : Nat} -> RingSyntax n -> RingSyntax n
      Sx² x = (x ⊗ x)
      S2x : {n : Nat} -> RingSyntax n -> RingSyntax n
      S2x x = (x ⊕ x)
      S4x : {n : Nat} -> RingSyntax n -> RingSyntax n
      S4x = S2x ∘ S2x

      ℝ2x-distrib-+ : {x y : ℝ} -> ℝ2x (x + y) == ℝ2x x + ℝ2x y
      ℝ2x-distrib-+ = +-swap
      ℝ2x-distrib-minus : {x : ℝ} -> ℝ2x (- x) == - (ℝ2x x)
      ℝ2x-distrib-minus = sym minus-distrib-plus
      ℝ2x-extract-left : {x y : ℝ} -> (ℝ2x x) * y == ℝ2x (x * y)
      ℝ2x-extract-left = *-distrib-+-right
      ℝ2x-extract-right : {x y : ℝ} -> x * (ℝ2x y) == ℝ2x (x * y)
      ℝ2x-extract-right = *-distrib-+-left

      ℝ2x-reflects-#0 : {x : ℝ} -> ℝ2x x # 0# -> x # 0#
      ℝ2x-reflects-#0 2x#0 =
        unsquash isProp-# (∥-map (either (\x -> x) (\x -> x)) (+-reflects-#0 2x#0))

      ℝx²-reflects-#0 : {x : ℝ} -> ℝx² x # 0# -> x # 0#
      ℝx²-reflects-#0 = *₁-reflects-#0

      4det-4 : ℝ
      4det-4 =
        ℝ4x (((a * a + c * c) * (b * b + d * d)) +
             (- (a * b + c * d) * (a * b + c * d)))

      ones-path : (ℝx² (ℝ2x 1#)) == (ℝ4x 1#)
      ones-path = *-distrib-+-right >=> +-cong *-left-one *-left-one

      4det-3=4det-4 : 4det-3 == 4det-4
      4det-3=4det-4 =
        *-distrib-+-right >=>
        +-cong *-distrib-+-left *-distrib-+-left >=>
        +-assoc >=> +-right (sym +-assoc >=>
                             +-left (+-right (*-commute >=> minus-extract-right) >=> +-inverse) >=>
                             +-left-zero) >=>
        +-left (ones-path >=> cong ℝ4x (sym *-right-one >=> *-cong (sym d1-path) (sym d2-path))) >=>
        +-right (*-cong (cong -_ (sym ℝ2x-distrib-+) >=> sym ℝ2x-distrib-minus)
                        (sym ℝ2x-distrib-+) >=>
                 ℝ2x-extract-right >=>
                 cong ℝ2x ℝ2x-extract-left) >=>
        sym ℝ2x-distrib-+ >=>
        cong ℝ2x (sym ℝ2x-distrib-+)

      rearrange-terms-path :
        (((a * a + c * c) * (b * b + d * d)) +
         (- (a * b + c * d) * (a * b + c * d))) ==
        (ℝx² (a * d + (- (b * c)))) +
        (a * a * b * b + (- (a * a * b * b))) +
        (c * c * d * d + (- (c * c * d * d)))
      rearrange-terms-path = RingSolver.solve ℝRing 4
        (\a b c d ->
          (((a ⊗ a ⊕ c ⊗ c) ⊗ (b ⊗ b ⊕ d ⊗ d)) ⊕
           (⊖ (a ⊗ b ⊕ c ⊗ d) ⊗ (a ⊗ b ⊕ c ⊗ d))) ,
          (Sx² (a ⊗ d ⊕ (⊖ (b ⊗ c)))) ⊕
          (a ⊗ a ⊗ b ⊗ b ⊕ (⊖ (a ⊗ a ⊗ b ⊗ b))) ⊕
          (c ⊗ c ⊗ d ⊗ d ⊕ (⊖ (c ⊗ c ⊗ d ⊗ d)))
        )
        refl a b c d

      cancel-terms-path :
        (((a * a + c * c) * (b * b + d * d)) +
         (- (a * b + c * d) * (a * b + c * d))) == ℝx² (determinant dir-m)
      cancel-terms-path =
        rearrange-terms-path >=>
        +-right +-inverse >=>
        +-right-zero >=>
        +-right +-inverse >=>
        +-right-zero

      full-4det-path : 4det-1 == ℝ4x (ℝx² (determinant dir-m))
      full-4det-path =
        4det-1=4det-2 >=>
        4det-2=4det-3 >=>
        4det-3=4det-4 >=>
        cong ℝ4x cancel-terms-path

      det#0 : (determinant dir-m) # 0#
      det#0 =
        ℝx²-reflects-#0 (ℝ2x-reflects-#0 (ℝ2x-reflects-#0 (subst (_# 0#) full-4det-path 4det-1#0)))

      isInvertible-dir-m : isInvertibleMatrix dir-m
      isInvertible-dir-m = det#0->isInvertible dir-m det#0

      inv-m : Matrix
      inv-m = isInvertibleMatrix.inv isInvertible-dir-m

      coeff : Axis -> ℝ
      coeff = vector-index (inv-m mv* (P-diff p1 p2))

      v = P-diff p1 p2
      diff-decomp : v == (coeff x-axis v* ⟨ d1 ⟩) v+ (coeff y-axis v* ⟨ d2 ⟩)
      diff-decomp =
        sym (mv*-left-identity v) >=>
        cong (_mv* v) (sym (isInvertibleMatrix.right-inverse isInvertible-dir-m)) >=>
        mv*-assoc dir-m inv-m v >=>
        vector-ext (\a -> finiteMerge-Axis _ _ >=>
                          +-cong *-commute *-commute)

      i1 : Point
      i1 = P-shift p1 (coeff x-axis v* v1)
      i2 : Point
      i2 = P-shift p2 (v- (coeff y-axis v* v2))

      l1 : Line
      l1 = [ p1 , [ d1 ] ]
      l2 : Line
      l2 = [ p2 , [ d2 ] ]

      i1=i2 : i1 == i2
      i1=i2 =
        cong (P-shift p1)
          (sym v+-left-zero >=>
           v+-left (sym v+-inverse >=> v+-right (cong v-_ diff-decomp)) >=>
           v+-assoc >=>
           v+-right (v+-left v--distrib-v+ >=>
                     v+-commute >=>
                     sym v+-assoc >=>
                     v+-left v+-inverse >=>
                     v+-left-zero)) >=>
        sym (P-shift-twice p1 (P-diff p1 p2) (v- (coeff y-axis v* v2))) >=>
        cong (\p -> P-shift p (v- (coeff y-axis v* v2))) (P-diff-step p1 p2)

      OnLine-l1i1 : ⟨ OnLine l1 i1 ⟩
      OnLine-l1i1 = coeff x-axis , sym (P-shift-step p1 (coeff x-axis v* v1))

      OnLine-l2i2 : ⟨ OnLine l2 i2 ⟩
      OnLine-l2i2 = (- (coeff y-axis)) ,
                    v*-minus-extract-left >=> sym (P-shift-step p2 (v- (coeff y-axis v* v2)))
      OnLine-l2i1 : ⟨ OnLine l2 i1 ⟩
      OnLine-l2i1 = subst (\i -> ⟨ OnLine l2 i ⟩) (sym i1=i2) OnLine-l2i2

    ans1 : Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩)
    ans1 = i1 , (OnLine-l1i1 , OnLine-l2i1)

    isProp-intersect : isProp (Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩))
    isProp-intersect (pa , (k1-a , path1-a) , (k2-a , path2-a))
                     (pb , (k1-b , path1-b) , (k2-b , path2-b)) =
      ΣProp-path (\{p} -> isProp× (snd (OnLine l1 p)) (snd (OnLine l2 p))) pa=pb
      where
      dp : Vector
      dp = P-diff pa pb

      ¬dp#0 : ¬ (dp # 0v)
      ¬dp#0 dp#0 = irrefl-path-# sd-path different-directions
        where
        v1#0 : v1 # 0v
        v1#0 = direction-#0 d1
        v2#0 : v2 # 0v
        v2#0 = direction-#0 d2

        sd1 : SemiDirection
        sd1 = vector->semi-direction v1 v1#0
        sd2 : SemiDirection
        sd2 = vector->semi-direction v2 v2#0


        path1-ab : (diff k1-a k1-b) v* v1 == dp
        path1-ab =
          v*-distrib-+ >=>
          v+-right (v*-minus-extract-left) >=>
          cong2 _v+_ path1-b (cong v-_ path1-a) >=>
          v+-commute >=>
          v+-left (sym (P-diff-anticommute pa p1)) >=>
          P-diff-trans pa p1 pb

        path2-ab : (diff k2-a k2-b) v* v2 == dp
        path2-ab =
          v*-distrib-+ >=>
          v+-right (v*-minus-extract-left) >=>
          cong2 _v+_ path2-b (cong v-_ path2-a) >=>
          v+-commute >=>
          v+-left (sym (P-diff-anticommute pa p2)) >=>
          P-diff-trans pa p2 pb


        dp-semi : SemiDirection
        dp-semi = vector->semi-direction dp dp#0

        semi-path1 : sd1 == dp-semi
        semi-path1 = vector->semi-direction-v* v1 v1#0 dp dp#0 _ path1-ab
        semi-path2 : sd2 == dp-semi
        semi-path2 = vector->semi-direction-v* v2 v2#0 dp dp#0 _ path2-ab

        normal-d-path : (d : Direction) -> normalize-vector ⟨ d ⟩ (direction-#0 d) == ⟨ d ⟩
        normal-d-path d@(v , len=1) =
          sym v*-left-one >=>
          v*-left (sym len=1) >=>
          (sym (normalize-vector-path v (direction-#0 d)))

        sd-path : [ d1 ] == [ d2 ]
        sd-path =
          cong [_] (sym (direction-ext (normal-d-path d1))) >=>
          semi-path1 >=> sym semi-path2 >=>
          cong [_] (direction-ext (normal-d-path d2))


      dp=0 : dp == 0v
      dp=0 = tight-# ¬dp#0

      pa=pb : pa == pb
      pa=pb = sym (P-shift-0v pa) >=> cong (P-shift pa) (sym dp=0) >=> (P-diff-step pa pb)

    ans2 : isContr (Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩))
    ans2 = ans1 , isProp-intersect ans1

  module _ (p1 p2 : Point) (d1 d2 : Direction) where
    private
      l1 : Line
      l1 = [ p1 , [ d1 ] ]
      l2 : Line
      l2 = [ p2 , [ d2 ] ]

    ans3 : isContr ([ d1 ] # [ d2 ] -> Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩))
    ans3 = isContrΠ (ans2 p1 p2 d1 d2)


  module _ (l1' l2' : Line') where
    private
      p1 = fst l1'
      p2 = fst l2'
      sd1 = snd l1'
      sd2 = snd l2'
      l1 : Line
      l1 = [ l1' ]
      l2 : Line
      l2 = [ l2' ]
    ans4 : isContr (sd1 # sd2 -> Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩))
    ans4 = SemiDirectionElim.liftContr2
             {C2 = \sd1 sd2 -> (sd1 # sd2 -> Σ[ p ∈ Point ] (⟨ OnLine [ p1 , sd1 ] p ⟩ ×
                                                             ⟨ OnLine [ p2 , sd2 ] p ⟩))}
             (ans3 p1 p2) sd1 sd2


  ans5 : (l1 l2 : Line) ->
         isContr (ConvergentLines l1 l2 ->
                  Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩))
  ans5 = SetQuotientElim.liftContr2 Line' SameLine' ans4

  ans6 : (l1 l2 : Line) -> ConvergentLines l1 l2 ->
         isContr (Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩))
  ans6 l1 l2 cls = fst (ans5 l1 l2) cls , \p -> cong (\f -> f cls) (snd (ans5 l1 l2) (\_ -> p))

abstract
  convergent-lines->intersection :
    (l1 l2 : Line) -> ConvergentLines l1 l2 ->
    isContr (Σ[ p ∈ Point ] (⟨ OnLine l1 p ⟩ × ⟨ OnLine l2 p ⟩))
  convergent-lines->intersection = ans6
