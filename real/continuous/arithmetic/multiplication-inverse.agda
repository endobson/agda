{-# OPTIONS --cubical --safe --exact-split #-}

module real.continuous.arithmetic.multiplication-inverse where

open import additive-group
open import additive-group.apartness
open import additive-group.instances.real
open import base
open import equality
open import funext
open import metric-space
open import metric-space.continuous
open import metric-space.instances.real
open import metric-space.instances.subspace
open import order
open import order.instances.real
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.arithmetic.multiplication.inverse
open import real.continuous.arithmetic
open import real.distance
open import real.subspace
open import ring
open import ring.implementations.real
open import semiring
open import subset.subspace
open import truncation

module _ {ℓD : Level} {D : Type ℓD} {{MS : MetricSpaceStr D}} where
  private
    isContinuousAt-ℝ1/⁺ : {f : D -> ℝ# 0#} -> {x : D} ->
                          isContinuousAt f x ->
                          0# < (Subspace.value (f x)) ->
                          isContinuousAt (\x -> ℝ1/ (f x)) x
    isContinuousAt-ℝ1/⁺ {f} {x} cf 0<v ε⁺@(ε , 0<ε) = ∥-map handle (cf ε'⁺)
      where
      v : ℝ
      v = Subspace.value (f x)

      ε1 : ℝ
      ε1 = v * (v * ε)
      0<ε1 : 0# < ε1
      0<ε1 = *-preserves-0< 0<v (*-preserves-0< 0<v 0<ε)

      0<1+vε : 0# < (1# + v * ε)
      0<1+vε = +-preserves-0< 0<1 (*-preserves-0< 0<v 0<ε)
      1/[1+vε] : ℝ
      1/[1+vε] = ℝ1/ (1# + v * ε , inj-r 0<1+vε)
      0<1/[1+vε] : 0# < 1/[1+vε]
      0<1/[1+vε] = ℝ1/-preserves-0< 0<1+vε

      ε2 : ℝ
      ε2 = 1/[1+vε] * ε1
      0<ε2 : 0# < ε2
      0<ε2 = *-preserves-0< 0<1/[1+vε] 0<ε1


      ε' : ℝ
      ε' = min (min ε1 ε2) v
      ε'⁺ : ℝ⁺
      ε'⁺ = ε' , min-greatest-< (min-greatest-< 0<ε1 0<ε2) 0<v




      handle : Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε'⁺ (f x) (f y)) ->
               Σ[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> εClose ε⁺ (ℝ1/ (f x)) (ℝ1/ (f y)))
      handle (δ , δ-close) = δ , δ-close'
        where
        δ-close' : ∀ y -> εClose δ x y -> εClose ε⁺ (ℝ1/ (f x)) (ℝ1/ (f y))
        δ-close' y dxy<δ =
          max-least-< d-1/fx-1/fy<ε (trans-=-< (sym diff-anticommute) d-1/fy-1/fx<ε)
          where
          v' : ℝ
          v' = Subspace.value (f y)

          df<ε' : distance (f x) (f y) < ε'
          df<ε' = δ-close y dxy<δ

          0<v' : 0# < v'
          0<v' =
            distance-diff-<₂
              (trans-=-< (distance-commuteᵉ v' v)
                (trans-<-= (trans-<-≤ df<ε' min-≤-right) (sym diff0-path)))

          v'<v+ε1 : v' < (v + ε1)
          v'<v+ε1 =
            trans-=-< (sym diff-step)
              (+₁-preserves-< (trans-≤-< max-≤-left
                 (trans-<-≤ df<ε' (trans-≤ min-≤-left min-≤-left))))

          v-ε2<v' : (v + (- ε2)) < v'
          v-ε2<v' =
            trans-<-=
              (+₁-preserves-<
                (trans-<-=
                  (minus-flips-<
                    (trans-≤-<
                      (trans-≤-= max-≤-left (distance-commuteᵉ (f y) (f x)))
                      (trans-<-≤ df<ε' (trans-≤ min-≤-left min-≤-right))))
                  (sym diff-anticommute)))
              diff-step

          0<v+ε1 : 0# < (v + ε1)
          0<v+ε1 = +-preserves-0< 0<v 0<ε1

          1/[v+ε1] : ℝ
          1/[v+ε1] = ℝ1/ (v + ε1 , inj-r 0<v+ε1)
          1/v[1+vε] : ℝ
          1/v[1+vε] = ℝ1/ (v * (1# + v * ε) , inj-r (*-preserves-0< 0<v 0<1+vε))

          1/[v+ε1]<1/fy : 1/[v+ε1] < (ℝ1/ (f y))
          1/[v+ε1]<1/fy = ℝ1/⁺-flips-< 0<v' v'<v+ε1

          d-1/[v+ε1]-1/fx<ε : (diff 1/[v+ε1] (ℝ1/ (f x))) < ε
          d-1/[v+ε1]-1/fx<ε = trans-=-< path3 lt
            where
            1/[v+ε1]=1/v[1+vε] : 1/[v+ε1] == 1/v[1+vε]
            1/[v+ε1]=1/v[1+vε] =
              cong ℝ1/ (Subspace-path (+-left (sym *-right-one) >=> sym *-distrib-+-left))

            path1 : diff 1/[v+ε1] (ℝ1/ (f x)) == ℝ1/ (f x) * (diff 1/[1+vε] 1#)
            path1 = cong2 diff (1/[v+ε1]=1/v[1+vε] >=> ℝ1/-distrib-*) (sym *-right-one) >=>
                    sym *-distrib-diff-left
            path2 : diff 1/[1+vε] 1# == v * (ε * 1/[1+vε])
            path2 =
              cong2 diff (sym *-left-one) (sym ℝ1/-inverse >=> *-commute) >=>
              sym *-distrib-diff-right >=>
              *-left (+-assoc >=> diff-step) >=>
              *-assoc

            path3 : diff 1/[v+ε1] (ℝ1/ (f x)) == (ε * 1/[1+vε])
            path3 = path1 >=> *-right path2 >=> sym *-assoc >=>
                    *-left ℝ1/-inverse >=> *-left-one
            1<1+vε : 1# < (1# + (v * ε))
            1<1+vε = trans-=-< (sym +-right-zero) (+₁-preserves-< (*-preserves-0< 0<v 0<ε))


            lt : (ε * 1/[1+vε]) < ε
            lt = trans-<-= (*₁-preserves-< 0<ε (ℝ1/⁺-flips-< 0<1 1<1+vε))
                           (*-right (sym *-right-one >=>
                                     (ℝ1/-inverseᵉ (_ , inj-r 0<1))) >=>
                            *-right-one)


          d-1/fy-1/fx<ε : (diff (ℝ1/ (f y)) (ℝ1/ (f x))) < ε
          d-1/fy-1/fx<ε =
            trans-< (+₁-preserves-< (minus-flips-< 1/[v+ε1]<1/fy))
                    d-1/[v+ε1]-1/fx<ε


          d-1/fx-1/fy<ε : (diff (ℝ1/ (f x)) (ℝ1/ (f y))) < ε
          d-1/fx-1/fy<ε = d-1/fx-1/fy
            where
            v-ε2=v/[1+vε] : v + (- ε2) == v * 1/[1+vε]
            v-ε2=v/[1+vε] =
              +-left (sym *-left-one >=> *-left (sym ℝ1/-inverse) >=> *-assoc) >=>
              sym *-distrib-diff-left >=>
              *-commute >=>
              *-left (+-left *-commute >=> sym *-distrib-diff-left >=>
                      *-right (+-left +-commute >=> +-assoc >=> diff-step) >=>
                      *-right-one)

            0<v-ε2 : 0# < (v + (- ε2))
            0<v-ε2 = trans-<-= (*-preserves-0< 0<v 0<1/[1+vε]) (sym v-ε2=v/[1+vε])

            path1 : ℝ1/ (v + (- ε2) , inj-r 0<v-ε2) ==
                    ℝ1/ (v * 1/[1+vε] , inj-r (*-preserves-0< 0<v 0<1/[1+vε]))
            path1 = cong ℝ1/ (Subspace-path v-ε2=v/[1+vε])


            1/[v/[1+vε]]=[1+vε]/fx :
              ℝ1/ (v * 1/[1+vε] , inj-r (*-preserves-0< 0<v 0<1/[1+vε])) ==
              (1# + v * ε) * ℝ1/ (f x)
            1/[v/[1+vε]]=[1+vε]/fx =
              ℝ1/-distrib-* >=> *-commute >=>
              *-left (sym *-right-one >=>
                      *-right (sym ℝ1/-inverse) >=>
                      sym *-assoc >=>
                      *-left (ℝ1/-inverseᵉ (_ , ℝ1/-#0)) >=>
                      *-left-one)

            d-1/fx-[1+vε]/fx : diff (ℝ1/ (f x)) ((1# + v * ε) * ℝ1/ (f x)) == ε
            d-1/fx-[1+vε]/fx =
              cong2 diff (sym *-right-one) *-commute >=>
              sym *-distrib-diff-left >=>
              *-right (+-assoc >=> diff-step) >=>
              sym *-assoc >=>
              *-left ℝ1/-inverse >=>
              *-left-one

            d-1/fx-1/fy : diff (ℝ1/ (f x)) (ℝ1/ (f y)) < ε
            d-1/fx-1/fy =
              trans-<-= (+₂-preserves-< (ℝ1/⁺-flips-< 0<v-ε2 v-ε2<v'))
                (cong (diff (ℝ1/ (f x))) (path1 >=> 1/[v/[1+vε]]=[1+vε]/fx) >=>
                 d-1/fx-[1+vε]/fx)

    isContinuousAt-ℝ1/⁻ : {f : D -> ℝ# 0#} -> {x : D} ->
                          isContinuousAt f x ->
                          (Subspace.value (f x)) < 0# ->
                          isContinuousAt (\x -> ℝ1/ (f x)) x
    isContinuousAt-ℝ1/⁻ {f} {x} cf fx<0 =
      subst2 isContinuousAt path (reflᵉ x)
        (isContinuousAt-minus (isContinuousAt-ℝ1/⁺ cf' (minus-flips-<0 fx<0)))
      where
      f' : D -> ℝ# 0#
      f' x = (- (Subspace.value (f x))) , minus-preserves-#0 (Subspace.prop (f x))

      cf' : isContinuousAt f' x
      cf' ε⁺@(ε , _) = transport (\i -> ∃[ δ ∈ ℝ⁺ ] (∀ y -> εClose δ x y -> d y i < ε)) (cf ε⁺)
        where
        d : (y : D) -> distance (f x) (f y) == distance (f' x) (f' y)
        d y = minus-preserves-distance


      path : (\x -> - (ℝ1/ (f' x))) == (\x -> ℝ1/ (f x))
      path = funExt (\x -> cong -_ (sym (ℝ--ℝ1/-commute _)) >=>
                           minus-double-inverse)


  opaque
    isContinuousAt-ℝ1/ : {f : D -> ℝ# 0#} -> {x : D} ->
                         isContinuousAt f x ->
                         isContinuousAt (\x -> ℝ1/ (f x)) x
    isContinuousAt-ℝ1/ {f} {x} cf =
      case (Subspace.prop (f x)) of
        (\{ (inj-l fx<0) -> isContinuousAt-ℝ1/⁻ cf fx<0
          ; (inj-r 0<fx) -> isContinuousAt-ℝ1/⁺ cf 0<fx
          })

    isContinuous-ℝ1/ : {f : D -> ℝ# 0#} ->
                       isContinuous f ->
                       isContinuous (\x -> ℝ1/ (f x))
    isContinuous-ℝ1/ (isContinuous-cons cf) .isContinuous.at x =
      isContinuousAt-ℝ1/ (cf x)
