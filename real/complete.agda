{-# OPTIONS --cubical --safe --exact-split #-}

module real.complete where

open import additive-group
open import additive-group.instances.real
open import base
open import hlevel.base
open import heyting-field.instances.rational
open import heyting-field.instances.real
open import equality
open import metric-space
open import metric-space.complete
open import metric-space.continuous
open import metric-space.instances.real
open import net
open import order
open import ordered-field
open import ordered-field.mean
open import order.minmax
open import order.minmax.instances.real
open import order.instances.rational
open import order.instances.real
open import ordered-semiring
open import ordered-additive-group
open import ordered-additive-group.instances.rational
open import ordered-additive-group.instances.real
open import ordered-semiring.instances.real
open import ordered-semiring.instances.rational
open import rational
open import nat.arithmetic
open import real
open import real.order
open import real.subspace
open import real.sequence
open import real.rational
open import real.arithmetic.rational
open import relation hiding (U)
open import ring.implementations.real
open import ring.implementations.rational
open import semiring
open import subset.subspace
open import truncation

private
  ℚ->ℝ-preserves-1/2 : _
  ℚ->ℝ-preserves-1/2 = Semiringʰ-preserves-1/ℕ Semiringʰ-ℚ->ℝ 2⁺

opaque
  isComplete₀-ℝ : isComplete₀ ℝ
  isComplete₀-ℝ N cauchy = x , isLimit-x
    where
    module N = Net N
    I : Type₀
    I = N.I
    f : I -> ℝ
    f = N.f
    instance
      -- TODO add accessor for this
      IPO : isPreOrder N.≼
      IPO = DirectedSet.isPreOrder-R (N.directed-set)

    L' : Pred ℚ ℓ-zero
    L' q = Σ[ q' ∈ ℚ ] ((q < q') × isEventually N (\x -> Real.L x q'))
    U' : Pred ℚ ℓ-zero
    U' q = Σ[ q' ∈ ℚ ] ((q' < q) × isEventually N (\x -> Real.U x q'))

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥
    U : Pred ℚ ℓ-zero
    U q = ∥ U' q ∥

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-bind handle (cauchy ε)
      where
      ε : ℝ⁺
      ε = (1# , 0<1)
      handle : Σ[ i ∈ I ] (∀ i2 i3 -> i ≼ i2 -> i ≼ i3 -> εClose ε (f i2) (f i3)) -> Inhabited L
      handle (i , close) = ∥-bind handle2 (Real.Inhabited-L (f i))
        where
        handle2 : Σ ℚ (Real.L (f i)) -> Inhabited L
        handle2 (q , fiL-q) = ∣ (q + (- 1#)) + (- 1#) , ∣ q + (- 1#) , q-2<q-1 , ∣ i , close-L' ∣ ∣ ∣
          where
          q-1<q : (q + (- 1#)) < q
          q-1<q = trans-<-= (+₁-preserves-< (minus-flips-0< 0<1)) +-right-zero
          q-2<q-1 : ((q + (- 1#)) + (- 1#)) < (q + (- 1#))
          q-2<q-1 = +₂-preserves-< q-1<q
          close-L' : ∀ i2 -> i ≼ i2 -> Real.L (f i2) (q + (- 1#))
          close-L' i2 i≼i2 =
            ℝ<->L (trans-=-< ℚ->ℝ-preserves-diff (trans-<-= (+-preserves-< q<fi -1<diff) diff-step))
            where
            q<fi : ℚ->ℝ q < f i
            q<fi = L->ℝ< fiL-q
            dis<1 : distance (f i) (f i2) < 1#
            dis<1 = close i i2 refl-≼ i≼i2
            diff<1 : diff (f i2) (f i) < 1#
            diff<1 = trans-≤-< (trans-≤-= max-≤-left distance-commute) dis<1
            -1<diff : (- 1#) < diff (f i) (f i2)
            -1<diff = trans-<-= (minus-flips-< diff<1) (sym diff-anticommute)

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-bind handle (cauchy ε)
      where
      ε : ℝ⁺
      ε = (1# , 0<1)
      handle : Σ[ i ∈ I ] (∀ i2 i3 -> i ≼ i2 -> i ≼ i3 -> εClose ε (f i2) (f i3)) -> Inhabited U
      handle (i , close) = ∥-bind handle2 (Real.Inhabited-U (f i))
        where
        handle2 : Σ ℚ (Real.U (f i)) -> Inhabited U
        handle2 (q , fiU-q) = ∣ (q + 1#) + 1# , ∣ q + 1# , q+1<q+2 , ∣ i , close-U' ∣ ∣ ∣
          where
          q<q+1 : q < (q + 1#)
          q<q+1 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1)
          q+1<q+2 : (q + 1#) < ((q + 1#) + 1#)
          q+1<q+2 = +₂-preserves-< q<q+1
          close-U' : ∀ i2 -> i ≼ i2 -> Real.U (f i2) (q + 1#)
          close-U' i2 i≼i2 =
            ℝ<->U (trans-<-= (trans-=-< (sym diff-step) (+-preserves-< fi<q diff<1))
                             (sym ℚ->ℝ-preserves-+))
            where
            fi<q : f i < ℚ->ℝ q
            fi<q = U->ℝ< fiU-q
            dis<1 : distance (f i) (f i2) < 1#
            dis<1 = close i i2 refl-≼ i≼i2
            diff<1 : diff (f i) (f i2) < 1#
            diff<1 = trans-≤-< max-≤-left dis<1

    disjoint : Universal (Comp (L ∩ U))
    disjoint q (Lq , Uq) = unsquash isPropBot (∥-bind2 handle Lq Uq)
      where
      handle : L' q -> U' q -> ∥ Bot ∥
      handle (q1 , q<q1 , q1-close) (q2 , q2<q , q2-close) =
        ∥-map handle2 (isEventually-∩ N (\x -> Real.L x q1) (\x -> Real.U x q2) q1-close q2-close)
        where
        handle2 : isEventuallyΣ N (\x -> Real.L x q1 × Real.U x q2) -> Bot
        handle2 (i , q12-close) = handle3 (q12-close i N.refl-≼)
          where
          handle3 : Real.L (f i) q1 × Real.U (f i) q2 -> Bot
          handle3 (fiL-q1 , fiU-q2) =
            irrefl-< (trans-< (trans-< (ℚ->ℝ-preserves-< q<q1) q1<fi)
                              (trans-< fi<q2 (ℚ->ℝ-preserves-< q2<q)))
            where
            q1<fi : ℚ->ℝ q1 < f i
            q1<fi = (L->ℝ< fiL-q1)
            fi<q2 : f i < ℚ->ℝ q2
            fi<q2 = (U->ℝ< fiU-q2)


    located : (q r : ℚ) -> q < r -> ∥ L q ⊎ U r ∥
    located q r q<r = ∥-bind handle (cauchy d/8⁺)
      where
      d : ℚ
      d = diff q r
      0<d : 0# < d
      0<d = diff-0<⁺ q<r
      d/8 : ℚ
      d/8 = 1/2 * (1/2 * (1/2 * d))
      0<d/8 : 0# < d/8
      0<d/8 = *-preserves-0< 0<1/2 (*-preserves-0< 0<1/2 (*-preserves-0< 0<1/2 0<d))
      d/8⁺ : ℝ⁺
      d/8⁺ = (ℚ->ℝ d/8 , ℚ->ℝ-preserves-< 0<d/8)
      m q' r' l u : ℚ
      m = mean q r
      q' = mean q m
      r' = mean m r
      l = mean q q'
      u = mean r' r

      q<m : q < m
      q<m = mean-<₁ q<r
      m<r : m < r
      m<r = mean-<₂ q<r
      q<q' : q < q'
      q<q' = mean-<₁ q<m
      r'<r : r' < r
      r'<r = mean-<₂ m<r
      q<l : q < l
      q<l = mean-<₁ q<q'
      u<r : u < r
      u<r = mean-<₂ r'<r


      q'<r' : q' < r'
      q'<r' = trans-< (mean-<₂ q<m) (mean-<₁ m<r)

      -- fix order of these
      d/2=qm : diff q m == 1/2 * d
      d/2=qm = diff-mean'
      d/4=qq' : diff q q' == 1/2 * (1/2 * d)
      d/4=qq' = diff-mean' >=> cong (1/2 *_) d/2=qm
      d/8=lq' : diff l q' == d/8
      d/8=lq' = diff-mean >=> cong (1/2 *_) d/4=qq'

      d/2=mr : diff m r == 1/2 * d
      d/2=mr = diff-mean
      d/4=r'r : diff r' r == 1/2 * (1/2 * d)
      d/4=r'r = diff-mean >=> cong (1/2 *_) d/2=mr
      d/8=r'u : diff r' u == d/8
      d/8=r'u = diff-mean' >=> cong (1/2 *_) d/4=r'r


      handle : Σ[ i ∈ I ] (∀ i2 i3 -> i ≼ i2 -> i ≼ i3 -> εClose d/8⁺ (f i2) (f i3)) -> ∥ L q ⊎ U r ∥
      handle (i , d/8-close) = ∥-bind handle2 (Real.located (f i) q' r' q'<r')
        where
        handle2 : Real.L (f i) q' ⊎ Real.U (f i) r' -> ∥ L q ⊎ U r ∥
        handle2 (inj-l fiL-q') =
          ∣ inj-l (∣ l  , q<l , (∣ i , lbound ∣) ∣) ∣
          where
          q'<fi : ℚ->ℝ q' < f i
          q'<fi = L->ℝ< fiL-q'

          lbound : ∀ i2 -> i ≼ i2 -> Real.L (f i2) l
          lbound i2 i≼i2 = ℝ<->L bound3
            where
            bound1 : distance (f i) (f i2) < (diff (ℚ->ℝ l) (ℚ->ℝ q'))
            bound1 = trans-<-= (d/8-close i i2 refl-≼ i≼i2)
                               (cong ℚ->ℝ (sym d/8=lq') >=> ℚ->ℝ-preserves-diff)
            bound2 : (diff (ℚ->ℝ q') (ℚ->ℝ l)) < diff (f i) (f i2)
            bound2 =
              subst2 _<_ (sym diff-anticommute) (sym diff-anticommute)
                (minus-flips-< (trans-≤-< (trans-≤-= max-≤-left distance-commute) bound1))
            bound3 : ℚ->ℝ l < f i2
            bound3 = subst2 _<_ diff-step diff-step (+-preserves-< q'<fi bound2)
        handle2 (inj-r fiU-r') =
          ∣ inj-r (∣ u  , u<r , (∣ i , ubound ∣) ∣) ∣
          where
          fi<r' : f i < ℚ->ℝ r'
          fi<r' = U->ℝ< fiU-r'

          ubound : ∀ i2 -> i ≼ i2 -> Real.U (f i2) u
          ubound i2 i≼i2 = ℝ<->U bound3
            where
            bound1 : distance (f i) (f i2) < (diff (ℚ->ℝ r') (ℚ->ℝ u))
            bound1 = trans-<-= (d/8-close i i2 refl-≼ i≼i2)
                               (cong ℚ->ℝ (sym d/8=r'u) >=> ℚ->ℝ-preserves-diff)
            bound2 : diff (f i) (f i2) < (diff (ℚ->ℝ r') (ℚ->ℝ u))
            bound2 = trans-≤-< max-≤-left bound1
            bound3 : f i2 < ℚ->ℝ u
            bound3 = subst2 _<_ diff-step diff-step (+-preserves-< fi<r' bound2)

    isLowerSet-L : isLowerSet L
    isLowerSet-L {q} {r} q<r = ∥-map handle
      where
      handle : L' r -> L' q
      handle (r' , r<r' , er') = (r' , trans-< q<r r<r' , er')

    isUpperSet-U : isUpperSet U
    isUpperSet-U {q} {r} q<r = ∥-map handle
      where
      handle : U' q -> U' r
      handle (q' , q'<q , eq') = (q' , trans-< q'<q q<r , eq')

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-map handle
      where
      handle : L' q -> Σ[ r ∈ ℚ ] (q < r × L r)
      handle (q' , q<q' , eq') =
        mean q q' , mean-<₁ q<q' , ∣ q' , mean-<₂ q<q' , eq' ∣

    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q = ∥-map handle
      where
      handle : U' q -> Σ[ r ∈ ℚ ] (r < q × U r)
      handle (q' , q'<q , eq') =
        mean q' q , mean-<₂ q'<q , ∣ q' , mean-<₁ q'<q , eq' ∣

    x : ℝ
    x = record
      { L = L
      ; U = U
      ; isProp-L = \_ -> squash
      ; isProp-U = \_ -> squash
      ; Inhabited-L = Inhabited-L
      ; Inhabited-U = Inhabited-U
      ; isLowerSet-L = isLowerSet-L
      ; isUpperSet-U = isUpperSet-U
      ; isUpperOpen-L = isUpperOpen-L
      ; isLowerOpen-U = isLowerOpen-U
      ; disjoint = disjoint
      ; located = located
      }

    isLimit-x : isLimit N x
    isLimit-x .isLimit.close ε⁺@(ε , 0<ε) = ∥-bind handle 0<ε/4
      where
      ε/4 : ℝ
      ε/4 = 1/2 * (1/2 * ε)
      0<ε/4 : 0# < ε/4
      0<ε/4 = *-preserves-0< 0<1/2 (*-preserves-0< 0<1/2 0<ε)
      handle : 0# ℝ<' ε/4 -> isEventually N (εClose ε⁺ x)
      handle (ℝ<'-cons ε' 0U-ε' ε/4L-ε') = ∥-bind handle2 (cauchy ε'⁺)
        where
        ε'<ε/4 : ℚ->ℝ ε' < ε/4
        ε'<ε/4 = L->ℝ< ε/4L-ε'
        4ε'<ε : ℚ->ℝ ((ε' + ε') + (ε' + ε')) < ε
        4ε'<ε =
          trans-=-< (ℚ->ℝ-preserves-+ >=> +-cong ℚ->ℝ-preserves-+ ℚ->ℝ-preserves-+)
            (trans-<-= (+-preserves-< (+-preserves-< ε'<ε/4 ε'<ε/4) (+-preserves-< ε'<ε/4 ε'<ε/4))
              (+-cong 1/2-path 1/2-path >=> 1/2-path))
        0<ε' : 0# < ε'
        0<ε' = U->ℚ< 0U-ε'
        -ε'<0 : (- ε') < 0#
        -ε'<0 = minus-flips-0< 0<ε'
        ε'⁺ : ℝ⁺
        ε'⁺ = (ℚ->ℝ ε' , U->ℝ< 0U-ε')
        handle2 : Σ[ i ∈ N.I ] ((i₁ i₂ : N.I) -> i ≼ i₁ -> i ≼ i₂ ->
                               εClose ε'⁺ (f i₁) (f i₂)) ->
                 isEventually N (εClose ε⁺ x)
        handle2 (i , ε'-close) = ∣ i , ε-close ∣
          where
          ε-close : ∀ i2 -> i ≼ i2 -> εClose ε⁺ x (f i2)
          ε-close i2 i≼i2 =
            unsquash isProp-< (∥-map handle3
              (find-open-ball (f i2) (ε' + ε' , +-preserves-0< 0<ε' 0<ε')))
            where
            handle3 : OpenBall (f i2) (ε' + ε') -> εClose ε⁺ x (f i2)
            handle3 (l , u , fi2L-l , fi2U-u , dlu=2ε') =
              max-least-< d1<ε (trans-=-< (sym diff-anticommute) d2<ε)
              where
              l<fi2 : ℚ->ℝ l < f i2
              l<fi2 = L->ℝ< fi2L-l
              fi2<u : f i2 < ℚ->ℝ u
              fi2<u = U->ℝ< fi2U-u
              u' u'' l' l'' : ℚ
              u' = u + ε'
              u'' = u' + ε'
              l' = l + (- ε')
              l'' = l' + (- ε')
              l'<l : l' < l
              l'<l = trans-<-= (+₁-preserves-< -ε'<0) +-right-zero
              l''<l' : l'' < l'
              l''<l' = +₂-preserves-< l'<l
              u<u' : u < u'
              u<u' = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<ε')
              u'<u'' : u' < u''
              u'<u'' = +₂-preserves-< u<u'

              dl''u=4ε' : diff l'' u == ((ε' + ε') + (ε' + ε'))
              dl''u=4ε' =
                sym diff-trans >=>
                +-right dlu=2ε' >=>
                +-left (+-right (sym diff-anticommute >=>
                                 +-right (sym diff-anticommute) >=>
                                 sym +-assoc) >=>
                        diff-step)

              dlu''=4ε' : diff l u'' == ((ε' + ε') + (ε' + ε'))
              dlu''=4ε' =
                sym diff-trans >=>
                +-left dlu=2ε' >=>
                +-right (+-left +-assoc >=> +-assoc >=> diff-step)


              xL-l'' : L l''
              xL-l'' = ∣ l' , l''<l' , ∣ i , eventually-l' ∣ ∣
                where
                eventually-l' : ∀ i3 -> i ≼ i3 -> Real.L (f i3) l'
                eventually-l' i3 i≼i3 = ℝ<->L bound3
                  where
                  bound1 : distance (f i2) (f i3) < ℚ->ℝ ε'
                  bound1 = ε'-close i2 i3 i≼i2 i≼i3
                  bound2 : ℚ->ℝ (- ε') < diff (f i2) (f i3)
                  bound2 =
                    subst2 _<_ (sym ℚ->ℝ-preserves--) (sym diff-anticommute)
                      (minus-flips-< (trans-≤-< (trans-≤-= max-≤-left distance-commute) bound1))
                  bound3 : ℚ->ℝ l' < (f i3)
                  bound3 =
                    subst2 _<_ (sym ℚ->ℝ-preserves-+) diff-step
                      (+-preserves-< l<fi2 bound2)

              xU-u'' : U u''
              xU-u'' = ∣ u' , u'<u'' , ∣ i , eventually-u' ∣ ∣
                where
                eventually-u' : ∀ i3 -> i ≼ i3 -> Real.U (f i3) u'
                eventually-u' i3 i≼i3 = ℝ<->U bound3
                  where
                  bound1 : distance (f i2) (f i3) < ℚ->ℝ ε'
                  bound1 = ε'-close i2 i3 i≼i2 i≼i3
                  bound2 :  diff (f i2) (f i3) < ℚ->ℝ ε'
                  bound2 = trans-≤-< max-≤-left bound1
                  bound3 : f i3 < ℚ->ℝ u'
                  bound3 =
                    subst2 _<_ diff-step (sym ℚ->ℝ-preserves-+)
                      (+-preserves-< fi2<u bound2)

              l''<x : ℚ->ℝ l'' < x
              l''<x = L->ℝ< xL-l''
              x<u'' : x < ℚ->ℝ u''
              x<u'' = U->ℝ< xU-u''

              d1<dl''u : diff x (f i2) < ℚ->ℝ (diff l'' u)
              d1<dl''u =
                trans-<-= (+-preserves-< fi2<u (minus-flips-< l''<x))
                          (sym ℚ->ℝ-preserves-diff)

              d2<dlu'' : diff (f i2) x < ℚ->ℝ (diff l u'')
              d2<dlu'' =
                trans-<-= (+-preserves-< x<u'' (minus-flips-< l<fi2))
                          (sym ℚ->ℝ-preserves-diff)

              d1<ε : diff x (f i2) < ε
              d1<ε = trans-< (trans-<-= d1<dl''u (cong ℚ->ℝ dl''u=4ε')) 4ε'<ε

              d2<ε : diff (f i2) x < ε
              d2<ε = trans-< (trans-<-= d2<dlu'' (cong ℚ->ℝ dlu''=4ε')) 4ε'<ε
