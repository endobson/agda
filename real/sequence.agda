{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence where

open import additive-group
open import base
open import equality
open import heyting-field.instances.rational
open import hlevel
open import nat
open import order
open import order.minmax
open import order.instances.nat
open import order.instances.rational
open import order.minmax.instances.rational
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-field
open import ordered-field.archimedean
open import ordered-field.mean
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.archimedean.instances.rational
open import ordered-semiring.instances.rational
open import rational
open import rational.order
open import real
open import real.order
open import real.rational
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import semiring
open import semiring.exponentiation
open import sign
open import sign.instances.rational
open import sum
open import truncation

private
  variable
    ℓ : Level

ℚSequence : Type₀
ℚSequence = Nat -> ℚ

private
  Seq = ℚSequence


private
  ε-weaken-< : (q r : ℚ) -> (ε : ℚ⁺) -> (q r+ ⟨ ε ⟩) < r -> q < r
  ε-weaken-< q r (_ , 0<ε) lt =
    trans-=-< (sym +-right-zero) (trans-< (+₁-preserves-< 0<ε) lt)

  abs-diff-weaken-< : (x y z : ℚ) -> (abs (diff x y)) < z -> (diff x y) < z
  abs-diff-weaken-< x y z lt = trans-≤-< max-≤-left lt

CenteredBall : ℝ -> ℚ -> Type₀
CenteredBall x ε = Σ[ q ∈ ℚ ] (Real.L x (q r+ (r- ε)) × Real.U x (q r+ ε))

OpenBall : ℝ -> ℚ -> Type₀
OpenBall x ε = Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (Real.L x q1 × Real.U x q2 × diff q1 q2 == ε)


centered-ball->0<ε : (x : ℝ) (ε : ℚ) -> CenteredBall x ε -> 0# < ε
centered-ball->0<ε x ε (q , lq , uq) = 0<ε
  where
  q-ε<q+ε : (q + (- ε)) < (q + ε)
  q-ε<q+ε = ℝ-bounds->ℚ< x lq uq

  path : diff (q + (- ε)) (q + ε) == ε + ε
  path = sym +-swap-diff >=>
         +-cong +-inverse (cong (ε +_) minus-double-inverse) >=>
         +-left-zero

  0<2ε : 0# < (ε + ε)
  0<2ε = trans-<-= (diff-0<⁺ q-ε<q+ε) path

  0<ε : 0# < ε
  0<ε = unsquash isProp-< (∥-map (either (\x -> x) (\x -> x)) (+-reflects-0< 0<2ε))


center-ball :
  (z : ℝ) (q1 q2 : ℚ) -> (Real.L z q1) -> (Real.U z q2) -> CenteredBall z (1/2 * (diff q1 q2))
center-ball z q1 q2 Lq Uq =
  (mean q1 q2) ,
  subst (Real.L z) (sym mean-minus-1/2-diff) Lq ,
  subst (Real.U z) (sym mean-+-1/2-diff) Uq


weaken-centered-ball : (x : ℝ) (ε₁ ε₂ : ℚ) -> (ε₁ < ε₂) -> CenteredBall x ε₁ -> CenteredBall x ε₂
weaken-centered-ball x e1 e2 e1<e2 (q , lq , uq) =
  (q , x.isLowerSet-L q-e2<q-e1 lq , x.isUpperSet-U q+e1<q+e2 uq)
  where
  module x = Real x
  q-e2<q-e1 : (q r+ (r- e2)) < (q r+ (r- e1))
  q-e2<q-e1 = +₁-preserves-< (minus-flips-< e1<e2)
  q+e1<q+e2 : (q r+ e1) < (q r+ e2)
  q+e1<q+e2 = +₁-preserves-< e1<e2

strengthen-centered-ball : (x : ℝ) (ε : ℚ) -> CenteredBall x ε -> ∥ CenteredBall x (1/2 * ε) ∥
strengthen-centered-ball x e b@(q , l-p1 , u-p5) =
  ∥-map2 handle (x.located p2 p3 p2<p3) (x.located p3 p4 p3<p4)
  where
  module x = Real x
  p1 = q r+ (r- e)
  p3 = q
  p5 = q r+ e
  p2 = mean p1 p3
  p4 = mean p3 p5

  0<e : 0# < e
  0<e = centered-ball->0<ε x e b

  diff-p1p3 : diff p1 p3 == e
  diff-p1p3 = cong (p3 r+_) (sym diff-anticommute) >=> diff-step
  diff-p3p5 : diff p3 p5 == e
  diff-p3p5 = r+-assoc q e (r- q) >=> diff-step

  p3<p5 : p3 < p5
  p3<p5 = trans-=-< (sym +-right-zero) (+₁-preserves-< 0<e)
  p1<p3 : p1 < p3
  p1<p3 = trans-<-= (+₁-preserves-< (minus-flips-0< 0<e)) +-right-zero

  p2<p3 : p2 < p3
  p2<p3 = mean-<₂ p1<p3
  p3<p4 : p3 < p4
  p3<p4 = mean-<₁ p3<p5


  diff-p2p4 : diff p2 p4 == e
  diff-p2p4 =
    sym diff-trans >=>
    cong2 _+_ (diff-mean >=> cong (1/2 *_) diff-p1p3)
              (diff-mean' >=> cong (1/2 *_) diff-p3p5) >=>
    1/2-path


  handle : (x.L p2 ⊎ x.U p3) -> (x.L p3 ⊎ x.U p4) -> CenteredBall x (1/2 * e)
  handle (inj-r u-p3) _ =
    subst (CenteredBall x) (cong (1/2 *_) diff-p1p3) (center-ball x p1 p3 l-p1 u-p3)
  handle (inj-l l-p2) (inj-l l-p3) =
    subst (CenteredBall x) (cong (1/2 *_) diff-p3p5) (center-ball x p3 p5 l-p3 u-p5)
  handle (inj-l l-p2) (inj-r u-p4) =
    subst (CenteredBall x) (cong (1/2 *_) diff-p2p4) (center-ball x p2 p4 l-p2 u-p4)


private
  repeated-strengthen-centered-ball :
    (x : ℝ) (ε : ℚ) (n : ℕ) -> CenteredBall x ε -> ∥ CenteredBall x ((1/2 ^ℕ n) * ε) ∥
  repeated-strengthen-centered-ball x e zero b = ∣ subst (CenteredBall x) (sym *-left-one) b ∣
  repeated-strengthen-centered-ball x e (suc n) b =
    ∥-bind handle (repeated-strengthen-centered-ball x e n b)
    where
    handle : CenteredBall x ((1/2 ^ℕ n) * e) -> ∥ CenteredBall x ((1/2 ^ℕ (suc n)) * e) ∥
    handle b = subst (\z -> ∥ (CenteredBall x z) ∥)
                 (sym (r*-assoc 1/2 (1/2 ^ℕ n) e))
                 (strengthen-centered-ball x _ b)

  initial-centered-ball : (x : ℝ) -> ∃[ (ε , _) ∈ ℚ⁺ ] (CenteredBall x ε)
  initial-centered-ball x = ∥-map2 handle x.Inhabited-L x.Inhabited-U
    where
    module x = Real x

    handle : Σ ℚ x.L -> Σ ℚ x.U -> Σ[ (ε , _) ∈ ℚ⁺ ] (CenteredBall x ε)
    handle (q1 , lq1) (q2 , uq2) =
      (_ , *-preserves-0< 0<1/2 (diff-0<⁺ q1<q2)) ,
      center-ball x q1 q2 lq1 uq2
      where
      q1<q2 : q1 < q2
      q1<q2 = ℝ-bounds->ℚ< x lq1 uq2

find-centered-ball : (x : ℝ) -> (ε : ℚ⁺) -> ∥ CenteredBall x ⟨ ε ⟩ ∥
find-centered-ball x (e1 , 0<e1) = ∥-bind handle (initial-centered-ball x)
  where
  handle : Σ[ (e2 , _) ∈ ℚ⁺ ] (CenteredBall x e2) -> ∥ CenteredBall x e1 ∥
  handle ((e2 , 0<e2) , b) = ∥-bind handle2 (small-1/2^ℕ (e1/e2 , 0<e1/e2))
    where
    e1/e2 : ℚ
    e1/e2 = e1 * r1/ e2 (\p -> irrefl-path-< (sym p) 0<e2)
    0<e1/e2 : 0# < e1/e2
    0<e1/e2 = *-preserves-0< 0<e1 (r1/-preserves-Pos _ _ 0<e2)

    handle2 : Σ[ n ∈ Nat ] ((1/2 ^ℕ n) < e1/e2) ->
              ∥ CenteredBall x e1 ∥
    handle2 (n , lt) = ∥-map handle3 (repeated-strengthen-centered-ball x e2 n b)
      where
      lt' : ((1/2 ^ℕ n) * e2) < e1
      lt' = trans-<-= (*₂-preserves-< lt 0<e2)
                      (*-assoc >=> *-right (r1/-inverse _ _) >=> *-right-one)

      handle3 : CenteredBall x ((1/2 ^ℕ n) * e2) -> CenteredBall x e1
      handle3 b2 = weaken-centered-ball x _ _ lt' b2

find-open-ball : (x : ℝ) -> (ε : ℚ⁺) -> ∥ OpenBall x ⟨ ε ⟩ ∥
find-open-ball x e@(e' , 0<e') = ∥-map handle (find-centered-ball x e2)
  where
  e2' = 1/2 * e'
  e2 : ℚ⁺
  e2 = e2' , *-preserves-0< 0<1/2 0<e'

  handle : CenteredBall x e2' -> OpenBall x e'
  handle (q , l , u) = q r+ (r- e2') , q r+ e2' , l , u , path
    where
    path : (q r+ e2') r+ (r- (diff e2' q)) == e'
    path =
      cong2 _r+_ (r+-commute q e2') (sym diff-anticommute) >=>
      r+-assoc e2' q (diff q e2') >=>
      cong (e2' r+_) diff-step >=>
      1/2-path
