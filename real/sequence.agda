{-# OPTIONS --cubical --safe --exact-split #-}

module real.sequence where

open import base
open import additive-group
open import equality
open import hlevel
open import nat
open import rational
open import rational.difference
open import rational.order
open import rational.minmax
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import real
open import real.order
open import real.rational
open import semiring
open import truncation
open import order
open import order.instances.nat
open import order.instances.rational
open import ordered-semiring
open import ordered-ring
open import sign
open import sign.instances.rational

private
  variable
    ℓ : Level

ℚSequence : Type₀
ℚSequence = Nat -> ℚ

private
  Seq = ℚSequence

Cauchy : Pred Seq ℓ-zero
Cauchy s = (ε : ℚ⁺) -> ∃[ n ∈ Nat ] ((m₁ m₂ : Nat) -> m₁ ≥ n -> m₂ ≥ n ->
                                     (abs-diffℚ (s m₁) (s m₂)) < ⟨ ε ⟩)

OpenEventualUpperBound : Seq -> Pred ℚ ℓ-zero
OpenEventualUpperBound s q = ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> (s m r+ ⟨ ε ⟩) < q)

OpenEventualLowerBound : Seq -> Pred ℚ ℓ-zero
OpenEventualLowerBound s q = ∃[ n ∈ ℕ ] Σ[ ε ∈ ℚ⁺ ] ((m : Nat) -> m ≥ n -> (q r+ ⟨ ε ⟩) < s m)


private
  diff-swap : (a b c : ℚ) -> (a r+ (r- b)) < c -> (a r+ (r- c)) < b
  diff-swap a b c d<c = Pos-diffℚ⁻ (diffℚ c a) b (subst Pos path (Pos-diffℚ (diffℚ b a) c d<c))
    where
    path : c r+ (r- (a r+ (r- b))) == b r+ (r- (a r+ (r- c)))
    path =
      cong (c r+_) (minus-distrib-plus >=>
                    cong ((r- a) r+_) minus-double-inverse >=>
                    (r+-commute (r- a) b)) >=>
      r+-commute c (b r+ (r- a)) >=>
      cong ((b r+ (r- a)) r+_) (sym minus-double-inverse) >=>
      r+-assoc b (r- a) (r- (r- c)) >=>
      cong (b r+_) (sym minus-distrib-plus)

  ε-weaken-< : (q r : ℚ) -> (ε : ℚ⁺) -> (q r+ ⟨ ε ⟩) < r -> q < r
  ε-weaken-< q r ε⁺@(ε , _) lt =
    trans-< {_} {_} {_} {q} {q r+ ε} {r} (r+-Pos->order q ε⁺) lt

  abs-diffℚ-weaken-< : (x y z : ℚ) -> (abs-diffℚ x y) < z -> (diffℚ x y) < z
  abs-diffℚ-weaken-< x y z lt =
    maxℚ-weaken-<₁ (diffℚ x y) (r- (diffℚ x y)) z lt

  midℚ-plus-half-diffℚ : (x y : ℚ) -> (midℚ x y r+ (1/2r r* (diffℚ x y))) == y
  midℚ-plus-half-diffℚ x y =
    sym (*-distrib-+-left {_} {_} {_} {1/2r} {x r+ y} {diffℚ x y}) >=>
    cong (1/2r r*_)
      (cong2 _r+_ (r+-commute x y) (r+-commute y (r- x)) >=>
       r+-assoc y x ((r- x) r+ y) >=>
       cong (y r+_) ((sym (r+-assoc x (r- x) y)) >=>
                     cong (_r+ y) (r+-inverse x) >=>
                     r+-left-zero y)) >=>
    (*-distrib-+-left {_} {_} {_} {1/2r} {y} {y}) >=>
    1/2r-path' y

  midℚ-commute : (x y : ℚ) -> midℚ x y == midℚ y x
  midℚ-commute x y = cong (1/2r r*_) (r+-commute x y)

  midℚ-minus-half-diffℚ : (x y : ℚ) -> (midℚ x y r+ (r- (1/2r r* (diffℚ x y)))) == x
  midℚ-minus-half-diffℚ x y =
    cong2 _r+_ (midℚ-commute x y)
      (sym minus-extract-right >=>
       cong (1/2r r*_) (sym (diffℚ-anticommute y x))) >=>
    midℚ-plus-half-diffℚ y x

  diffℚ-midℚ : (a b : ℚ) -> diffℚ (midℚ a b) b == 1/2r * diffℚ a b
  diffℚ-midℚ a b =
    cong (_r+ (r- (midℚ a b))) (sym (midℚ-plus-half-diffℚ a b)) >=>
    r+-assoc (midℚ a b) (1/2r r* diffℚ a b) (r- (midℚ a b)) >=>
    diffℚ-step (midℚ a b) (1/2r r* diffℚ a b)

  diffℚ-midℚ' : (a b : ℚ) -> diffℚ a (midℚ a b) == 1/2r * diffℚ a b
  diffℚ-midℚ' a b =
    cong ((midℚ a b) r+_) (cong r-_ (sym (midℚ-minus-half-diffℚ a b)) >=>
                           sym (diffℚ-anticommute (midℚ a b) (1/2r r* (diffℚ a b)))) >=>
    diffℚ-step (midℚ a b) (1/2r r* diffℚ a b)

midℚ-<₁ : (a b : ℚ) -> (a < b) -> a < (midℚ a b)
midℚ-<₁ a b a<b =
  Pos-diffℚ⁻ a (midℚ a b)
    (subst Pos (sym (diffℚ-midℚ' a b))
               (r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) (Pos-diffℚ a b a<b)))

midℚ-<₂ : (a b : ℚ) -> (a < b) -> (midℚ a b) < b
midℚ-<₂ a b a<b =
  Pos-diffℚ⁻ (midℚ a b) b
    (subst Pos (sym (diffℚ-midℚ a b))
               (r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) (Pos-diffℚ a b a<b)))


CenteredBall : ℝ -> ℚ -> Type₀
CenteredBall x ε = Σ[ q ∈ ℚ ] (Real.L x (q r+ (r- ε)) × Real.U x (q r+ ε))

OpenBall : ℝ -> ℚ -> Type₀
OpenBall x ε = Σ[ q1 ∈ ℚ ] Σ[ q2 ∈ ℚ ] (Real.L x q1 × Real.U x q2 × diffℚ q1 q2 == ε)


centered-ball->Pos-ε : (x : ℝ) (ε : ℚ) -> CenteredBall x ε -> Pos ε
centered-ball->Pos-ε x e (q , lq , uq) = subst Pos 1/2-2e==e Pos-1/2-2e
  where
  q-e<q+e : (q r+ (r- e)) < (q r+ e)
  q-e<q+e = ℝ-bounds->ℚ< x lq uq

  path : diffℚ (q r+ (r- e)) (q r+ e) == 2r r* e
  path = sym (r+-swap-diffℚ q q (r- e) e) >=>
         cong2 _r+_ (r+-inverse q) (cong (e r+_) minus-double-inverse) >=>
         r+-left-zero (e r+ e) >=>
         2r-path e

  Pos-2e : Pos (2r r* e)
  Pos-2e = subst Pos path (Pos-diffℚ (q r+ (r- e)) (q r+ e) q-e<q+e)

  Pos-1/2-2e : Pos (1/2r r* (2r r* e))
  Pos-1/2-2e = r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) Pos-2e

  1/2-2e==e : (1/2r r* (2r r* e)) == e
  1/2-2e==e = sym (r*-assoc 1/2r 2r e) >=>
              cong (_r* e) (r*-commute 1/2r 2r >=> 2r-1/2r-path) >=>
              r*-left-one e


center-ball :
  (z : ℝ) (q1 q2 : ℚ) -> (Real.L z q1) -> (Real.U z q2) -> CenteredBall z (1/2r r* (diffℚ q1 q2))
center-ball z q1 q2 Lq Uq =
  (midℚ q1 q2) ,
  subst (Real.L z) (sym (midℚ-minus-half-diffℚ q1 q2)) Lq ,
  subst (Real.U z) (sym (midℚ-plus-half-diffℚ q1 q2)) Uq

weaken-centered-ball : (x : ℝ) (ε₁ ε₂ : ℚ) -> (ε₁ < ε₂) -> CenteredBall x ε₁ -> CenteredBall x ε₂
weaken-centered-ball x e1 e2 e1<e2 (q , lq , uq) =
  (q , x.isLowerSet-L _ _ q-e2<q-e1 lq , x.isUpperSet-U _ _ q+e1<q+e2 uq)
  where
  module x = Real x
  q-e2<q-e1 : (q r+ (r- e2)) < (q r+ (r- e1))
  q-e2<q-e1 = +₁-preserves-< (minus-flips-< e1<e2)
  q+e1<q+e2 : (q r+ e1) < (q r+ e2)
  q+e1<q+e2 = +₁-preserves-< e1<e2


strengthen-centered-ball : (x : ℝ) (ε : ℚ) -> CenteredBall x ε -> ∥ CenteredBall x (1/2r r* ε) ∥
strengthen-centered-ball x e b@(q , l-p1 , u-p5) =
  ∥-map2 handle (x.located p2 p3 p2<p3) (x.located p3 p4 p3<p4)
  where
  module x = Real x
  p1 = q r+ (r- e)
  p3 = q
  p5 = q r+ e
  p2 = midℚ p1 p3
  p4 = midℚ p3 p5

  Pos-e : Pos e
  Pos-e = centered-ball->Pos-ε x e b

  diffℚ-p1p3 : diffℚ p1 p3 == e
  diffℚ-p1p3 = cong (p3 r+_) (sym (diffℚ-anticommute q e)) >=> diffℚ-step q e
  diffℚ-p3p5 : diffℚ p3 p5 == e
  diffℚ-p3p5 = r+-assoc q e (r- q) >=> diffℚ-step q e

  p3<p5 : p3 < p5
  p3<p5 = Pos-diffℚ⁻ p3 p5 (subst Pos (sym diffℚ-p3p5) Pos-e)
  p1<p3 : p1 < p3
  p1<p3 = Pos-diffℚ⁻ p1 p3 (subst Pos (sym diffℚ-p1p3) Pos-e)

  p2<p3 : p2 < p3
  p2<p3 = midℚ-<₂ p1 p3 p1<p3
  p3<p4 : p3 < p4
  p3<p4 = midℚ-<₁ p3 p5 p3<p5


  diffℚ-p2p4 : diffℚ p2 p4 == e
  diffℚ-p2p4 =
    sym (diffℚ-trans p2 p3 p4) >=>
    cong2 _+_ (diffℚ-midℚ p1 p3 >=> cong (1/2r r*_) diffℚ-p1p3)
              (diffℚ-midℚ' p3 p5 >=> cong (1/2r r*_) diffℚ-p3p5) >=>
    1/2r-path' e


  handle : (x.L p2 ⊎ x.U p3) -> (x.L p3 ⊎ x.U p4) -> CenteredBall x (1/2r r* e)
  handle (inj-r u-p3) _ =
    subst (CenteredBall x) (cong (1/2r r*_) diffℚ-p1p3) (center-ball x p1 p3 l-p1 u-p3)
  handle (inj-l l-p2) (inj-l l-p3) =
    subst (CenteredBall x) (cong (1/2r r*_) diffℚ-p3p5) (center-ball x p3 p5 l-p3 u-p5)
  handle (inj-l l-p2) (inj-r u-p4) =
    subst (CenteredBall x) (cong (1/2r r*_) diffℚ-p2p4) (center-ball x p2 p4 l-p2 u-p4)


private
  repeated-strengthen-centered-ball :
    (x : ℝ) (ε : ℚ) (n : ℕ) -> CenteredBall x ε -> ∥ CenteredBall x ((1/2r r^ℕ⁰ n) r* ε) ∥
  repeated-strengthen-centered-ball x e zero b = ∣ subst (CenteredBall x) (sym (r*-left-one e)) b ∣
  repeated-strengthen-centered-ball x e (suc n) b =
    ∥-bind handle (repeated-strengthen-centered-ball x e n b)
    where
    handle : CenteredBall x ((1/2r r^ℕ⁰ n) r* e) -> ∥ CenteredBall x ((1/2r r^ℕ⁰ (suc n)) r* e) ∥
    handle b = subst (\z -> ∥ (CenteredBall x z) ∥)
                 (sym (r*-assoc 1/2r (1/2r r^ℕ⁰ n) e))
                 (strengthen-centered-ball x _ b)

  initial-centered-ball : (x : ℝ) -> ∃[ ε ∈ ℚ ] (CenteredBall x ε)
  initial-centered-ball x = ∥-map2 handle x.Inhabited-L x.Inhabited-U
    where
    module x = Real x

    handle : Σ ℚ x.L -> Σ ℚ x.U -> Σ[ ε ∈ ℚ ] (CenteredBall x ε)
    handle (q1 , lq1) (q2 , uq2) = _ , center-ball x q1 q2 lq1 uq2


find-centered-ball : (x : ℝ) -> (ε : ℚ⁺) -> ∥ CenteredBall x ⟨ ε ⟩ ∥
find-centered-ball x e1⁺@(e1 , _) = ∥-bind handle (initial-centered-ball x)
  where
  handle : Σ[ e2 ∈ ℚ ] (CenteredBall x e2) -> ∥ CenteredBall x e1 ∥
  handle (e2 , b) = ∥-bind handle2 (ℚ-archimedian (e2 , centered-ball->Pos-ε x e2 b) e1⁺)
    where
    handle2 : (Σ[ n ∈ Nat ] (((1/2r r^ℕ⁰ n) r* e2) < e1)) -> ∥ CenteredBall x e1 ∥
    handle2 (n , lt) = ∥-map handle3 (repeated-strengthen-centered-ball x e2 n b)
      where
      handle3 : CenteredBall x ((1/2r r^ℕ⁰ n) r* e2) -> CenteredBall x e1
      handle3 b2 = weaken-centered-ball x _ _ lt b2

find-open-ball : (x : ℝ) -> (ε : ℚ⁺) -> ∥ OpenBall x ⟨ ε ⟩ ∥
find-open-ball x e@(e' , pos-e') = ∥-map handle (find-centered-ball x e2)
  where
  e2' = 1/2r r* e'
  e2 : ℚ⁺
  e2 = e2' , r*-preserves-Pos 1/2r _ (Pos-1/ℕ _) pos-e'

  handle : CenteredBall x e2' -> OpenBall x e'
  handle (q , l , u) = q r+ (r- e2') , q r+ e2' , l , u , path
    where
    path : (q r+ e2') r+ (r- (diffℚ e2' q)) == e'
    path =
      cong2 _r+_ (r+-commute q e2') (sym (diffℚ-anticommute q e2')) >=>
      r+-assoc e2' q (diffℚ q e2') >=>
      cong (e2' r+_) (diffℚ-step q e2') >=>
      1/2r-path' e'



-- OpenBallPred : ℚ⁺ -> ℚ -> Pred ℚ ℓ-zero
-- OpenBallPred (ε , _) center q = abs-diffℚ center q < ε
--
-- record OpenBallℚ : Type₀ where
--   constructor open-ballℚ
--   field
--     ε⁺ : ℚ⁺
--     center : ℚ
--
--   ε : ℚ
--   ε = fst ε⁺
--
--   contains : Pred ℚ ℓ-zero
--   contains = OpenBallPred ε⁺ center
--
-- OpenBallℚ-⊆ : Rel OpenBallℚ ℓ-zero
-- OpenBallℚ-⊆ b1 b2 = OpenBallℚ.contains b1 ⊆ OpenBallℚ.contains b2
--
-- OpenBallℚ-RawSeq : Type₀
-- OpenBallℚ-RawSeq = Nat -> OpenBallℚ
--
-- OpenBallℚ-Concentric : Pred OpenBallℚ-RawSeq ℓ-zero
-- OpenBallℚ-Concentric s = (m n : ℕ) -> m ℕ< n -> OpenBallℚ-⊆ (s m) (s n)
-- Seq+ : Seq -> Seq -> Seq
-- Seq+ s₁ s₂ n = s₁ n r+ s₂ n
--
-- Seq- : Seq -> Seq
-- Seq- s n = r- (s n)
--
-- SeqDiff : Seq -> Seq -> Seq
-- SeqDiff s₁ s₂ = Seq+ s₂ (Seq- s₁)
--
-- Increasing : Pred Seq ℓ-zero
-- Increasing s = (m n : Nat) -> (m ℕ< n) -> (s m < s n)
--
-- Decreasing : Pred Seq ℓ-zero
-- Decreasing s = (m n : Nat) -> (m ℕ< n) -> (s m > s n)
--
-- EventualUpperBound : Seq -> Pred ℚ ℓ-zero
-- EventualUpperBound s q = ∃[ n ∈ Nat ] ((m : Nat) -> m ≥ n -> s m < q)
--
-- EventualLowerBound : Seq -> Pred ℚ ℓ-zero
-- EventualLowerBound s q = ∃[ n ∈ Nat ] ((m : Nat) -> m ≥ n -> q < s m)
--
-- UpperBound : Seq -> Pred ℚ ℓ-zero
-- UpperBound s q = (n : Nat) -> s n < q
--
-- LowerBound : Seq -> Pred ℚ ℓ-zero
-- LowerBound s q = (n : Nat) -> q < s n
--
-- BoundedAbove : Pred Seq ℓ-zero
-- BoundedAbove s = ∃ ℚ (UpperBound s)
--
-- BoundedBelow : Pred Seq ℓ-zero
-- BoundedBelow s = ∃ ℚ (LowerBound s)
