{-# OPTIONS --cubical --safe --exact-split #-}

module rational.order where

open import abs
open import base
open import equality
open import fraction.sign
open import hlevel
open import isomorphism
open import rational
open import rational.sign
open import relation
open import ring
open import ring.implementations.rational
open import semiring
open import set-quotient
open import sigma
open import sign
open import sign.instances.fraction
open import sign.instances.rational
open import truncation
open import univalence

import int.order
import int
import nat

open int using (Int ; int)
open nat using (ℕ ; Nat⁺; 2⁺ ; _*⁺_)

private
  module i where
    open int.order public
    open int public

private
  numer : Rational' -> Int
  numer = Rational'.numerator
  denom : Rational' -> Int
  denom = Rational'.denominator
  rNonZero : (r : Rational') -> i.NonZero (denom r)
  rNonZero = Rational'.NonZero-denominator


_<'_ : Rational' -> Rational' -> Type₀
q <' r = Pos (r r+' (r-' q))

_>'_ : Rational' -> Rational' -> Type₀
q >' r = r <' q


_≤'_ : Rational' -> Rational' -> Type₀
q ≤' r = NonNeg (r r+' (r-' q))

_≥'_ : Rational' -> Rational' -> Type₀
q ≥' r = r ≤' q

isProp-<' : {q r : Rational'} -> isProp (q <' r)
isProp-<' = isProp-Pos _

isProp-≤' : {q r : Rational'} -> isProp (q ≤' r)
isProp-≤' = isProp-NonNeg _


r~-preserves-NonNeg : {q1 q2 : Rational'} -> NonNeg q1 -> q1 r~ q2 -> NonNeg q2
r~-preserves-NonNeg {q1} {q2} nn-q1 r = handle (decide-sign q1)
  where
  handle : Σ[ s ∈ Sign ] isSign s q1 -> NonNeg q2
  handle (pos-sign  , p-q1) = Pos->NonNeg (r~-preserves-sign p-q1 r)
  handle (zero-sign , z-q1) = Zero->NonNeg (r~-preserves-sign z-q1 r)
  handle (neg-sign  , n-q1)  = bot-elim (NonNeg->¬Neg nn-q1 n-q1)


r~-preserves-<₁ : {q1 q2 r : Rational'} -> q1 <' r -> q1 r~ q2 -> q2 <' r
r~-preserves-<₁ {q1} {q2} {r} q1<r q1~q2 =
  r~-preserves-sign q1<r (r+'-preserves-r~₂ r (r-' q1) (r-' q2) (r-'-preserves-r~ q1 q2 q1~q2))

r~-preserves-<₂ : {q r1 r2 : Rational'} -> q <' r1 -> r1 r~ r2 -> q <' r2
r~-preserves-<₂ {q} {r1} {r2} q<r1 r1~r2 =
  r~-preserves-sign q<r1 (r+'-preserves-r~₁ (r-' q) r1 r2 r1~r2)

r1/'-preserves-Pos : (q : Rational') -> (i : ℚInv' q) -> Pos q -> Pos (r1/' q i)
r1/'-preserves-Pos q i p = is-signℚ' (subst i.Pos i.*-commute (isSignℚ'.v p))

r1/'-preserves-Neg : (q : Rational') -> (i : ℚInv' q) -> Neg q -> Neg (r1/' q i)
r1/'-preserves-Neg q i p = is-signℚ' (subst i.Neg i.*-commute (isSignℚ'.v p))


r-'-flips-sign : (q : Rational') (s : Sign) -> (isSign s q) -> (isSign (s⁻¹ s) (r-' q))
r-'-flips-sign q s qs =
  is-signℚ'
    (subst (i.isSign (s⁻¹ s)) (sym i.minus-extract-left)
           (i.minus-isSign {numer q i.* denom q} {s} (isSignℚ'.v qs)))

Zero-0r' : Zero 0r'
Zero-0r' = is-signℚ' (subst i.Zero (sym i.*-left-zero) tt)

Zero-r~ : (q : Rational') -> Zero q -> q r~ 0r'
Zero-r~ q zq = (cong (i._* (denom 0r')) path >=> i.*-left-zero >=> sym i.*-left-zero)
  where
  path : (numer q) == (.int 0)
  path = i.*-left-zero-eq (rNonZero q) (i.Zero-path ((numer q) i.* (denom q)) (isSignℚ'.v zq))



irrefl-<' : Irreflexive _<'_
irrefl-<' {a} a<a = (i.NonPos->¬Pos (i.Zero->NonPos (isSignℚ'.v b-zero)) (isSignℚ'.v b-pos))
  where
  b = a r+' (r-' a)

  b-pos : Pos b
  b-pos = a<a
  b-zero : Zero b
  b-zero = r~-preserves-sign {0r'} {b} {zero-sign} Zero-0r' (sym (r+'-inverse a))

trans-<' : Transitive _<'_
trans-<' {a} {b} {c} a<b b<c = a<c
  where
  d = b r+' (r-' a)
  e = c r+' (r-' b)
  f = c r+' (r-' a)

  step1 : (e r+' d) r~' (c r+' ((r-' b) r+' d))
  step1 = r~->r~' r+'-assoc

  step2 : (c r+' ((r-' b) r+' d)) r~' (c r+' (((r-' b) r+' b) r+' (r-' a)))
  step2 = r~->r~' (r+'-preserves-r~₂ c _ _ (sym r+'-assoc))

  step3 : ((r-' b) r+' b) r~ 0r'
  step3 = (subst (_r~ 0r') (r+'-commute b (r-' b)) (r+'-inverse b))

  step4 : (c r+' (((r-' b) r+' b) r+' (r-' a))) r~' (c r+' (0r' r+' (r-' a)))
  step4 = r~->r~' (r+'-preserves-r~₂ _ _ _ (r+'-preserves-r~₁ _ _ _ step3))

  step5 : (c r+' (0r' r+' (r-' a))) r~' (c r+' (r-' a))
  step5 = r~->r~' (path->r~ (cong (c r+'_) (r+'-left-zero (r-' a))))

  combined-steps : (e r+' d) r~' f
  combined-steps = trans-r~' (trans-r~' (trans-r~' step1 step2) step4) step5

  f-path : (e r+' d) r~ f
  f-path = r~'->r~ combined-steps

  a<c : a <' c
  a<c = r~-preserves-sign {e r+' d} {f} {s = pos-sign} (r+'-preserves-Pos b<c a<b) f-path


decide-<' : Decidable2 _<'_
decide-<' x y = handle (i.int->sign z') (i.isSign-self z')
  where
  z = y r+' (r-' x)
  z' = numer z i.* denom z
  handle : (s : Sign) -> (i.isSign s z') -> Dec (x <' y)
  handle pos-sign pz = yes (is-signℚ' pz)
  handle zero-sign zz = no (\ pz -> i.NonPos->¬Pos (i.Zero->NonPos zz) (isSignℚ'.v pz))
  handle neg-sign nz = no (\ pz -> i.NonPos->¬Pos (i.Neg->NonPos nz) (isSignℚ'.v pz))


diffℚ : ℚ -> ℚ -> ℚ
diffℚ x y = (y r+ (r- x))

abstract
  diffℚ-anticommute : (x y : ℚ) -> diffℚ x y == r- (diffℚ y x)
  diffℚ-anticommute x y = sym (
    RationalRing.minus-distrib-plus {x} {r- y} >=>
    cong ((r- x) r+_) (RationalRing.minus-double-inverse {y}) >=>
    r+-commute (r- x) y)

  r+-swap-diffℚ : (a b c d : Rational) -> ((diffℚ a b) r+ (diffℚ c d)) == (diffℚ (a r+ c) (b r+ d))
  r+-swap-diffℚ a b c d =
    r+-assoc b (r- a) (diffℚ c d) >=>
    cong (b r+_) (sym (r+-assoc (r- a) d (r- c)) >=>
                  cong (_r+ (r- c)) (r+-commute (r- a) d) >=>
                  r+-assoc d (r- a) (r- c) >=>
                  cong (d r+_) (sym (RationalRing.minus-distrib-plus {a} {c}))) >=>
    sym (r+-assoc b d (r- (a r+ c)))

  r*-distrib-diffℚ : (a b c : Rational) -> a r* (diffℚ b c) == diffℚ (a r* b) (a r* c)
  r*-distrib-diffℚ a b c =
    RationalSemiring.*-distrib-+-left {a} {c} {r- b} >=>
    cong ((a r* c) r+_) (r*-minus-extract-right a b)


  diffℚ-trans : (x y z : ℚ) -> diffℚ x y r+ diffℚ y z == (diffℚ x z)
  diffℚ-trans x y z =
    r+-commute (diffℚ x y) (diffℚ y z) >=>
    r+-assoc z (r- y) (diffℚ x y) >=>
    cong (z r+_) (sym (r+-assoc (r- y) y (r- x)) >=>
                  cong (_r+ (r- x)) (r+-commute (r- y) y >=> r+-inverse y) >=>
                  r+-left-zero (r- x))

  diffℚ-step : (x y : ℚ) -> x + diffℚ x y == y
  diffℚ-step x y =
    sym (r+-assoc x y (r- x)) >=>
    cong (_r+ (r- x)) (r+-commute x y) >=>
    (r+-assoc y x (r- x)) >=>
    cong (y r+_) (r+-inverse x) >=>
    r+-right-zero y



private
  Dense : {ℓ ℓA : Level} {A : Type ℓA} -> Rel A ℓ -> Type (ℓ-max ℓA ℓ)
  Dense {A = A} _<_ = {x y : A} -> x < y -> Σ[ z ∈ A ] (x < z × z < y)



Posℚ : Rational -> Type₀
Posℚ = isSign pos-sign
Negℚ : Rational -> Type₀
Negℚ = isSign neg-sign
Zeroℚ : Rational -> Type₀
Zeroℚ = isSign zero-sign

isProp-Posℚ : {r : Rational} -> isProp (Posℚ r)
isProp-Posℚ {r} = isProp-isSign pos-sign r

ℚ⁺ : Type₀
ℚ⁺ = Σ ℚ Posℚ
ℚ⁻ : Type₀
ℚ⁻ = Σ ℚ Negℚ

ℚ⁰⁺ : Type₀
ℚ⁰⁺ = Σ ℚ NonNeg
ℚ⁰⁻ : Type₀
ℚ⁰⁻ = Σ ℚ NonPos

Zero-0r : Zero 0r
Zero-0r = is-signℚ Zero-0r'

Zero-path : (q : Rational) -> Zeroℚ q -> q == 0r
Zero-path =
  RationalElim.elimProp
    (\_ -> isPropΠ (\_ -> isSetRational _ _))
    (\q zq -> eq/ _ _ (Zero-r~ q (isSignℚ.v zq)))

Pos->Inv : {q : ℚ} -> Pos q -> ℚInv q
Pos->Inv {q} p z = NonZero->¬Zero (inj-l p) (subst Zero (sym z) Zero-0r)

Neg->Inv : {q : ℚ} -> Neg q -> ℚInv q
Neg->Inv {q} p z = NonZero->¬Zero (inj-r p) (subst Zero (sym z) Zero-0r)

abstract
  r+-preserves-Pos : (q1 q2 : Rational) -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r+ q2)
  r+-preserves-Pos =
    RationalElim.elimProp2
      {C2 = \q1 q2 -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r+ q2)}
      (\q1 q2 -> isPropΠ2 (\ _ _ -> isProp-Pos (q1 r+ q2)))
      (\q1 q2 p1 p2 ->
        subst Posℚ (sym r+-eval)
              (is-signℚ (r+'-preserves-Pos (isSignℚ.v p1) (isSignℚ.v p2))))

  r+-preserves-NonNeg : {q1 q2 : ℚ} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r+ q2)
  r+-preserves-NonNeg {q1} {q2} (inj-r z1) nn-q2          =
    (subst NonNeg (sym (cong (_r+ q2) (Zero-path _ z1) >=> r+-left-zero q2)) nn-q2)
  r+-preserves-NonNeg {q1} {q2} (inj-l p1) (inj-r z2) =
    inj-l (subst Pos (sym (cong (q1 r+_) (Zero-path _ z2) >=> r+-right-zero q1)) p1)
  r+-preserves-NonNeg {q1} {q2} (inj-l p1) (inj-l p2) = inj-l (r+-preserves-Pos _ _ p1 p2)

  r*-preserves-Pos : (q1 q2 : Rational) -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r* q2)
  r*-preserves-Pos =
    RationalElim.elimProp2
      {C2 = \q1 q2 -> Posℚ q1 -> Posℚ q2 -> Posℚ (q1 r* q2)}
      (\q1 q2 -> isPropΠ2 (\ _ _ -> isProp-Pos (q1 r* q2)))
      (\q1 q2 p1 p2 ->
          subst Posℚ (sym r*-eval) (is-signℚ (r*'-preserves-Pos (isSignℚ.v p1) (isSignℚ.v p2))))

  r*₁-preserves-Zero : (q1 : ℚ) {q2 : Rational} -> Zero q2 -> Zero (q1 r* q2)
  r*₁-preserves-Zero q1 {q2} zq2 = subst Zero (sym q1q2==0) Zero-0r
    where
    q2==0 : q2 == 0r
    q2==0 = Zero-path q2 zq2
    q1q2==0 : q1 r* q2 == 0r
    q1q2==0 = cong (q1 r*_) q2==0 >=> r*-right-zero q1

  r*₂-preserves-Zero : {q1 : ℚ} -> Zero q1 -> (q2 : Rational) -> Zero (q1 r* q2)
  r*₂-preserves-Zero {q1} zq1 q2 = subst Zero (r*-commute q2 q1) (r*₁-preserves-Zero q2 zq1)

  r*-preserves-NonNeg : {q1 q2 : ℚ} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r* q2)
  r*-preserves-NonNeg {q1} {q2} (inj-r z1) _          = inj-r (r*₂-preserves-Zero z1 q2)
  r*-preserves-NonNeg {q1} {q2} (inj-l p1) (inj-r z2) = inj-r (r*₁-preserves-Zero q1 z2)
  r*-preserves-NonNeg {q1} {q2} (inj-l p1) (inj-l p2) = inj-l (r*-preserves-Pos _ _ p1 p2)

  r--flips-sign : (q : Rational) (s : Sign) -> (isSignℚ s q) -> (isSignℚ (s⁻¹ s) (r- q))
  r--flips-sign =
    RationalElim.elimProp
      (\q -> isPropΠ2 (\ s _ -> isProp-isSign (s⁻¹ s) (r- q)))
      (\q s qs -> is-signℚ (r-'-flips-sign q s (isSignℚ.v qs)))

  r+-preserves-Neg : (q1 q2 : ℚ) -> Neg q1 -> Neg q2 -> Neg (q1 r+ q2)
  r+-preserves-Neg q1 q2 n1 n2 =
    subst Neg p (r--flips-sign _ _ (r+-preserves-Pos _ _ (r--flips-sign _ _ n1) (r--flips-sign _ _ n2)))
    where
    p : (r- ((r- q1) r+ (r- q2))) == (q1 r+ q2)
    p = cong r-_ (sym (RationalRing.minus-distrib-plus {q1} {q2})) >=> RationalRing.minus-double-inverse


  r+-preserves-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonPos (q1 r+ q2)
  r+-preserves-NonPos {q1} {q2} (inj-r z1) np-q2          =
    (subst NonPos (sym (cong (_r+ q2) (Zero-path _ z1) >=> r+-left-zero q2)) np-q2)
  r+-preserves-NonPos {q1} {q2} (inj-l n1) (inj-r z2) =
    inj-l (subst Neg (sym (cong (q1 r+_) (Zero-path _ z2) >=> r+-right-zero q1)) n1)
  r+-preserves-NonPos {q1} {q2} (inj-l n1) (inj-l n2) = inj-l (r+-preserves-Neg _ _ n1 n2)



  r1/ᵉ-preserves-Pos : (q : Rational) -> (i : ℚInv q) -> Pos q -> Pos (r1/ᵉ q i)
  r1/ᵉ-preserves-Pos =
    RationalElim.elimProp
      (\q -> isPropΠ2 (\ i _ -> isProp-Pos (r1/ᵉ q i)))
      (\q i p -> is-signℚ (r1/'-preserves-Pos q (ℚInv->ℚInv' q i) (isSignℚ.v p)))

  r1/ᵉ-preserves-Neg : (q : Rational) -> (i : ℚInv q) -> Neg q -> Neg (r1/ᵉ q i)
  r1/ᵉ-preserves-Neg =
    RationalElim.elimProp
      (\q -> isPropΠ2 (\ i _ -> isProp-Neg (r1/ᵉ q i)))
      (\q i p -> is-signℚ (r1/'-preserves-Neg q (ℚInv->ℚInv' q i) (isSignℚ.v p)))


  r1/-preserves-Pos : (q : Rational) -> (i : ℚInv q) -> Pos q -> Pos (r1/ q i)
  r1/-preserves-Pos q i p = subst Pos (sym r1/-eval) (r1/ᵉ-preserves-Pos q i p)

  r1/-preserves-Neg : (q : Rational) -> (i : ℚInv q) -> Neg q -> Neg (r1/ q i)
  r1/-preserves-Neg q i n = subst Neg (sym r1/-eval) (r1/ᵉ-preserves-Neg q i n)

  r*₁-preserves-sign : (q : ℚ⁺) (r : Rational) {s : Sign} -> isSignℚ s r ->
                       isSignℚ s (⟨ q ⟩ r* r)
  r*₁-preserves-sign (q , pos-q) r {zero-sign} zero-r =
    subst Zero (sym qr==0) Zero-0r
    where
    r==0 : r == 0r
    r==0 = Zero-path r zero-r
    qr==0 : q r* r == 0r
    qr==0 = cong (q r*_) r==0 >=> r*-right-zero q
  r*₁-preserves-sign (q , pos-q) r {pos-sign} pos-r = r*-preserves-Pos q r pos-q pos-r
  r*₁-preserves-sign (q , pos-q) r {neg-sign} neg-r =
    subst Neg RationalRing.minus-double-inverse neg-mmqr
    where
    pos-mr : Pos (r- r)
    pos-mr = r--flips-sign _ _ neg-r
    pos-qmr : Pos (q r* (r- r))
    pos-qmr = r*-preserves-Pos _ _ pos-q pos-mr
    pos-mqr : Pos (r- (q r* r))
    pos-mqr = subst Pos (r*-minus-extract-right q r) pos-qmr
    neg-mmqr : Neg (r- (r- (q r* r)))
    neg-mmqr = r--flips-sign _ _ pos-mqr


  r*₁-flips-sign : (q : ℚ⁻) (r : Rational) {s : Sign} -> isSignℚ s r ->
                    isSignℚ (s⁻¹ s) (⟨ q ⟩ r* r)
  r*₁-flips-sign (q , neg-q) r {s} r-sign =
    subst (isSignℚ (s⁻¹ s)) RationalRing.minus-double-inverse s-mmqr
    where
    mq = r- q
    s-mqr1 = r*₁-preserves-sign (mq , r--flips-sign _ _ neg-q) r r-sign
    s-mqr2 = subst (isSignℚ s) (r*-minus-extract-left q r) s-mqr1
    s-mmqr = r--flips-sign _ _ s-mqr2


  r*-NonNeg-NonNeg : {q1 q2 : ℚ} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r* q2)
  r*-NonNeg-NonNeg = r*-preserves-NonNeg

  r*-NonNeg-NonPos : {q1 q2 : ℚ} -> NonNeg q1 -> NonPos q2 -> NonPos (q1 r* q2)
  r*-NonNeg-NonPos (inj-r z1) _          = inj-r (r*₂-preserves-Zero z1 _)
  r*-NonNeg-NonPos (inj-l p1) (inj-r z2) = inj-r (r*₁-preserves-Zero _ z2)
  r*-NonNeg-NonPos (inj-l p1) (inj-l n2) = inj-l (r*₁-preserves-sign (_ , p1) _ n2)

  r*-NonPos-NonNeg : {q1 q2 : ℚ} -> NonPos q1 -> NonNeg q2 -> NonPos (q1 r* q2)
  r*-NonPos-NonNeg np1 nn2 = subst NonPos (r*-commute _ _) (r*-NonNeg-NonPos nn2 np1)

  r*-NonPos-NonPos : {q1 q2 : ℚ} -> NonPos q1 -> NonPos q2 -> NonNeg (q1 r* q2)
  r*-NonPos-NonPos (inj-r z1) _          = inj-r (r*₂-preserves-Zero z1 _)
  r*-NonPos-NonPos (inj-l p1) (inj-r z2) = inj-r (r*₁-preserves-Zero _ z2)
  r*-NonPos-NonPos (inj-l n1) (inj-l n2) = inj-l (r*₁-flips-sign (_ , n1) _ n2)

  r*-ZeroFactor : {q1 q2 : ℚ} -> Zero (q1 r* q2) -> Zero q1 ⊎ Zero q2
  r*-ZeroFactor {q1} {q2} zp = handle _ _ (snd (decide-sign q1)) (snd (decide-sign q2))
    where
    handle : (s1 s2 : Sign) -> isSignℚ s1 q1 -> isSignℚ s2 q2 -> Zero q1 ⊎ Zero q2
    handle zero-sign _         z1 _ = inj-l z1
    handle pos-sign  zero-sign p1 z2 = inj-r z2
    handle neg-sign  zero-sign n1 z2 = inj-r z2
    handle pos-sign  pos-sign  p1 p2 =
      bot-elim (NonZero->¬Zero (inj-l (r*₁-preserves-sign (_ , p1) _ p2)) zp)
    handle pos-sign  neg-sign  p1 n2 =
      bot-elim (NonZero->¬Zero (inj-r (r*₁-preserves-sign (_ , p1) _ n2)) zp)
    handle neg-sign  pos-sign  n1 p2 =
      bot-elim (NonZero->¬Zero (inj-r (r*₁-flips-sign (_ , n1) _ p2)) zp)
    handle neg-sign  neg-sign  n1 n2 =
      bot-elim (NonZero->¬Zero (inj-l (r*₁-flips-sign (_ , n1) _ n2)) zp)


  r--NonNeg : {q1 : ℚ} -> NonNeg q1 -> NonPos (r- q1)
  r--NonNeg (inj-l s) = (inj-l (r--flips-sign _ _ s))
  r--NonNeg (inj-r s) = (inj-r (r--flips-sign _ _ s))

  r--NonPos : {q1 : ℚ} -> NonPos q1 -> NonNeg (r- q1)
  r--NonPos (inj-l s) = (inj-l (r--flips-sign _ _ s))
  r--NonPos (inj-r s) = (inj-r (r--flips-sign _ _ s))


_<_ : Rational -> Rational -> Type₀
q < r = Posℚ (r r+ (r- q))

_>_ : Rational -> Rational -> Type₀
q > r = r < q

_ℚ≤_ : ℚ -> ℚ -> Type₀
x ℚ≤ y = NonNeg (diffℚ x y)

isProp-< : {a b : Rational} -> isProp (a < b)
isProp-< {a} {b} = isProp-Pos (b r+ (r- a))

irrefl-< : Irreflexive _<_
irrefl-< {a} a<a =
  RationalElim.elimProp
    {C = (\r -> r < r -> Bot)}
    (\_ -> isPropΠ (\_ -> isPropBot))
    (\r s -> (irrefl-<' {r} (isSignℚ.v (subst Posℚ r+-eval s)))) a a<a

abstract
  trans-< : Transitive _<_
  trans-< {a} {b} {c} a<b b<c =
    RationalElim.elimProp3
      {C3 = (\a b c -> a < b -> b < c -> a < c)}
      (\a _ c -> isPropΠ2 (\_ _ -> isProp-< {a} {c}))
      (\a b c a<b b<c -> subst Posℚ (sym r+-eval)
                               (is-signℚ (trans-<' (isSignℚ.v (subst Posℚ r+-eval a<b))
                                         (isSignℚ.v (subst Posℚ r+-eval b<c)))))
      a b c a<b b<c

asym-< : Asymmetric _<_
asym-< {a} {b} lt1 lt2 = irrefl-< {a} (trans-< {a} {b} {a} lt1 lt2)

refl-ℚ≤ : Reflexive _ℚ≤_
refl-ℚ≤ {x} = inj-r (subst Zero (sym (r+-inverse x)) Zero-0r)

Pos-1/ℕ : (n : Nat⁺) -> Posℚ (1/ℕ n)
Pos-1/ℕ (n@(suc _) , _) = is-signℚ (is-signℚ' (i.*-Pos-Pos tt tt))

Pos-0< : (q : Rational) -> Posℚ q -> 0r < q
Pos-0< q = subst Posℚ p
  where
  p : q == q r+ (r- 0r)
  p = sym (r+-right-zero q)

Neg-<0 : (q : Rational) -> Negℚ q -> q < 0r
Neg-<0 q n = subst Posℚ (sym (r+-left-zero (r- q))) (r--flips-sign q _ n)

NonNeg-0≤ : (q : Rational) -> NonNeg q -> 0r ℚ≤ q
NonNeg-0≤ q nn-q = subst NonNeg (sym (r+-right-zero q)) nn-q

0<-Pos : (q : Rational) -> 0r < q -> Pos q
0<-Pos q 0<q = subst Pos (r+-right-zero q) 0<q

<0-Neg : (q : Rational) -> q < 0r -> Neg q
<0-Neg q q<0 = (subst Negℚ (sym (diffℚ-anticommute 0r q) >=> r+-right-zero q)
                           (r--flips-sign _ _ q<0))

0≤-NonNeg : (q : Rational) -> 0r ℚ≤ q -> NonNeg q
0≤-NonNeg q 0<q = subst NonNeg (r+-right-zero q) 0<q

≤0-NonPos : (q : Rational) -> q ℚ≤ 0r -> NonPos q
≤0-NonPos q (inj-l q<0) = inj-l (subst Negℚ (sym (diffℚ-anticommute 0r q) >=> r+-right-zero q)
                                            (r--flips-sign _ _ q<0))
≤0-NonPos q (inj-r q=0) = inj-r (subst Zeroℚ (sym (diffℚ-anticommute 0r q) >=> r+-right-zero q)
                                             (r--flips-sign _ _ q=0))



NonPos≤NonNeg : {q r : Rational} -> NonPos q -> NonNeg r -> q ℚ≤ r
NonPos≤NonNeg np-q nn-r = r+-preserves-NonNeg nn-r (r--NonPos np-q)

Pos-1r : Posℚ 1r
Pos-1r = Pos-1/ℕ nat.1⁺


dense-< : Dense _<_
dense-< {x} {y} lt = z , (pos-d3 , pos-d4)
  where
  d1 = y r+ (r- x)
  d2 = d1 r* 1/2r
  z = x r+ d2
  z' = y r+ (r- d2)
  d3 = z r+ (r- x)
  d4 = y r+ (r- z)

  d2-path : d2 r+ d2 == d1
  d2-path = 1/2r-path d1

  z-path : z == z'
  z-path =
    begin
      x r+ d2
    ==< sym (r+-right-zero _) >
      (x r+ d2) r+ 0r
    ==< cong ((x r+ d2) r+_) (sym (r+-inverse d2)) >
      (x r+ d2) r+ (d2 r+ (r- d2))
    ==< r+-assoc x d2 (d2 r+ (r- d2)) >=>
        cong (x r+_) (sym (r+-assoc d2 d2 (r- d2)) >=> (cong (_r+ (r- d2)) d2-path)) >
      x r+ (d1 r+ (r- d2))
    ==< sym (r+-assoc x d1 (r- d2)) >
      (x r+ (y r+ (r- x))) r+ (r- d2)
    ==< cong (_r+ (r- d2)) (sym (r+-assoc x y (r- x)) >=>
                            cong (_r+ (r- x)) (r+-commute x y) >=>
                            r+-assoc y x (r- x) >=>
                            cong (y r+_) (r+-inverse x) >=>
                            r+-right-zero y) >
      y r+ (r- d2)
    end

  pos-d1 : Posℚ d1
  pos-d1 = lt

  pos-d2 : Posℚ d2
  pos-d2 = r*-preserves-Pos d1 1/2r pos-d1 (Pos-1/ℕ (2 , tt))

  d3-path : d2 == d3
  d3-path =
    sym (cong (_r+ (r- x)) (r+-commute x d2) >=>
         r+-assoc d2 x (r- x) >=>
         cong (d2 r+_) (r+-inverse x) >=>
         r+-right-zero d2)
  pos-d3 : Posℚ d3
  pos-d3 = subst Posℚ d3-path pos-d2

  d4-path : d2 == d4
  d4-path =
    sym (cong (\z -> y r+ (r- z)) z-path >=>
         cong (y r+_) (RationalRing.minus-distrib-plus {y} {r- d2}) >=>
         sym (r+-assoc y (r- y) (r- (r- d2))) >=>
         cong2 _r+_ (r+-inverse y) (RationalRing.minus-double-inverse {d2}) >=>
         r+-left-zero d2)
  pos-d4 : Posℚ d4
  pos-d4 = subst Posℚ d4-path pos-d2


decide-< : Decidable2 _<_
decide-< =
  RationalElim.elimProp2
    (\a b -> isPropDec (isProp-< {a} {b}))
    (\a b -> subst (\x -> Dec (Posℚ x)) (sym r+-eval) (handle (decide-<' a b)))
  where
  handle : {q : Rational'} -> Dec (Pos q) -> Dec (Pos [ q ])
  handle (yes pq) = yes (is-signℚ pq)
  handle (no ¬pq) = no (\v -> ¬pq (isSignℚ.v v))

private
  zero-diff->path : (x y : Rational) -> Zeroℚ (y r+ (r- x)) -> x == y
  zero-diff->path x y zyx = sym p
    where
    p : y == x
    p = sym (r+-right-zero y) >=>
        (cong (y r+_) (sym (r+-inverse x) >=> r+-commute x (r- x))) >=>
        sym (r+-assoc y (r- x) x) >=>
        cong (_r+ x) (Zero-path (y r+ (r- x)) zyx) >=>
        r+-left-zero x

connected-< : Connected _<_
connected-< {x} {y} x≮y y≮x =
  handle (decide-sign z)
  where
  z = (y r+ (r- x))
  z2 = (x r+ (r- y))
  p : (r- z) == z2
  p =
    (RationalRing.minus-distrib-plus {y} {r- x}) >=>
    cong ((r- y) r+_) (RationalRing.minus-double-inverse {x}) >=>
    r+-commute (r- y) x

  handle : Σ[ s ∈ Sign ] (isSignℚ s z) -> x == y
  handle (pos-sign  , pz) = bot-elim (x≮y pz)
  handle (zero-sign , zz) = zero-diff->path x y zz
  handle (neg-sign  , nz) = bot-elim (y≮x (subst Posℚ p (r--flips-sign z neg-sign nz)))

trichotomous-< : Trichotomous _<_
trichotomous-< x y = handle (decide-< x y) (decide-< y x)
  where
  handle : Dec (x < y) -> Dec (y < x) -> Tri (x < y) (x == y) (y < x)
  handle (yes x<y) (yes y<x) = bot-elim (asym-< {x} {y} x<y y<x)
  handle (yes x<y) (no y≮x)  = tri< x<y (\p -> y≮x (transport (\i -> (p i) < (p (~ i))) x<y)) y≮x
  handle (no x≮y)  (yes y<x) = tri> x≮y (\p -> x≮y (transport (\i -> (p (~ i)) < (p i)) y<x)) y<x
  handle (no x≮y)  (no y≮x)  = tri= x≮y (connected-< x≮y y≮x) y≮x

comparison-< : Comparison _<_
comparison-< x y z x<z = handle (trichotomous-< y w)
  where
  Σw = dense-< {x} {z} x<z
  w = fst Σw
  x<w = proj₁ (snd Σw)
  w<z = proj₂ (snd Σw)
  handle : Tri (y < w) (y == w) (y > w) -> ∥ (x < y) ⊎ (y < z) ∥
  handle (tri< y<w _ _)  = ∣ inj-r (trans-< {y} {w} {z} y<w w<z) ∣
  handle (tri= _ y==w _) = ∣ inj-l (subst (x <_) (sym y==w) x<w) ∣
  handle (tri> _ _ w<y)  = ∣ inj-l (trans-< {x} {w} {y} x<w w<y) ∣



r+₁-preserves-order : (a b c : Rational) -> b < c -> (a r+ b) < (a r+ c)
r+₁-preserves-order a b c = subst Posℚ (sym path)
  where
  path : (a r+ c) r+ (r- (a r+ b)) == c r+ (r- b)
  path = cong2 _r+_ (r+-commute a c) (RationalRing.minus-distrib-plus {a} {b}) >=>
         r+-assoc c a ((r- a) r+ (r- b)) >=>
         cong (c r+_) (sym (r+-assoc a (r- a) (r- b)) >=>
                       (cong (_r+ (r- b)) (r+-inverse a)) >=>
                       (r+-left-zero (r- b)))

r+₂-preserves-order : (a b c : Rational) -> a < b -> (a r+ c) < (b r+ c)
r+₂-preserves-order a b c lt =
  subst2 _<_ (r+-commute c a) (r+-commute c b) (r+₁-preserves-order c a b lt)


r+₁-preserves-≤ : (a b c : Rational) -> b ℚ≤ c -> (a r+ b) ℚ≤ (a r+ c)
r+₁-preserves-≤ a b c = subst NonNeg (sym path)
  where
  path : (a r+ c) r+ (r- (a r+ b)) == c r+ (r- b)
  path = cong2 _r+_ (r+-commute a c) (RationalRing.minus-distrib-plus {a} {b}) >=>
         r+-assoc c a ((r- a) r+ (r- b)) >=>
         cong (c r+_) (sym (r+-assoc a (r- a) (r- b)) >=>
                       (cong (_r+ (r- b)) (r+-inverse a)) >=>
                       (r+-left-zero (r- b)))

r+₂-preserves-≤ : (a b c : Rational) -> a ℚ≤ b -> (a r+ c) ℚ≤ (b r+ c)
r+₂-preserves-≤ a b c lt =
  subst2 _ℚ≤_ (r+-commute c a) (r+-commute c b) (r+₁-preserves-≤ c a b lt)


r--flips-order : (b c : Rational) -> b < c -> (r- b) > (r- c)
r--flips-order b c = subst Posℚ p
  where
  p : c r+ (r- b) == (r- b) r+ (r- (r- c))
  p = r+-commute c (r- b) >=> cong ((r- b) r+_) (sym (RationalRing.minus-double-inverse {c}))

r--flips-≤ : (b c : Rational) -> b ℚ≤ c -> (r- c) ℚ≤ (r- b)
r--flips-≤ b c = subst NonNeg p
  where
  p : c r+ (r- b) == (r- b) r+ (r- (r- c))
  p = r+-commute c (r- b) >=> cong ((r- b) r+_) (sym (RationalRing.minus-double-inverse {c}))


r+-Pos->order : (a : ℚ) (b : Σ ℚ Posℚ) -> a < (a r+ ⟨ b ⟩)
r+-Pos->order a (b , pos-b) = subst Posℚ (sym path) pos-b
  where
  path : (a r+ b) r+ (r- a) == b
  path = (cong (_r+ (r- a)) (r+-commute a b))
         >=> r+-assoc b a (r- a)
         >=> (cong (b r+_) (r+-inverse a))
         >=> r+-right-zero b

r+-Neg->order : (a : ℚ) (b : Σ ℚ Negℚ) -> a > (a r+ ⟨ b ⟩)
r+-Neg->order a (b , neg-b) = subst ((a r+ b) <_) path lt
  where
  lt : (a r+ b) < ((a r+ b) r+ (r- b))
  lt = r+-Pos->order (a r+ b) (r- b , r--flips-sign b neg-sign neg-b)
  path : ((a r+ b) r+ (r- b)) == a
  path = r+-assoc a b (r- b) >=> cong (a r+_) (r+-inverse b) >=> r+-right-zero a

r*₁-preserves-order : (a : ℚ⁺) (b c : Rational) -> b < c -> (⟨ a ⟩ r* b) < (⟨ a ⟩ r* c)
r*₁-preserves-order (a , pos-a) b c b<c = subst Posℚ path pos-diff
  where
  pos-diff : Posℚ (a r* (c r+ (r- b)))
  pos-diff = r*-preserves-Pos a (c r+ (r- b)) pos-a b<c

  path : (a r* (c r+ (r- b))) == (a r* c) r+ (r- (a r* b))
  path = *-distrib-+-left {_} {_} {a} {c} {r- b} >=>
         cong ((a r* c) r+_) (RationalRing.minus-extract-right {a} {b})

r*₂-preserves-order : (a b : Rational) (c : ℚ⁺) -> a < b -> ( a r* ⟨ c ⟩) < (b r* ⟨ c ⟩)
r*₂-preserves-order a b c@(c' , _) a<b =
  subst2 _<_ (r*-commute c' a) (r*-commute c' b) (r*₁-preserves-order c a b a<b)

r*₁-preserves-≤ : (a : ℚ⁰⁺) (b c : ℚ) -> b ℚ≤ c -> (⟨ a ⟩ r* b) ℚ≤ (⟨ a ⟩ r* c)
r*₁-preserves-≤ (a , nn-a) b c b≤c =
  subst NonNeg (r*-distrib-diffℚ a b c) (r*-preserves-NonNeg nn-a b≤c)

r*₂-preserves-≤ : (a b : Rational) (c : ℚ⁰⁺) -> a ℚ≤ b -> ( a r* ⟨ c ⟩) ℚ≤ (b r* ⟨ c ⟩)
r*₂-preserves-≤ a b c@(c' , _) a≤b =
  subst2 _ℚ≤_ (r*-commute c' a) (r*-commute c' b) (r*₁-preserves-≤ c a b a≤b)



r*₁-flips-order : (a : ℚ⁻) (b c : Rational) -> b < c -> (⟨ a ⟩ r* c) < (⟨ a ⟩ r* b)
r*₁-flips-order a⁻@(a , _) b c b<c = pos-acab
  where
  neg-abc : Neg (a r* (diffℚ b c))
  neg-abc = r*₁-flips-sign a⁻ (diffℚ b c) b<c

  pos-acb : Pos (a r* (diffℚ c b))
  pos-acb = subst Pos (sym (r*-minus-extract-right a (diffℚ b c)) >=>
                       cong (a r*_) (sym (diffℚ-anticommute c b)))
                  (r--flips-sign _ neg-sign neg-abc)
  pos-acab : Pos (diffℚ (a r* c) (a r* b))
  pos-acab = subst Pos (RationalSemiring.*-distrib-+-left {a} {b} {(r- c)} >=>
                        cong ((a r* b) +_) (r*-minus-extract-right a c))
                   pos-acb

r*₂-flips-order : (a b : ℚ) (c : ℚ⁻) -> a < b -> (b r* ⟨ c ⟩) < (a r* ⟨ c ⟩)
r*₂-flips-order a b c@(c' , _) a<b =
  subst2 _<_ (r*-commute c' b) (r*-commute c' a) (r*₁-flips-order c a b a<b)


r*₁-flips-≤ : (a : ℚ⁰⁻) (b c : Rational) -> b ℚ≤ c -> (⟨ a ⟩ r* c) ℚ≤ (⟨ a ⟩ r* b)
r*₁-flips-≤ (a , _) b c (inj-r b=c) =
  subst NonNeg (r*-distrib-diffℚ a c b)
    (inj-r (r*₁-preserves-Zero a (subst Zero (sym (diffℚ-anticommute c b)) (r--flips-sign _ _ b=c))))
r*₁-flips-≤ (a , (inj-r za)) b c (inj-l _) =
  subst NonNeg (r*-distrib-diffℚ a c b) (inj-r (r*₂-preserves-Zero za _))
r*₁-flips-≤ (a , (inj-l na)) b c (inj-l b<c) =
  inj-l (r*₁-flips-order (a , na) b c b<c)

r*₂-flips-≤ : (a b : ℚ) (c : ℚ⁰⁻) -> a ℚ≤ b -> (b r* ⟨ c ⟩) ℚ≤ (a r* ⟨ c ⟩)
r*₂-flips-≤ a b c@(c' , _) a≤b =
  subst2 _ℚ≤_ (r*-commute c' b) (r*-commute c' a) (r*₁-flips-≤ c a b a≤b)

r1/-Pos-flips-order : (a b : ℚ⁺) -> ⟨ a ⟩ < ⟨ b ⟩ ->
                      (r1/ ⟨ b ⟩ (Pos->Inv (snd b))) < (r1/ ⟨ a ⟩ (Pos->Inv (snd a)))
r1/-Pos-flips-order (a , pos-a) (b , pos-b) a<b = subst Pos path pos-prod
  where
  inv-a = (Pos->Inv pos-a)
  inv-b = (Pos->Inv pos-b)
  a' = r1/ a inv-a
  b' = r1/ b inv-b
  pos-a' = r1/-preserves-Pos a inv-a pos-a
  pos-b' = r1/-preserves-Pos b inv-b pos-b

  pos-a'b' : Pos (a' r* b')
  pos-a'b' = r*₁-preserves-sign (_ , pos-a') b' pos-b'

  pos-prod : Pos ((a' r* b') r* (b r+ (r- a)))
  pos-prod = r*₁-preserves-sign ((a' r* b') , pos-a'b') (b r+ (r- a)) a<b

  path : (a' r* b') r* (b r+ (r- a)) == a' r+ (r- b')
  path =
    *-distrib-+-left >=>
    +-cong (*-assoc >=> *-right (r1/-inverse b inv-b) >=> *-right-one)
           (r*-minus-extract-right _ _ >=>
            cong r-_ (*-left *-commute >=> *-assoc >=>
                      *-right (r1/-inverse a inv-a) >=> *-right-one))


r1/-Pos-flips-≤ : (a b : ℚ⁺) -> ⟨ a ⟩ ℚ≤ ⟨ b ⟩ ->
                  (r1/ ⟨ b ⟩ (Pos->Inv (snd b))) ℚ≤ (r1/ ⟨ a ⟩ (Pos->Inv (snd a)))
r1/-Pos-flips-≤ a b (inj-l a<b) = inj-l (r1/-Pos-flips-order a b a<b)
r1/-Pos-flips-≤ (a , pos-a) (b , pos-b) (inj-r z-ab) =
  subst (_ℚ≤ (r1/ a (Pos->Inv pos-a))) path refl-ℚ≤

  where
  a==b = zero-diff->path a b z-ab

  path : (r1/ a (Pos->Inv pos-a)) == (r1/ b (Pos->Inv pos-b))
  path i = (r1/ (a==b i) (Pos->Inv (isProp->PathP (\ j -> isProp-Pos (a==b j)) pos-a pos-b i)))


0<1r : 0r < 1r
0<1r = subst Pos (sym (r+-right-zero 1r)) Pos-1r

-1r<0 : (r- 1r) < 0r
-1r<0 = r--flips-order 0r 1r 0<1r


1/2r<1r : 1/2r < 1r
1/2r<1r = subst2 _<_ (r+-left-zero 1/2r) (2r-path 1/2r >=> 2r-1/2r-path)  0r+1/2r<1/2r+1/2r
  where
  0<1/2r : 0r < 1/2r
  0<1/2r = Pos-0< 1/2r (Pos-1/ℕ (2 , tt))

  0r+1/2r<1/2r+1/2r : (0r r+ 1/2r) < (1/2r r+ 1/2r)
  0r+1/2r<1/2r+1/2r = r+₂-preserves-order 0r 1/2r 1/2r 0<1/2r

1/2ℕ<1/ℕ : (n : Nat⁺) -> 1/ℕ (2⁺ *⁺ n) < 1/ℕ n
1/2ℕ<1/ℕ n =
  subst2 _<_ (sym (1/2ℕ-path n)) (r*-left-one (1/ℕ n))
        (r*₂-preserves-order 1/2r 1r (1/ℕ n , Pos-1/ℕ n) 1/2r<1r)

ℕ->ℚ'-preserves-order : (a b : Nat) -> a nat.< b -> (ℕ->ℚ' a) <' (ℕ->ℚ' b)
ℕ->ℚ'-preserves-order a b (c , path) = ans
  where

  sd : Rational'
  sd = (same-denom-r+' (ℕ->ℚ' b) (r-' (ℕ->ℚ' a)))

  diff : Rational'
  diff = (ℕ->ℚ' b r+' (r-' (ℕ->ℚ' a)))

  sd~diff : sd r~ diff
  sd~diff = same-denom-r+'-r~ (ℕ->ℚ' b) (r-' (ℕ->ℚ' a)) refl

  path2 : int (c nat.+' suc a) i.+ (i.- (int a)) == i.pos c
  path2 = i.+-left (cong int nat.+'-right-suc) >=>
          i.+-left (int-inject-+' {suc c} {a}) >=>
          i.+-assoc >=>
          i.+-right i.add-minus-zero >=>
          i.+-right-zero

  Pos-b-a : i.Pos ((int b) i.+ (i.- (int a)))
  Pos-b-a = subst i.Pos (sym path2 >=> cong (\x -> (int x i.+ (i.- (int a)))) path) tt

  Pos-sd : Pos sd
  Pos-sd = is-signℚ' (int.*-Pos-Pos Pos-b-a tt)

  ans : Pos diff
  ans = r~-preserves-sign Pos-sd sd~diff

ℕ->ℚ-preserves-order : (a b : Nat) -> a nat.< b -> (ℕ->ℚ a) < (ℕ->ℚ b)
ℕ->ℚ-preserves-order a b a<b = (subst Pos (sym r+-eval) (is-signℚ (ℕ->ℚ'-preserves-order a b a<b)))

1/ℕ-flips-order : (a b : Nat⁺) -> ⟨ a ⟩ nat.< ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
1/ℕ-flips-order a@(a' , _) b@(b' , _) lt = subst2 _<_ b-path a-path ab*<
  where
  ab = 1/ℕ a r* 1/ℕ b
  pos-ab : Pos ab
  pos-ab = r*-preserves-Pos _ _ (Pos-1/ℕ a) (Pos-1/ℕ b)

  a-path : (ab r* (ℕ->ℚ b')) == 1/ℕ a
  a-path =
    r*-assoc (1/ℕ a) (1/ℕ b) (ℕ->ℚ b') >=>
    cong (1/ℕ a r*_) (1/ℕ-ℕ-path b) >=>
    r*-right-one (1/ℕ a)
  b-path : (ab r* (ℕ->ℚ a')) == 1/ℕ b
  b-path =
    cong (_r* ℕ->ℚ a') (r*-commute (1/ℕ a) (1/ℕ b)) >=>
    r*-assoc (1/ℕ b) (1/ℕ a) (ℕ->ℚ a') >=>
    cong (1/ℕ b r*_) (1/ℕ-ℕ-path a) >=>
    r*-right-one (1/ℕ b)

  ab*< : (ab r* (ℕ->ℚ a')) < (ab r* (ℕ->ℚ b'))
  ab*< = r*₁-preserves-order (ab , pos-ab) (ℕ->ℚ a') (ℕ->ℚ b')
           (ℕ->ℚ-preserves-order a' b' lt)


-- ℕ<-1/ℕ< : (a b : Nat⁺) -> ⟨ a ⟩ nat.< ⟨ b ⟩ -> 1/ℕ b < 1/ℕ a
-- ℕ<-1/ℕ< a b lt = ?


midℚ : ℚ -> ℚ -> ℚ
midℚ x y = 1/2r r* (x r+ y)


abstract
  r+-both-preserves-order : (a b c d : Rational) -> a < b -> c < d -> (a r+ c) < (b r+ d)
  r+-both-preserves-order a b c d a<b c<d = subst Posℚ (r+-swap-diffℚ a b c d) Pos-sum-diff
    where
    Pos-sum-diff : Posℚ ((diffℚ a b) r+ (diffℚ c d))
    Pos-sum-diff = r+-preserves-Pos (diffℚ a b) (diffℚ c d) a<b c<d

  r+-both-preserves-≤ : (a b c d : Rational) -> a ℚ≤ b -> c ℚ≤ d -> (a r+ c) ℚ≤ (b r+ d)
  r+-both-preserves-≤ a b c d a<b c<d = subst NonNeg (r+-swap-diffℚ a b c d) NonNeg-sum-diff
    where
    NonNeg-sum-diff : NonNeg ((diffℚ a b) r+ (diffℚ c d))
    NonNeg-sum-diff = r+-preserves-NonNeg {diffℚ a b} {diffℚ c d} a<b c<d


-- floor and <



isProp-ℚ≤ : {x y : ℚ} -> isProp (x ℚ≤ y)
isProp-ℚ≤ {x} {y} = isProp-NonNeg (diffℚ x y)

split-< : (q r : ℚ) -> (q < r) ⊎ (r ℚ≤ q)
split-< q r = handle (trichotomous-< q r)
  where
  handle : Tri (q < r) (q == r) (q > r) -> (q < r) ⊎ (r ℚ≤ q)
  handle (tri< q<r _ _) = inj-l q<r
  handle (tri= _ q=r _) =
    inj-r (inj-r (subst Zero (sym (r+-inverse r) >=> cong (_r+ (r- r)) (sym q=r)) Zero-0r))
  handle (tri> _ _ q>r) =
    inj-r (inj-l q>r)




NonNeg-fractional-part' : (q : ℚ') -> NonNeg (fractional-part' q)
NonNeg-fractional-part' (record { numerator = n ; denominator = d@(int.pos d')}) =
  NonNeg-nd->ℚ' (int.*-NonNeg-Pos (remainderℤ-NonNeg n (d , inj-l tt) tt) tt)
NonNeg-fractional-part' (record { numerator = n ; denominator = d@(int.neg d')}) =
  NonNeg-nd->ℚ' (int.*-NonPos-Neg (remainderℤ-NonPos n (d , inj-r tt) tt) tt)
NonNeg-fractional-part' (record { denominator = int.zero-int ; NonZero-denominator = inj-l ()})
NonNeg-fractional-part' (record { denominator = int.zero-int ; NonZero-denominator = inj-r ()})

NonNeg-fractional-part : (q : ℚ) -> NonNeg (fractional-part q)
NonNeg-fractional-part =
  RationalElim.elimProp
    (\q -> isProp-NonNeg (fractional-part q))
    (\q -> NonNeg-ℚ'->ℚ (NonNeg-fractional-part' q))

NonNeg->0≤ : (q : ℚ) -> NonNeg q -> 0r ℚ≤ q
NonNeg->0≤ q nn-q = subst NonNeg (sym (r+-right-zero q)) nn-q

diffℚ-fractional-part : (q : Rational) -> diffℚ (floorℚ q) q == (fractional-part q)
diffℚ-fractional-part q =
  cong (_r+ (r- (floorℚ q))) (sym (fractional-part-r+ q) >=>
                              r+-commute (floorℚ q) (fractional-part q)) >=>
  r+-assoc (fractional-part q) (floorℚ q) (r- (floorℚ q)) >=>
  cong (fractional-part q r+_) (r+-inverse (floorℚ q)) >=>
  r+-right-zero (fractional-part q)

floor-≤ : (q : ℚ) -> (floorℚ q) ℚ≤ q
floor-≤ q = subst NonNeg (sym (diffℚ-fractional-part q)) (NonNeg-fractional-part q)

fractional-part-0≤ : (q : ℚ) -> 0r ℚ≤ (fractional-part q)
fractional-part-0≤ q = NonNeg->0≤ (fractional-part q) (NonNeg-fractional-part q)



r+-Pos-NonNeg : {q1 q2 : Rational} -> Pos q1 -> NonNeg q2 -> Pos (q1 r+ q2)
r+-Pos-NonNeg {q1} {q2} p-q1 (inj-l p-q2) =
  r+-preserves-Pos q1 q2 p-q1 p-q2
r+-Pos-NonNeg {q1} {q2} p-q1 (inj-r z-q2) =
  subst Pos (sym (r+-right-zero q1) >=> cong (q1 r+_) (sym (Zero-path q2 z-q2))) p-q1

r+-NonNeg-Pos : {q1 q2 : Rational} -> NonNeg q1 -> Pos q2 -> Pos (q1 r+ q2)
r+-NonNeg-Pos {q1} {q2} n p = subst Pos (r+-commute q2 q1) (r+-Pos-NonNeg p n)

r+-NonNeg-NonNeg : {q1 q2 : Rational} -> NonNeg q1 -> NonNeg q2 -> NonNeg (q1 r+ q2)
r+-NonNeg-NonNeg {q1} {q2} nn-q1 (inj-l p-q2) =
  inj-l (r+-NonNeg-Pos nn-q1 p-q2)
r+-NonNeg-NonNeg {q1} {q2} nn-q1 (inj-r z-q2) =
  subst NonNeg (sym (r+-right-zero q1) >=> cong (q1 r+_) (sym (Zero-path q2 z-q2))) nn-q1

r+-Neg-NonPos : {q1 q2 : Rational} -> Neg q1 -> NonPos q2 -> Neg (q1 r+ q2)
r+-Neg-NonPos {q1} {q2} n-q1 np-q2 =
   subst Neg (cong r-_ (sym RationalRing.minus-distrib-plus) >=>
              RationalRing.minus-double-inverse {q1 r+ q2})
             (r--flips-sign _ _ (r+-Pos-NonNeg (r--flips-sign _ _ n-q1) (r--NonPos np-q2)))

r+-NonPos-Neg : {q1 q2 : Rational} -> NonPos q1 -> Neg q2 -> Neg (q1 r+ q2)
r+-NonPos-Neg {q1} {q2} np n = subst Neg (r+-commute q2 q1) (r+-Neg-NonPos n np)


NonNeg-≤ : (a b : ℚ) -> NonNeg a -> a ℚ≤ b -> NonNeg b
NonNeg-≤ a b nn-a a≤b = subst NonNeg (diffℚ-step a b) (r+-NonNeg-NonNeg nn-a a≤b)
NonPos-≤ : (a b : ℚ) -> NonPos b -> a ℚ≤ b -> NonPos a
NonPos-≤ a b np-b a≤b =
  subst NonPos (diffℚ-step b a)
               (r+-preserves-NonPos np-b (subst NonPos (sym (diffℚ-anticommute b a))
                                                       (r--NonNeg a≤b)))
Pos-≤ : (a b : ℚ) -> Pos a -> a ℚ≤ b -> Pos b
Pos-≤ a b p-a a≤b = subst Pos (diffℚ-step a b) (r+-Pos-NonNeg p-a a≤b)
Neg-≤ : (a b : ℚ) -> Neg b -> a ℚ≤ b -> Neg a
Neg-≤ a b n-b a≤b =
 subst Neg (RationalRing.minus-double-inverse {a})
           (r--flips-sign _ _ (Pos-≤ (r- b) (r- a) (r--flips-sign _ _ n-b) (r--flips-≤ a b a≤b)))

Pos-< : (a b : ℚ) -> NonNeg a -> a < b -> Pos b
Pos-< a b nn-a a<b = subst Pos (diffℚ-step a b) (r+-NonNeg-Pos nn-a a<b)

Neg-< : (a b : ℚ) -> NonPos b -> a < b -> Neg a
Neg-< a b np-b a<b =
 subst Neg (RationalRing.minus-double-inverse {a})
           (r--flips-sign _ _ (Pos-< (r- b) (r- a) (r--NonPos np-b) (r--flips-order a b a<b)))


trans-<-≤ : {q1 q2 q3 : Rational} -> q1 < q2 -> q2 ℚ≤ q3 -> q1 < q3
trans-<-≤ {q1} {q2} {q3} q1<q2 q2≤q3 =
  subst Pos (diffℚ-trans q1 q2 q3) (r+-Pos-NonNeg q1<q2 q2≤q3)

trans-≤-< : {q1 q2 q3 : Rational} -> q1 ℚ≤ q2 -> q2 < q3 -> q1 < q3
trans-≤-< {q1} {q2} {q3} q1≤q2 q2<q3 =
  subst Pos (diffℚ-trans q1 q2 q3) (r+-NonNeg-Pos q1≤q2 q2<q3)

abstract
  trans-ℚ≤ : {q1 q2 q3 : Rational} -> q1 ℚ≤ q2 -> q2 ℚ≤ q3 -> q1 ℚ≤ q3
  trans-ℚ≤ {q1} {q2} {q3} q1≤q2 q2<q3 =
    subst NonNeg (diffℚ-trans q1 q2 q3) (r+-NonNeg-NonNeg q1≤q2 q2<q3)

antisym-ℚ≤ : Antisymmetric _ℚ≤_
antisym-ℚ≤ {a} {b} (inj-l a<b) b≤a = bot-elim (irrefl-< {a} (trans-<-≤ {a} {b} {a} a<b b≤a))
antisym-ℚ≤ {a} {b} (inj-r a=b) _ = zero-diff->path a b a=b


-- Archimedean


private
  nd⁺->ℚ' : (n : Nat) (d : Nat⁺) -> ℚ'
  nd⁺->ℚ' n (d , pos-d) = record
    { numerator = i.ℕ->ℤ n
    ; denominator = i.ℕ->ℤ d
    ; NonZero-denominator = i.Pos->NonZero (i.Pos'->Pos pos-d)
    }

  n⁺d⁺->ℚ' : (n d : Nat⁺) -> ℚ'
  n⁺d⁺->ℚ' (n' , _)  d = nd⁺->ℚ' n' d

  n⁺d⁺->ℚ : (n d : Nat⁺) -> ℚ
  n⁺d⁺->ℚ n d = [ n⁺d⁺->ℚ' n d ]

  n⁺d⁺->ℚ⁺ : (n d : Nat⁺) -> ℚ⁺
  n⁺d⁺->ℚ⁺ n d = n⁺d⁺->ℚ n d ,
           is-signℚ (is-signℚ' (i.*-Pos-Pos (i.Pos'->Pos (snd n)) (i.Pos'->Pos (snd d))))


  ℚ⁺-elimProp :
    {ℓ : Level} -> {P : Pred ℚ⁺ ℓ} -> ((q : ℚ⁺) -> isProp (P q)) ->
    ((n d : Nat⁺) -> P (n⁺d⁺->ℚ⁺ n d)) ->
    (q : ℚ⁺) -> P q
  ℚ⁺-elimProp {P = P} isProp-P f (q , pos-q) =
    RationalElim.elimProp (\q -> isPropΠ (\pos-q -> isProp-P (q , pos-q))) handle q pos-q
    where
    find-rep : (q' : ℚ') -> (Pos q') -> Σ[ n ∈ Nat⁺ ] (Σ[ d ∈ Nat⁺ ] (n⁺d⁺->ℚ' n d r~ q'))
    find-rep (record { numerator = (i.pos n') ; denominator = (i.pos d') }) _ =
      ((suc n' , tt) , (suc d' , tt) , refl)
    find-rep (record { numerator = (i.zero-int) ; denominator = (i.pos d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg (inj-r tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.neg _) ; denominator = (i.pos d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonPos-NonNeg (inj-l tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.pos _) ; denominator = (i.neg d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonNeg-NonPos (inj-l tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.zero-int) ; denominator = (i.neg d') }) p =
      bot-elim (i.NonPos->¬Pos (i.*-NonNeg-NonPos (inj-r tt) (inj-l tt)) (isSignℚ'.v p))
    find-rep (record { numerator = (i.neg n') ; denominator = (i.neg d') }) _ =
      ((suc n' , tt) , (suc d' , tt) , i.minus-extract-right >=> sym i.minus-extract-left )
    find-rep (record { denominator = i.zero-int ; NonZero-denominator = inj-l ()})
    find-rep (record { denominator = i.zero-int ; NonZero-denominator = inj-r ()})

    handle : (q' : ℚ') -> (pos-q : (Pos [ q' ])) -> P ([ q' ] , pos-q)
    handle q' pos-q' = subst P path (f n d)
      where
      rep = find-rep q' (isSignℚ.v pos-q')
      n = fst rep
      d = fst (snd rep)
      nd~ = snd (snd rep)

      path : (n⁺d⁺->ℚ⁺ n d) == ([ q' ] , pos-q')
      path = ΣProp-path (\{x} -> isProp-Posℚ {x}) (eq/ _ _ nd~)


  1/ℕ-<-step1 : (n d : Nat⁺) -> (1/ℕ' d) ≤' (n⁺d⁺->ℚ' n d)
  1/ℕ-<-step1 n@(n'@(suc n'') , _)  d@(d' , pos-d) = ans
    where
    x1 = same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d))
    x2 = ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))

    NonNeg-numer : i.NonNeg (int n' i.+ (i.- (int 1)))
    NonNeg-numer = subst i.NonNeg (sym i.+-eval >=> i.+-commute) (int.NonNeg-nonneg n'')

    ans2 : NonNeg (same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)))
    ans2 = NonNeg-nd->ℚ' (i.*-NonNeg-NonNeg NonNeg-numer (i.Pos->NonNeg (i.Pos'->Pos pos-d)))

    ans~ : same-denom-r+' (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)) r~ ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))
    ans~ = same-denom-r+'-r~ (n⁺d⁺->ℚ' n d) (r-' (1/ℕ' d)) refl

    ans : NonNeg ((n⁺d⁺->ℚ' n d) r+' (r-' (1/ℕ' d)))
    ans = r~-preserves-NonNeg {x1} {x2} ans2 ans~


  1/ℕ-<-step2 : (n d : Nat⁺) -> ∃[ m ∈ Nat⁺ ] ( 1/ℕ' m ≤' (n⁺d⁺->ℚ' n d))
  1/ℕ-<-step2 n d = ∣ d , 1/ℕ-<-step1 n d ∣

  1/ℕ-<-step3 : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ ⟨ q ⟩)
  1/ℕ-<-step3 = ℚ⁺-elimProp (\q -> squash) (\n d -> (∥-map (handle n d) (1/ℕ-<-step2 n d)))
    where
    handle : (n d : Nat⁺) -> Σ[ m ∈ Nat⁺ ] (1/ℕ' m ≤' (n⁺d⁺->ℚ' n d)) ->
             Σ[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ (n⁺d⁺->ℚ n d))
    handle n d (m , p) = m , subst NonNeg (sym r+-eval) (NonNeg-ℚ'->ℚ p)

small-1/ℕ : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ m < ⟨ q ⟩)
small-1/ℕ q = ∥-map handle (1/ℕ-<-step3 q)
  where
  handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m ℚ≤ ⟨ q ⟩) -> Σ[ m ∈ Nat⁺ ] (1/ℕ m < ⟨ q ⟩)
  handle (m , m≤) = (2⁺ *⁺ m) , trans-<-≤ {1/ℕ (2⁺ *⁺ m)} {1/ℕ m} {⟨ q ⟩} (1/2ℕ<1/ℕ m) m≤

private
  small-1/2^ℕ-step1 : (q : ℚ⁺) -> ∃[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < ⟨ q ⟩)
  small-1/2^ℕ-step1 q@(q' , _) = ∥-map handle (small-1/ℕ q)
    where
    handle : Σ[ m ∈ Nat⁺ ] (1/ℕ m < q') -> Σ[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < q')
    handle (m@(m' , _) , lt) =
      m , trans-< {1/ℕ (2⁺ nat.^⁺ m')} {1/ℕ m} {q'}
            (1/ℕ-flips-order m (2⁺ nat.^⁺ m') (nat.2^n-large m')) lt

small-1/2^ℕ : (q : ℚ⁺) -> ∃[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < ⟨ q ⟩)
small-1/2^ℕ q@(q' , _) = ∥-map handle (small-1/2^ℕ-step1 q)
  where
  handle : Σ[ m ∈ Nat⁺ ] (1/ℕ (2⁺ nat.^⁺ ⟨ m ⟩) < q') ->
           Σ[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < q')
  handle ((m , _) , lt) = m , subst (_< q') (1/2^ℕ-path m) lt


ℚ-archimedian : (q1 q2 : ℚ⁺) -> ∃[ n ∈ Nat ] (((1/2r r^ℕ⁰ n) r* ⟨ q1 ⟩) < ⟨ q2 ⟩)
ℚ-archimedian q1@(q1' , pos-q1) q2@(q2' , pos-q2) = ∥-map handle (small-1/2^ℕ q3)
  where
  iq1 : ℚInv q1'
  iq1 p = (NonZero->¬Zero (Pos->NonZero pos-q1) (subst Zero (sym p) Zero-0r))

  q3' = q2' r* (r1/ q1' iq1)
  q3 : ℚ⁺
  q3 = q3' , r*-preserves-Pos _ _ pos-q2 (r1/-preserves-Pos q1' iq1 pos-q1)

  q3-path : q3' r* q1' == q2'
  q3-path = r*-assoc q2' (r1/ q1' iq1) q1' >=>
            cong (q2' r*_) (r1/-inverse q1' iq1) >=>
            r*-right-one q2'

  handle : Σ[ m ∈ Nat ] ((1/2r r^ℕ⁰ m) < q3') ->
           Σ[ m ∈ Nat ] (((1/2r r^ℕ⁰ m) r* q1') < q2')
  handle (m , lt) = m , subst (((1/2r r^ℕ⁰ m) r* q1') <_) q3-path lt2
    where
    lt2 : ((1/2r r^ℕ⁰ m) r* q1') < (q3' r* q1')
    lt2 = r*₂-preserves-order (1/2r r^ℕ⁰ m) q3' q1 lt


-- Seperate

seperate-< : (a b : ℚ) -> a < b -> Σ[ ε ∈ ℚ⁺ ] (a r+ ⟨ ε ⟩) < (b r+ (r- ⟨ ε ⟩))
seperate-< a b a<b = ε , pos-diff
  where
  Pos-1/2r = Pos-1/ℕ 2⁺
  ε' = 1/2r r* (1/2r r* (diffℚ a b))
  ε : ℚ⁺
  ε = ε' , r*-preserves-Pos 1/2r _ Pos-1/2r (r*-preserves-Pos 1/2r (diffℚ a b) Pos-1/2r a<b)

  path : (diffℚ (a r+ ε') (b r+ (r- ε'))) == 1/2r r* (diffℚ a b)
  path =
    sym (r+-swap-diffℚ a b ε' (r- ε')) >=>
    cong2 _r+_
          (sym (r*-left-one (diffℚ a b)))
          (sym (RationalRing.minus-distrib-plus {ε'} {ε'}) >=>
           cong r-_ (1/2r-path' (1/2r r* (diffℚ a b))) >=>
           sym (RationalRing.minus-extract-left {1/2r} {diffℚ a b})) >=>
    sym (*-distrib-+-right {_} {_} {1r} {r- 1/2r} {diffℚ a b}) >=>
    cong (_r* (diffℚ a b)) (cong (_r+ (r- 1/2r)) (sym (1/2r-path 1r) >=>
                                                  cong2 _+_ (r*-left-one 1/2r) (r*-left-one 1/2r)) >=>
                            r+-assoc 1/2r 1/2r (r- 1/2r) >=>
                            diffℚ-step 1/2r 1/2r)

  pos-diff : Pos (diffℚ (a r+ ε') (b r+ (r- ε')))
  pos-diff = subst Pos (sym path) (r*-preserves-Pos 1/2r (diffℚ a b) (Pos-1/ℕ 2⁺) a<b)
