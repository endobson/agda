{-# OPTIONS --cubical --safe --exact-split #-}

open import abs
open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import equality
open import fraction.sign
open import hlevel
open import order
open import order.instances.int
open import order.instances.nat
open import rational
open import relation
open import ring
open import ring.implementations.int
open import semiring
open import sign
open import sign.instances.int
open import sign.instances.fraction
open import truncation

import int
import nat

module i = int
open i using (int)

open EqReasoning


module fraction.order where

diffℚ' : ℚ' -> ℚ' -> ℚ'
diffℚ' q r = r r+' (r-' q)

private
  infixl 20 _>~>_
  _>~>_ : {a b c : ℚ'} -> a r~' b -> b r~' c -> a r~' c
  _>~>_ = trans-r~'

abstract
  r+'-swap : (a b c d : ℚ') -> ((a r+' b) r+' (c r+' d)) r~ ((a r+' c) r+' (b r+' d))
  r+'-swap a b c d =
    r~'->r~ (s1 >~> s2 >~> s3 >~> s4 >~> s5)
    where
    s1 : ((a r+' b) r+' (c r+' d)) r~' (a r+' (b r+' (c r+' d)))
    s1 = r~->r~' r+'-assoc

    s2 : (a r+' (b r+' (c r+' d))) r~' (a r+' ((b r+' c) r+' d))
    s2 = r~->r~' (r+'-preserves-r~₂ a _ _ (sym r+'-assoc))

    s3 : (a r+' ((b r+' c) r+' d)) r~' (a r+' ((c r+' b) r+' d))
    s3 = r~->r~' (r+'-preserves-r~₂ a _ _ (r+'-preserves-r~₁ d _ _ (path->r~ (r+'-commute b c))))

    s4 : (a r+' ((c r+' b) r+' d)) r~' (a r+' (c r+' (b r+' d)))
    s4 = r~->r~' (r+'-preserves-r~₂ a _ _ r+'-assoc)

    s5 : (a r+' (c r+' (b r+' d))) r~' ((a r+' c) r+' (b r+' d))
    s5 = r~->r~' (sym r+'-assoc)


  diffℚ'-r+'₁ : (a b c : ℚ') -> (diffℚ' (a r+' b) (a r+' c)) r~ (diffℚ' b c)
  diffℚ'-r+'₁ a b c =
    r~'->r~ (s1 >~> s2 >~> s3 >~> s4)
    where
    s1 : ((diffℚ' (a r+' b) (a r+' c))) r~' ((a r+' c) r+' ((r-' a) r+' (r-' b)))
    s1 = path->r~' (cong ((a r+' c) r+'_) (r-'-distrib-r+' a b))

    s2 : ((a r+' c) r+' ((r-' a) r+' (r-' b))) r~' ((a r+' (r-' a)) r+' (c r+' (r-' b)))
    s2 = r~->r~' (r+'-swap a c (r-' a) (r-' b))

    s3 : ((a r+' (r-' a)) r+' (c r+' (r-' b))) r~' (0r' r+' (diffℚ' b c))
    s3 = r~->r~' (r+'-preserves-r~₁ (diffℚ' b c) (a r+' (r-' a)) 0r' (r+'-inverse a))

    s4 : (0r' r+' (diffℚ' b c)) r~' (diffℚ' b c)
    s4 = path->r~' (r+'-left-zero (diffℚ' b c))

  diffℚ'-r*'₁ : (a b c : ℚ') -> (diffℚ' (a r*' b) (a r*' c)) r~ (a r*' (diffℚ' b c))
  diffℚ'-r*'₁ a b c =
    trans-r~ (diffℚ' (a r*' b) (a r*' c)) ((a r*' c) r+' (a r*' (r-' b))) (a r*' (diffℚ' b c))
             (r+'-preserves-r~₂ (a r*' c) _ _ s7) s1
    where


    r*'-distrib-r+'-left : (a b c : ℚ') -> (a r*' (b r+' c)) r~ ((a r*' b) r+' (a r*' c))
    r*'-distrib-r+'-left a b c =
      r~'->r~ (s2 >~> r~->r~' (r*'-distrib-r+'-right _ _ _) >~> s5 >~> s6)
      where

      s2 : (a r*' (b r+' c)) r~' ((b r+' c) r*' a)
      s2 = path->r~' (r*'-commute _ _)

      s3 : (b r*' a) r~ (a r*' b)
      s3 = (path->r~ (r*'-commute b a))

      s4 : (c r*' a) r~ (a r*' c)
      s4 = (path->r~ (r*'-commute c a))

      s5 : ((b r*' a) r+' (c r*' a)) r~' ((a r*' b) r+' (c r*' a))
      s5 = (r~->r~' (r+'-preserves-r~₁ (c r*' a) (b r*' a) (a r*' b) s3))

      s6 : ((a r*' b) r+' (c r*' a)) r~' ((a r*' b) r+' (a r*' c))
      s6 = (r~->r~' (r+'-preserves-r~₂ (a r*' b) (c r*' a) (a r*' c) s4))

    s1 : ((a r*' c) r+' (a r*' (r-' b))) r~ (a r*' (c r+' (r-' b)))
    s1 = sym-r~ (a r*' (c r+' (r-' b))) ((a r*' c) r+' (a r*' (r-' b)))
                (r*'-distrib-r+'-left _ _ _)

    s7 : (r-' (a r*' b)) r~ (a r*' (r-' b))
    s7 = *-left (sym minus-extract-right)




record _ℚ'<_ (q : ℚ') (r : ℚ') : Type₀ where
  constructor ℚ'<-cons
  field
    v : Pos (diffℚ' q r)

_ℚ'>_ : ℚ' -> ℚ' -> Type₀
q ℚ'> r = r ℚ'< q

record _ℚ'≤_ (q : ℚ') (r : ℚ') : Type₀ where
  constructor ℚ'≤-cons
  field
    v : NonNeg (diffℚ' q r)

_ℚ'≥_ : ℚ' -> ℚ' -> Type₀
q ℚ'≥ r = r ℚ'≤ q

isProp-ℚ'< : {q r : ℚ'} -> isProp (q ℚ'< r)
isProp-ℚ'< (ℚ'<-cons p1) (ℚ'<-cons p2) = cong ℚ'<-cons (isProp-Pos {D = ℚ'} _ p1 p2)

isProp-ℚ'≤ : {q r : ℚ'} -> isProp (q ℚ'≤ r)
isProp-ℚ'≤ (ℚ'≤-cons p1) (ℚ'≤-cons p2) = cong ℚ'≤-cons (isProp-NonNeg {D = ℚ'} _ p1 p2)


r~-preserves-<₁ : {q1 q2 r : ℚ'} -> q1 ℚ'< r -> q1 r~ q2 -> q2 ℚ'< r
r~-preserves-<₁ {q1} {q2} {r} (ℚ'<-cons pos-diff) q1~q2 =
  ℚ'<-cons (r~-preserves-sign pos-diff
             (r+'-preserves-r~₂ r (r-' q1) (r-' q2) (r-'-preserves-r~ q1 q2 q1~q2)))

r~-preserves-<₂ : {q r1 r2 : ℚ'} -> q ℚ'< r1 -> r1 r~ r2 -> q ℚ'< r2
r~-preserves-<₂ {q} {r1} {r2} (ℚ'<-cons pos-diff) r1~r2 =
  ℚ'<-cons (r~-preserves-sign pos-diff (r+'-preserves-r~₁ (r-' q) r1 r2 r1~r2))

r~-preserves-≤₁ : {q1 q2 r : ℚ'} -> q1 ℚ'≤ r -> q1 r~ q2 -> q2 ℚ'≤ r
r~-preserves-≤₁ {q1} {q2} {r} (ℚ'≤-cons nn-diff) q1~q2 =
  ℚ'≤-cons (r~-preserves-NonNeg nn-diff
             (r+'-preserves-r~₂ r (r-' q1) (r-' q2) (r-'-preserves-r~ q1 q2 q1~q2)))

r~-preserves-≤₂ : {q r1 r2 : ℚ'} -> q ℚ'≤ r1 -> r1 r~ r2 -> q ℚ'≤ r2
r~-preserves-≤₂ {q} {r1} {r2} (ℚ'≤-cons nn-diff) r1~r2 =
  ℚ'≤-cons (r~-preserves-NonNeg nn-diff (r+'-preserves-r~₁ (r-' q) r1 r2 r1~r2))


r+'₁-preserves-< : (a b c : ℚ') -> b ℚ'< c -> (a r+' b) ℚ'< (a r+' c)
r+'₁-preserves-< a b c (ℚ'<-cons pos-diff) =
  ℚ'<-cons (r~-preserves-sign pos-diff (sym (diffℚ'-r+'₁ a b c)))

r*'-preserves-0< : (a b : ℚ') -> 0r' ℚ'< a -> 0r' ℚ'< b -> 0r' ℚ'< (a r*' b)
r*'-preserves-0< a b (ℚ'<-cons pos-a-diff) (ℚ'<-cons pos-b-diff) =
  ℚ'<-cons (subst Pos (sym (r+'-right-zero (a r*' b)))
                  (r*'-preserves-Pos (subst Pos (r+'-right-zero a) pos-a-diff)
                                     (subst Pos (r+'-right-zero b) pos-b-diff)))

r*'₁-preserves-< : (a b c : ℚ') -> 0r' ℚ'< a -> b ℚ'< c -> (a r*' b) ℚ'< (a r*' c)
r*'₁-preserves-< a b c (ℚ'<-cons pos-a-diff) (ℚ'<-cons pos-bc-diff) =
  ℚ'<-cons (r~-preserves-sign pabc
             (sym-r~ (diffℚ' (a r*' b) (a r*' c)) (a r*' (diffℚ' b c)) (diffℚ'-r*'₁ a b c)))
  where
  pa : Pos a
  pa = (subst Pos (r+'-right-zero a) pos-a-diff)
  pbc : Pos (diffℚ' b c)
  pbc = pos-bc-diff
  pabc : Pos (a r*' diffℚ' b c)
  pabc = (r*'-preserves-Pos pa pos-bc-diff)


irrefl-ℚ'< : Irreflexive _ℚ'<_
irrefl-ℚ'< {a} (ℚ'<-cons pos-diff) = (NonPos->¬Pos {D = ℚ'} (Zero->NonPos {D = ℚ'} zero-diff) pos-diff)
  where
  zero-diff : Zero (a r+' (r-' a))
  zero-diff = r~-preserves-sign Zero-0r' (sym (r+'-inverse a))

trans-ℚ'< : Transitive _ℚ'<_
trans-ℚ'< {a} {b} {c} (ℚ'<-cons a<b) (ℚ'<-cons b<c) = a<c
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

  a<c : a ℚ'< c
  a<c = ℚ'<-cons (r~-preserves-sign (r+'-preserves-Pos b<c a<b) f-path)


decide-ℚ'< : Decidable2 _ℚ'<_
decide-ℚ'< x y = handle (decide-sign z')
  where
  z = y r+' (r-' x)
  z' = ℚ'.numerator z * ℚ'.denominator z
  handle : Σ[ s ∈ Sign ] (isSign s z') -> Dec (x ℚ'< y)
  handle (pos-sign  , pz) = yes (ℚ'<-cons (is-signℚ' pz))
  handle (zero-sign , zz) =
    no (\ (ℚ'<-cons pz) -> NonPos->¬Pos {D = i.Int} (Zero->NonPos {D = i.Int} zz) (isSignℚ'.v pz))
  handle (neg-sign  , nz) =
    no (\ (ℚ'<-cons pz) -> NonPos->¬Pos {D = i.Int} (Neg->NonPos {D = i.Int} nz) (isSignℚ'.v pz))

asym-ℚ'< : Asymmetric _ℚ'<_
asym-ℚ'< {q} {r} (ℚ'<-cons pos-d1) (ℚ'<-cons pos-d2) = NonPos->¬Pos {D = ℚ'} (inj-l neg-d2) pos-d2
  where
  d1 = r r+' (r-' q)
  d2 = q r+' (r-' r)
  -d1==d2 : (r-' d1) == d2
  -d1==d2 = r-'-distrib-r+' r (r-' q) >=>
            cong ((r-' r) r+'_) (r-'-double-inverse q) >=>
            r+'-commute (r-' r) q

  neg-d2 = (subst Neg -d1==d2 (r-'-flips-sign _ pos-sign pos-d1))


private
  r~->zero-diff : {q r : ℚ'} -> (q r~ r) -> Zero (r r+' (r-' q))
  r~->zero-diff {q} {r} q~r = zd
    where
    diff-v = (r r+' (r-' q))
    diffᵉ-v = (r r+'ᵉ (r-' q))
    n = ℚ'.numerator diffᵉ-v
    zpath : n == (int.int 0)
    zpath = +-left (sym q~r) >=>
            +-right minus-extract-left >=>
            int.add-minus-zero
    zn : Zero (ℚ'.numerator diff-v)
    zn = subst Zero (sym zpath >=> cong ℚ'.numerator (sym r+'-eval)) tt
    zd = is-signℚ' (int.*-Zero₁ zn)

  zero-diff->r~ : {q r : ℚ'} -> Zero (r r+' (r-' q)) -> (q r~ r)
  zero-diff->r~ {q} {r} z = q~r
    where
    diffᵉ = (r r+'ᵉ (r-' q))
    nq = ℚ'.numerator q
    dq = ℚ'.denominator q
    nr = ℚ'.numerator r
    dr = ℚ'.denominator r

    znᵉ : (ℚ'.numerator diffᵉ) == (int.int 0)
    znᵉ = cong ℚ'.numerator (sym r+'-eval) >=> int.Zero-path _ (Zero->Zero-numer z)

    q~r : nq * dr == nr * dq
    q~r =
      begin
        nq * dr
      ==< sym +-right-zero >=> +-right ((sym znᵉ) >=> +-commute) >
        (nq * dr) + (((- nq) * dr) + nr * dq)
      ==< +-right (+-left minus-extract-left) >
        (nq * dr) + (- (nq * dr) + nr * dq)
      ==< sym +-assoc >=> +-left int.add-minus-zero >=> +-left-zero >
        nr * dq
      end


  ℚ'<-¬r~ : {q r : ℚ'} -> q ℚ'< r -> ¬ (q r~ r)
  ℚ'<-¬r~ {q} {r} (ℚ'<-cons pos-diff) q~r = NonPos->¬Pos {D = ℚ'} (inj-r (r~->zero-diff q~r)) pos-diff


ℚ'≤-elim : {ℓ : Level} {P : ℚ' -> ℚ' -> Type ℓ} ->
           ({q r : ℚ'} -> q ℚ'< r -> P q r) ->
           ({q r : ℚ'} -> q r~ r -> P q r) ->
           (q r : ℚ') -> q ℚ'≤ r -> P q r
ℚ'≤-elim f< f~ q r (ℚ'≤-cons (inj-l pd)) = f< (ℚ'<-cons pd)
ℚ'≤-elim f< f~ q r (ℚ'≤-cons (inj-r zd)) = f~ (zero-diff->r~ zd)



trichotomous~-ℚ'< : (q r : ℚ') -> Tri (q ℚ'< r) (q r~ r) (r ℚ'< q)
trichotomous~-ℚ'< q r = handle (decide-sign d')
  where
  d = r r+' (r-' q)
  d2 = q r+' (r-' r)
  -d==d2 : (r-' d) == d2
  -d==d2 = r-'-distrib-r+' r (r-' q) >=>
           cong ((r-' r) r+'_) (r-'-double-inverse q) >=>
           r+'-commute (r-' r) q

  d' = ℚ'.numerator d * ℚ'.denominator d
  handle : Σ[ s ∈ Sign ] (isSign s d') -> Tri (q ℚ'< r) (q r~ r) (r ℚ'< q)
  handle (pos-sign  , pd) =
    tri< q<r (ℚ'<-¬r~ q<r) (asym-ℚ'< q<r)
    where
    q<r = (ℚ'<-cons (is-signℚ' pd))
  handle (zero-sign , zd) =
    tri= (\ (ℚ'<-cons pd) -> NonPos->¬Pos {D = i.Int} (Zero->NonPos {D = i.Int} zd) (isSignℚ'.v pd))
         (sym r~q)
         (\ (ℚ'<-cons pd2) ->
           NonZero->¬Zero {D = ℚ'} (inj-l pd2)
             (subst Zero -d==d2 (r-'-flips-sign _ zero-sign (is-signℚ' zd))))
    where
    d'-path : d' == (int.int 0)
    d'-path = int.Zero-path d' zd
    n = ℚ'.numerator d
    n-path : n == (int.int 0)
    n-path = int.*-left-zero-eq (ℚ'.NonZero-denominator d) d'-path

    r~q : r r~ q
    r~q =
      sym +-right-zero >=>
      +-right (sym int.add-minus-zero >=>
               +-commute >=>
               +-left (sym minus-extract-left)) >=>
      sym +-assoc >=>
      +-left (cong ℚ'.numerator (sym r+'-eval) >=> n-path) >=>
      +-left-zero

  handle (neg-sign  , nd) =
    tri> (\ (ℚ'<-cons pd) -> NonPos->¬Pos {D = i.Int} (Neg->NonPos {D = i.Int} nd) (isSignℚ'.v pd))
         (\ q~r -> ℚ'<-¬r~ r<q (sym q~r))
         r<q
    where
    r<q = (ℚ'<-cons (subst Pos -d==d2 (r-'-flips-sign _ neg-sign (is-signℚ' nd))))


connected~-ℚ'< : {q r : ℚ'} -> ¬(q ℚ'< r) -> ¬(r ℚ'< q) -> q r~ r
connected~-ℚ'< {q} {r} ¬q<r ¬r<q = handle (trichotomous~-ℚ'< q r)
  where

  handle : Tri (q ℚ'< r) (q r~ r) (r ℚ'< q) -> q r~ r
  handle (tri< q<r _ _) = bot-elim (¬q<r q<r)
  handle (tri= _ q~r _) = q~r
  handle (tri> _ _ r<q) = bot-elim (¬r<q r<q)

comparison-ℚ'< : Comparison _ℚ'<_
comparison-ℚ'< x y z x<z = ∣ handle (trichotomous~-ℚ'< x y) (trichotomous~-ℚ'< y z) ∣
  where
  handle : Tri (x ℚ'< y) (x r~ y) (y ℚ'< x) -> Tri (y ℚ'< z) (y r~ z) (z ℚ'< y) ->
           (x ℚ'< y) ⊎ (y ℚ'< z)
  handle (tri< x<y _ _)     _              = inj-l x<y
  handle (tri= _   _ _)     (tri< y<z _ _) = inj-r y<z
  handle (tri> _   _ _)     (tri< y<z _ _) = inj-r y<z
  handle (tri= _   x~y _)   (tri= ¬y<z _ _) = bot-elim (¬y<z (r~-preserves-<₁ x<z x~y))
  handle (tri= _   x~y _)   (tri> ¬y<z _ _) = bot-elim (¬y<z (r~-preserves-<₁ x<z x~y))
  handle (tri> _   _ y<x)   (tri= ¬y<z _ _) = bot-elim (¬y<z (trans-ℚ'< y<x x<z))
  handle (tri> _   _ y<x)   (tri> ¬y<z _ _) = bot-elim (¬y<z (trans-ℚ'< y<x x<z))


refl-ℚ'≤ : Reflexive _ℚ'≤_
refl-ℚ'≤ {a} = (ℚ'≤-cons (inj-r zero-diff))
  where
  zero-diff : Zero (a r+' (r-' a))
  zero-diff = r~-preserves-sign Zero-0r' (sym (r+'-inverse a))

weaken-ℚ'< : {a b : ℚ'} -> a ℚ'< b -> a ℚ'≤ b
weaken-ℚ'< (ℚ'<-cons p) = (ℚ'≤-cons (inj-l p))

trans-ℚ'≤ : Transitive _ℚ'≤_
trans-ℚ'≤ {a} {b} {c} (ℚ'≤-cons a<b) (ℚ'≤-cons b<c) = a<c
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

  a<c : a ℚ'≤ c
  a<c = ℚ'≤-cons (r~-preserves-NonNeg (r+'-preserves-NonNeg b<c a<b) f-path)

trans-ℚ'≤-ℚ'< : {a b c : ℚ'} -> a ℚ'≤ b -> b ℚ'< c -> a ℚ'< c
trans-ℚ'≤-ℚ'< (ℚ'≤-cons (inj-l p)) = trans-ℚ'< (ℚ'<-cons p)
trans-ℚ'≤-ℚ'< (ℚ'≤-cons (inj-r z)) b<c =
  r~-preserves-<₁ b<c (sym (zero-diff->r~ z))

trans-ℚ'<-ℚ'≤ : {a b c : ℚ'} -> a ℚ'< b -> b ℚ'≤ c -> a ℚ'< c
trans-ℚ'<-ℚ'≤ a<b (ℚ'≤-cons (inj-l p)) = trans-ℚ'< a<b (ℚ'<-cons p)
trans-ℚ'<-ℚ'≤ a<b (ℚ'≤-cons (inj-r z)) =
  r~-preserves-<₂ a<b (zero-diff->r~ z)

connex-ℚ'≤ : Connex _ℚ'≤_
connex-ℚ'≤ a b = ∣ handle (trichotomous~-ℚ'< a b) ∣
  where
  handle : Tri (a ℚ'< b) (a r~ b) (b ℚ'< a) -> (a ℚ'≤ b) ⊎ (b ℚ'≤ a)
  handle (tri< a<b _ _) = inj-l (weaken-ℚ'< a<b)
  handle (tri= _ a~b _) = inj-l (ℚ'≤-cons (inj-r (r~->zero-diff a~b)))
  handle (tri> _ _ b<a) = inj-r (weaken-ℚ'< b<a)

antisym~-ℚ'≤ : {a b : ℚ'} -> a ℚ'≤ b -> b ℚ'≤ a -> a r~ b
antisym~-ℚ'≤ {a} {b} a≤b b≤a = handle (trichotomous~-ℚ'< a b)
  where
  handle : Tri (a ℚ'< b) (a r~ b) (b ℚ'< a) -> a r~ b
  handle (tri< a<b _ _) = bot-elim (irrefl-ℚ'< (trans-ℚ'≤-ℚ'< b≤a a<b))
  handle (tri= _ a~b _) = a~b
  handle (tri> _ _ b<a) = bot-elim (irrefl-ℚ'< (trans-ℚ'≤-ℚ'< a≤b b<a))

-- Constants

ℕ->ℚ'-preserves-< : {a b : Nat} -> a < b -> (ℕ->ℚ' a) ℚ'< (ℕ->ℚ' b)
ℕ->ℚ'-preserves-< {a} {b} (c , path) = ℚ'<-cons ans
  where

  sd : ℚ'
  sd = (same-denom-r+' (ℕ->ℚ' b) (r-' (ℕ->ℚ' a)))

  diff-v : ℚ'
  diff-v = (ℕ->ℚ' b r+' (r-' (ℕ->ℚ' a)))

  sd~diff : sd r~ diff-v
  sd~diff = same-denom-r+'-r~ (ℕ->ℚ' b) (r-' (ℕ->ℚ' a)) refl

  path2 : int (c + suc a) + (- (int a)) == i.pos c
  path2 = +-left (cong int nat.+'-right-suc) >=>
          +-left (int-inject-+' {suc c} {a}) >=>
          +-assoc >=>
          +-right i.add-minus-zero >=>
          +-right-zero

  Pos-b-a : i.Pos ((int b) + (- (int a)))
  Pos-b-a = subst i.Pos (sym path2 >=> cong (\x -> (int x + (- (int a)))) path) tt

  Pos-sd : Pos sd
  Pos-sd = is-signℚ' (int.*-Pos-Pos Pos-b-a tt)

  ans : Pos diff-v
  ans = r~-preserves-sign Pos-sd sd~diff


ℕ->ℚ'-preserves-≤ : {a b : Nat} -> a ≤ b -> (ℕ->ℚ' a) ℚ'≤ (ℕ->ℚ' b)
ℕ->ℚ'-preserves-≤ (zero , path) =
  subst2 _ℚ'≤_ refl (cong ℕ->ℚ' path) refl-ℚ'≤
ℕ->ℚ'-preserves-≤ {a} {b} (suc c , path) = weaken-ℚ'< aℚ'<b
  where
  a<b : a < b
  a<b = c , nat.+'-right-suc >=> path
  aℚ'<b : (ℕ->ℚ' a) ℚ'< (ℕ->ℚ' b)
  aℚ'<b = ℕ->ℚ'-preserves-< a<b
