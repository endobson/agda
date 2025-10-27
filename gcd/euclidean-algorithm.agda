{-# OPTIONS --cubical --safe --exact-split #-}

module gcd.euclidean-algorithm where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import div
open import equality
open import gcd.propositional
open import int
open import int.nat
open import int.order
open import linear-combo
open import nat
open import nat.binary-strong-induction
open import nat.order
open import order
open import order.instances.nat
open import order.instances.int
open import order.minmax.instances.int
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.int
open import relation
open import ring.implementations.int
open import semiring
open import truncation

open EqReasoning

linear-combo->gcd : {a b d : Int} -> LinearCombination a b d -> d div a -> d div b -> GCD a b (abs d)
linear-combo->gcd {d = d} (linear-combo x y p) da db =
  (gcd (0≤->NonNeg abs-0≤) (∣ div-abs-left da ∣) (∣ div-abs-left db ∣)
    (\ z za zb -> ∣ transport (\i -> z div abs (p i)) (div-abs-right (div-linear za zb {x} {y})) ∣))

private
  data EuclideanTree : Nat -> Nat -> Type₀ where
    euclidean-tree-base : (a : Nat) -> EuclideanTree a 0
    euclidean-tree-sym : {a b : Nat} -> EuclideanTree a b -> EuclideanTree b a
    euclidean-tree-step : {a b : Nat} -> EuclideanTree a b -> EuclideanTree a (a +' b)

  euclidean-tree-same : (a : Nat) -> EuclideanTree a a
  euclidean-tree-same a = transport (\i -> EuclideanTree a (+'-right-zero {a} i))
                                    (euclidean-tree-step (euclidean-tree-base a))

  euclidean-tree-same' : {x y : Nat} -> x == y -> EuclideanTree x y
  euclidean-tree-same' {x} {y} p = transport (\i -> EuclideanTree x (p i)) (euclidean-tree-same x)


  EuclideanTree⁺ : Nat⁺ -> Nat⁺ -> Type₀
  EuclideanTree⁺ a b = EuclideanTree ⟨ a ⟩ ⟨ b ⟩

  euclidean-tree-root : {a b : Nat} -> EuclideanTree a b -> Nat
  euclidean-tree-root (euclidean-tree-base d) = d
  euclidean-tree-root (euclidean-tree-sym t) = (euclidean-tree-root t)
  euclidean-tree-root (euclidean-tree-step t) = (euclidean-tree-root t)

  root-div-both : {a b : Nat} -> (t : EuclideanTree a b)
                  -> ((euclidean-tree-root t) div' a × (euclidean-tree-root t) div' b)
  root-div-both (euclidean-tree-base a) = div'-refl , div'-zero
  root-div-both (euclidean-tree-sym t) = (proj₂ rec) , (proj₁ rec)
    where
    rec = (root-div-both t)
  root-div-both (euclidean-tree-step t) = proj₁ rec , div'-+' (proj₁ rec) (proj₂ rec)
    where
    rec = (root-div-both t)

  root-linear-combo : {a b : Nat} -> (t : EuclideanTree a b)
                      -> LinearCombination' a b (euclidean-tree-root t)
  root-linear-combo (euclidean-tree-base a) = linear-combo-zero
  root-linear-combo (euclidean-tree-sym t) = linear-combo-sym (root-linear-combo t)
  root-linear-combo (euclidean-tree-step t) = linear-combo-+' (root-linear-combo t)

  euclidean-tree->gcd : {a b : Nat} -> (t : EuclideanTree a b) -> GCD' a b (euclidean-tree-root t)
  euclidean-tree->gcd {a} {b} t = gcd->gcd' g'
    where
    r : Nat
    r = euclidean-tree-root t
    div-both : (r div' a) × (r div' b)
    div-both = root-div-both t
    lc : LinearCombination' a b r
    lc = root-linear-combo t
    g : GCD (int a) (int b) (abs (int r))
    g = linear-combo->gcd lc (div'->div (proj₁ div-both)) (div'->div (proj₂ div-both))
    g' : GCD (int a) (int b) (int r)
    g' = subst (GCD (int a) (int b)) (abs-0≤-path (0≤nonneg r)) g


compute-euclidean-tree : (a b : Nat) -> EuclideanTree a b
compute-euclidean-tree a b = sym-binary-strong-induction euclidean-tree-sym f a b
  where
  f : (x y : Nat)
      -> (x ≤ y)
      -> ({a b : Nat} -> a < y -> b < y -> EuclideanTree a b)
      -> EuclideanTree x y
  f zero y x≤y rec = euclidean-tree-sym (euclidean-tree-base y)
  f x@(suc x') y x≤y rec = handle (decide-nat x y)
    where
    handle : Dec (x == y) -> EuclideanTree x y
    handle (yes x==y) = (euclidean-tree-same' x==y)
    handle (no  x!=y) = transport (\i -> EuclideanTree x (path i))
                                  (euclidean-tree-step (rec x<y k<y))
      where
      x<y = strengthen-≤ x≤y x!=y

      k = suc (fst x<y)
      path : (x +' k) == y
      path = +'-commute {x} {k} >=> sym +'-right-suc >=> snd x<y
      k<y : k < y
      k<y = x' , +'-right-suc >=> path

abstract
  gcd'-exists : (a b : Nat) -> Σ[ d ∈ Nat ] (GCD' a b d)
  gcd'-exists a b = (euclidean-tree-root t) , (euclidean-tree->gcd t)
    where
    t : EuclideanTree a b
    t = compute-euclidean-tree a b

  gcd-exists : (a b : Int) -> Σ[ d ∈ Int ] (GCD a b d)
  gcd-exists a b = (int (euclidean-tree-root t)) , (gcd'->gcd (NonNeg-nonneg _) (euclidean-tree->gcd t))
    where
    t : EuclideanTree (abs' a) (abs' b)
    t = compute-euclidean-tree (abs' a) (abs' b)


-- GCD and linear combos convertible

abstract
  gcd'->linear-combo : {a b d : Nat} -> GCD' a b d -> LinearCombination' a b d
  gcd'->linear-combo {a} {b} {d} gcd-d =
    transport (\i -> LinearCombination' a b ((gcd'-unique gcd-d' gcd-d) i)) lc
    where
    module _ where
      t = compute-euclidean-tree a b
      lc = root-linear-combo t
      gcd-d' = euclidean-tree->gcd t

gcd->linear-combo : {a b d : Int} -> GCD a b d -> LinearCombination a b d
gcd->linear-combo {a} {b} {d} g = linear-combo-unabs lc₂
  where
  lc₁ : LinearCombination (int (abs' a)) (int (abs' b)) (int (abs' d))
  lc₁ = gcd'->linear-combo (gcd->gcd' g)
  lc₂ : LinearCombination (abs a) (abs b) (abs d)
  lc₂ = transport (\i -> LinearCombination (abs'-abs-path {a} i) (abs'-abs-path {b} i) (abs'-abs-path {d} i))
                  lc₁

linear-combo-one->gcd-one : {a b : Int} -> LinearCombination a b (int 1) -> GCD a b (int 1)
linear-combo-one->gcd-one lc =
  subst (GCD _ _) (abs-0≤-path (0≤nonneg 1)) (linear-combo->gcd lc div-one div-one)



-- Euclids lemma
euclids-lemma : {a b c : Int} -> a div (b * c) -> GCD a b (int 1) -> a div c
euclids-lemma {a} {b} {c} a%bc ab-gcd = handle (gcd->linear-combo ab-gcd)
  where
  handle : (LinearCombination a b (int 1)) -> a div c
  handle (linear-combo x y pr) = a%c
    where
    c==stuff : c == x * c * a + y * (b * c)
    c==stuff =
      begin
        c
      ==< sym (*-left-one) >
        (int 1) * c
      ==< *-left (sym pr) >
        (x * a + y * b) * c
      ==< *-distrib-+-right >
        x * a * c + y * b * c
      ==< +-left *-assoc >
        x * (a * c) + y * b * c
      ==< +-left (*-right *-commute) >
        x * (c * a) + y * b * c
      ==< sym (+-left *-assoc) >
        x * c * a + y * b * c
      ==< +-right *-assoc >
        x * c * a + y * (b * c)
      end
    a%stuff : a div (x * c * a + y * (b * c))
    a%stuff = div-linear div-refl a%bc {x * c} {y}

    a%c : a div c
    a%c = (subst (\ x -> a div x) (sym c==stuff) a%stuff)

euclids-lemma' : {a b c : Nat} -> a div' (b *' c) -> GCD' a b 1 -> a div' c
euclids-lemma' {a} {b} {c} a%bc g = result
  where
  int-a%bc : (int a) div (int b * int c)
  int-a%bc = transport (\i -> (int a) div (ℕ->ℤ-* {b} {c} i)) (div'->div a%bc)
  result : a div' c
  result = (div->div' (euclids-lemma int-a%bc (gcd'->gcd/nat g)))
