{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.exponentiation.poly-index.eval where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality-path
open import equivalence.base
open import finite-commutative-monoid.extension
open import finsum
open import finsum.arithmetic
open import functions
open import functions.embedding
open import funext
open import hlevel
open import nat
open import ordered-ring.exponentiation.poly-index
open import ring
open import semiring
open import semiring.exponentiation
open import sigma.base

module _
  {ℓD : Level} {D : Type ℓD}
  {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}}
  where
  private
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      IACM = ACM

  eval-PI : (x y : D) {n : Nat} -> (f : PolyIndex n -> D) -> PolyIndex n -> D
  eval-PI x y f pi@(i , j , _) = f pi * (x ^ℕ i * y ^ℕ j)



  module _ (x y : D) where
    private
      isExt-eval-shift₁ : {n : Nat} -> (f : PolyIndex n -> D) ->
        isεExtension CM (\pi -> x * eval-PI x y f pi)
                        (\pi -> eval-PI x y (shift₁ f) pi)
      isExt-eval-shift₁ {n} f = record
        { inc = inc
        ; isEmbed = isEmbed
        ; agree = agree
        ; ε-others = ε-others
        }
        where
        inc : PolyIndex n -> PolyIndex (suc n)
        inc (i , j , p) = suc i , j , cong suc p

        isEmbed : isEmbedding inc
        isEmbed = eqInv isEmbedding-eq-hasPropFibers isPropFib
          where
          isPropFib : (i : PolyIndex (suc n)) -> isProp (fiber inc i)
          isPropFib pi (pi1@(j1 , k1 , eq1) , p1) (pi2@(j2 , k2 , eq2) , p2) =
            ΣProp-path (isSet-PolyIndex _ _) pi-path
            where
            j-path : j1 == j2
            j-path i = pred (fst ((p1 >=> sym p2) i))
            k-path : k1 == k2
            k-path i = (fst (snd ((p1 >=> sym p2) i)))
            eq-path : PathP (\i -> j-path i + k-path i == n) eq1 eq2
            eq-path = isProp->PathP (\_ -> isSetNat _ _)
            pi-path : pi1 == pi2
            pi-path i = j-path i , k-path i , eq-path i

        agree : ∀ pi -> x * eval-PI x y f pi == eval-PI x y (shift₁ f) (inc pi)
        agree _ = sym *-assoc >=> *-left *-commute >=> *-assoc >=> *-right (sym *-assoc)

        ε-others : ∀ pi -> ¬ (fiber inc pi) -> eval-PI x y (shift₁ f) pi == 0#
        ε-others (zero , _ , p) _ = *-left-zero
        ε-others (suc i , j , p) ¬fib = bot-elim (¬fib fib)
          where
          fib : fiber inc (suc i , j , p)
          fib = (i , j , cong pred p) ,
                (\k -> suc i , j , isSetNat _ _ (cong suc (cong pred p)) p k)

    shift₁-eval-path : {n : Nat} -> (f : PolyIndex n -> D) ->
                       finiteSum (eval-PI x y (shift₁ f)) == x * finiteSum (eval-PI x y f)
    shift₁-eval-path f =
      sym (finiteMerge-extension CM (isExt-eval-shift₁ f)) >=>
      finiteSum-*

    private
      isExt-eval-shift₂ : {n : Nat} -> (f : PolyIndex n -> D) ->
        isεExtension CM (\pi -> y * eval-PI x y f pi)
                        (\pi -> eval-PI x y (shift₂ f) pi)
      isExt-eval-shift₂ {n} f = record
        { inc = inc
        ; isEmbed = isEmbed
        ; agree = agree
        ; ε-others = ε-others
        }
        where
        inc : PolyIndex n -> PolyIndex (suc n)
        inc (i , j , p) = i , suc j , +'-right-suc >=> cong suc p

        isEmbed : isEmbedding inc
        isEmbed = eqInv isEmbedding-eq-hasPropFibers isPropFib
          where
          isPropFib : (i : PolyIndex (suc n)) -> isProp (fiber inc i)
          isPropFib pi (pi1@(j1 , k1 , eq1) , p1) (pi2@(j2 , k2 , eq2) , p2) =
            ΣProp-path (isSet-PolyIndex _ _) pi-path
            where
            check : inc pi1 == inc pi2
            check = (p1 >=> sym p2)

            j-path : j1 == j2
            j-path i = (fst ((p1 >=> sym p2) i))
            k-path : k1 == k2
            k-path i = pred (fst (snd ((p1 >=> sym p2) i)))
            eq-path : PathP (\i -> j-path i + k-path i == n) eq1 eq2
            eq-path = isProp->PathP (\_ -> isSetNat _ _)
            pi-path : pi1 == pi2
            pi-path i = j-path i , k-path i , eq-path i

        agree : ∀ pi -> y * eval-PI x y f pi == eval-PI x y (shift₂ f) (inc pi)
        agree (i , j , p) =
          *-commute >=> *-assoc >=> *-left f-path >=> *-right (*-assoc >=> *-right *-commute)
          where
          f-path : ∀ {q q'} -> f (i , j , q) == f (i , j , q')
          f-path {q} {q'} k = f (i , j , isSetNat _ _ q q' k)

        ε-others : ∀ pi -> ¬ (fiber inc pi) -> eval-PI x y (shift₂ f) pi == 0#
        ε-others (_ , zero , p) _ = *-left-zero
        ε-others (i , suc j , p) ¬fib = bot-elim (¬fib fib)
          where
          fib : fiber inc (i , suc j , p)
          fib = (i , j , cong pred (sym +'-right-suc >=> p)) ,
                (\k -> i , suc j , isSetNat _ _ (+'-right-suc >=>
                                                 cong suc (cong pred (sym +'-right-suc >=> p))) p k)


    shift₂-eval-path : {n : Nat} -> (f : PolyIndex n -> D) ->
                       finiteSum (eval-PI x y (shift₂ f)) == y * finiteSum (eval-PI x y f)
    shift₂-eval-path {n} f =
      sym (finiteMerge-extension CM (isExt-eval-shift₂ f)) >=>
      finiteSum-*

  module _ {{AG : AdditiveGroup ACM}} (x y : D) where
    eval-diff-path : (n : Nat) (f g : PolyIndex n -> D) ->
       eval-PI x y (\pi -> diff (f pi) (g pi)) ==
       (\pi -> diff (eval-PI x y f pi) (eval-PI x y g pi))
    eval-diff-path n f g = funExt (\_ -> *-distrib-diff-right)

    eval-+-path : (n : Nat) (f g : PolyIndex n -> D) ->
       eval-PI x y (\pi -> (f pi) + (g pi)) ==
       (\pi -> (eval-PI x y f pi) + (eval-PI x y g pi))
    eval-+-path n f g = funExt (\_ -> *-distrib-+-right)
