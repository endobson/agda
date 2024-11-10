{-# OPTIONS --cubical --safe --exact-split #-}

module order.instances.finsubset where

open import base
open import equality-path
open import equivalence
open import fin
open import finsubset
open import functions
open import functions.embedding
open import hlevel
open import isomorphism
open import order
open import relation
open import set-quotient.order

module _ {ℓD : Level} {D : Type ℓD}  where
  module _ ((n1 , f1 , isEmbed-f1) (n2 , f2 , isEmbed-f2) : OrderedFinSubset D) where
    record OrderedFinSubset≼ : Type ℓD where
      constructor ofs≼
      field
        fibers : ∀ (i : Fin n1) -> fiber f2 (f1 i)

      contains : ∀ {d : D} -> fiber f1 d -> fiber f2 d
      contains (i , p) = case (fibers i) of (\ (j , p2) -> j , p2 >=> p)

      convert : Fin n1 -> Fin n2
      convert i = fst (fibers i)
      convert-preserves-value : ∀ i -> f2 (convert i) == f1 i
      convert-preserves-value i = snd (fibers i)
      opaque
        isEmbedding-convert : isEmbedding convert
        isEmbedding-convert = isEmbedding-2of3₂ convert-preserves-value isEmbed-f2 isEmbed-f1


  private
    isProp-OrderedFinSubset≼ : ∀ {x y} -> isProp (OrderedFinSubset≼ x y)
    isProp-OrderedFinSubset≼ {_ , f1 , _} {_ , _ , embed-f2} (ofs≼ fibs1) (ofs≼ fibs2) =
      cong ofs≼ (isPropΠ (\i -> eqFun isEmbedding-eq-hasPropFibers embed-f2 (f1 i)) fibs1 fibs2)

    trans-OrderedFinSubset≼ : Transitive OrderedFinSubset≼
    trans-OrderedFinSubset≼ lt1 lt2 =
      ofs≼ (\i -> OrderedFinSubset≼.contains lt2 (OrderedFinSubset≼.fibers lt1 i))

  instance
    opaque
      isPreOrder-OrderedFinSubset≼ : isPreOrder OrderedFinSubset≼
      isPreOrder-OrderedFinSubset≼ = record
        { isProp-≼ = isProp-OrderedFinSubset≼
        ; refl-≼ = ofs≼ (\i -> i , refl)
        ; trans-≼ = trans-OrderedFinSubset≼
        }

module _ {ℓD : Level} {D : Type ℓD} where
  private
    opaque
      same-rel : ∀ (x y : OrderedFinSubset D) -> (OrderedFinSubset~ x y) ≃ (x ≼ y × y ≼ x)
      same-rel x@(xn , xf , ex) y@(yn , yf , ey) =
        isoToEquiv (iso forward backward
                        (\_ -> isProp× isProp-≼ isProp-≼ _ _)
                        (\_ -> isProp-OrderedFinSubset~ x y _ _))
        where
        forward : OrderedFinSubset~ x y -> (x ≼ y × y ≼ x)
        forward eq = ofs≼ fib-y , ofs≼ fib-x
          where
          fib-y : (i : Fin xn) -> fiber yf (xf i)
          fib-y i = eqFun (eq (xf i)) (i , refl)
          fib-x : (i : Fin yn) -> fiber xf (yf i)
          fib-x i = eqInv (eq (yf i)) (i , refl)

        backward : (x ≼ y × y ≼ x) -> OrderedFinSubset~ x y
        backward (x≼y , y≼x) d =
          isoToEquiv (iso x->y y->x
                          (\_ -> eqFun isEmbedding-eq-hasPropFibers ey _ _ _)
                          (\_ -> eqFun isEmbedding-eq-hasPropFibers ex _ _ _))
          where
          x->y : fiber xf d -> fiber yf d
          x->y = OrderedFinSubset≼.contains x≼y
          y->x : fiber yf d -> fiber xf d
          y->x = OrderedFinSubset≼.contains y≼x

  FinSubset≤' : Rel (FinSubset D) ℓD
  FinSubset≤' = SetQuotient≤ same-rel

  record FinSubset≤ (x y : FinSubset D) : Type ℓD where
    constructor fs≤
    field
      val : FinSubset≤' x y

  instance
    opaque
      isPartialOrder-FinSubset≤ : isPartialOrder FinSubset≤
      isPartialOrder-FinSubset≤ = record
        { refl-≤ = \{s} -> fs≤ (PO.refl-≤ {s})
        ; trans-≤ = \{x} {y} {z} (fs≤ x≤y) (fs≤ y≤z) -> (fs≤ (PO.trans-≤ {x} {y} {z} x≤y y≤z))
        ; antisym-≤ = \(fs≤ x≤y) (fs≤ y≤x) -> PO.antisym-≤ x≤y y≤x
        ; isProp-≤ = \{x} {y} (fs≤ lt1) (fs≤ lt2) i -> fs≤ (PO.isProp-≤ {x} {y} lt1 lt2 i)
        }
        where
        PO : isPartialOrder FinSubset≤'
        PO = isPartialOrder-SetQuotient≤ same-rel
        module PO = isPartialOrder PO

      isPreOrder-FinSubset≤ : isPreOrder FinSubset≤
      isPreOrder-FinSubset≤ = isPartialOrder->isPreOrder isPartialOrder-FinSubset≤
