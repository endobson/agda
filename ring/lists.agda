{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import ring

module ring.lists {ℓD : Level} {Domain : Type ℓD} (S : Semiring Domain) where

open import equality
open import list.unordered

import commutative-monoid
import list
import monoid
import unordered-list

open Semiring S

private
  variable
    ℓ : Level
    A : Set ℓ

-- Ordered sums/products
module _ where

  open list
  open monoid

  sum : List Domain -> Domain
  sum = concat {{+-Monoid}}

  sumʰ : Monoidʰ {{M₂ = +-Monoid}} sum
  sumʰ = concatʰ
  module sumʰ where
    open Monoidʰ sumʰ public
    preserves-+ = preserves-∙

  sum-inject-++ : {a b : List Domain} -> sum (a ++ b) == sum a + sum b
  sum-inject-++ {a} {b} = sumʰ.preserves-+ a b

  sum-map-inject-++ : (f : A -> Domain) {a1 a2 : List A}
                      -> (sum (map f (a1 ++ a2))) == (sum (map f a1)) + (sum (map f a2))
  sum-map-inject-++ f {a1} {a2} = Monoidʰ.preserves-∙ (sumʰ ∘ʰ (mapʰ f)) a1 a2

  sum-map-Permutation : {as1 as2 : (List A)} -> (f : A -> Domain) -> (Permutation A as1 as2)
                       -> (sum (map f as1)) == (sum (map f as2))
  sum-map-Permutation f (permutation-empty) = refl
  sum-map-Permutation f (permutation-cons a p) =
    cong (f a +_) (sum-map-Permutation f p)
  sum-map-Permutation f (permutation-swap a b p) =
    sym (+-assoc {f a} {f b})
    >=> (+-left (+-commute {f a} {f b}))
    >=> (+-assoc {f b} {f a})
  sum-map-Permutation f (permutation-compose p1 p2) =
    sum-map-Permutation f p1 >=> sum-map-Permutation f p2


  product : List Domain -> Domain
  product = concat {{*-Monoid}}


  productʰ : Monoidʰ {{M₂ = *-Monoid}} product
  productʰ = concatʰ
  module productʰ where
    open Monoidʰ productʰ public
    preserves-* = preserves-∙

  product-inject-++ : {a b : List Domain} -> product (a ++ b) == product a * product b
  product-inject-++ {a} {b} = productʰ.preserves-* a b

  product-map-inject-++ : (f : A -> Domain) {a1 a2 : List A}
    -> (product (map f (a1 ++ a2))) == (product (map f a1)) * (product (map f a2))
  product-map-inject-++ f {a1} {a2} = Monoidʰ.preserves-∙ (productʰ ∘ʰ (mapʰ f)) a1 a2

  product-map-Permutation : {as1 as2 : (List A)} -> (f : A -> Domain) -> (Permutation A as1 as2)
                            -> (product (map f as1)) == (product (map f as2))
  product-map-Permutation f (permutation-empty) = refl
  product-map-Permutation f (permutation-cons a p) =
    cong (f a *_) (product-map-Permutation f p)
  product-map-Permutation f (permutation-swap a b p) =
    sym (*-assoc {f a} {f b})
    >=> (*-left (*-commute {f a} {f b}))
    >=> (*-assoc {f b} {f a})
  product-map-Permutation f (permutation-compose p1 p2) =
    product-map-Permutation f p1 >=> product-map-Permutation f p2

-- Unordered sums/products
module _ where
  open unordered-list
  open commutative-monoid

  unordered-sum : UList Domain -> Domain
  unordered-sum = concat {{+-CommMonoid}} isSetDomain

  unordered-sumʰ : CommMonoidʰ unordered-sum
  unordered-sumʰ = concatʰ

  unordered-product : UList Domain -> Domain
  unordered-product = concat {{*-CommMonoid}} isSetDomain

  unordered-productʰ : CommMonoidʰ unordered-product
  unordered-productʰ = concatʰ


-- Proofs that sums/products are onder indepdendent
module _ where
  open list

  sum==unordered-sum : (l : List Domain) -> sum l == unordered-sum (unorder l)
  sum==unordered-sum []        = refl
  sum==unordered-sum (a :: as) = cong (a +_) (sum==unordered-sum as)

  product==unordered-product : (l : List Domain) -> product l == unordered-product (unorder l)
  product==unordered-product []        = refl
  product==unordered-product (a :: as) = cong (a *_) (product==unordered-product as)
