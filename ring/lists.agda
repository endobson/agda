{-# OPTIONS --cubical --safe --exact-split #-}

open import additive-group
open import base
open import semiring

module ring.lists {ℓD : Level} {Domain : Type ℓD} {ACM : AdditiveCommMonoid Domain}
                  (S : Semiring ACM) where

open import equality
open import hlevel.base
open import infinity-monoid using
  ( InfinityMonoidʰ
  ; InfinityMonoidʰᵉ
  )

import commutative-monoid
import list
import monoid
import unordered-list.base
import unordered-list.operations

private
  variable
    ℓ : Level
    A : Set ℓ

  instance
    IS = S
    IACM = ACM

  module S = Semiring S

-- Ordered sums/products
module _ where

  open list
  open monoid

  private
    instance
      isSet'-Domain : isSet' Domain
      isSet'-Domain .isSet'.f = S.isSet-Domain

  sum : List Domain -> Domain
  sum = concat {{S.+-InfinityMonoid}}

  sumʰ : InfinityMonoidʰᵉ ListInfinityMonoid S.+-InfinityMonoid sum
  sumʰ = concatʰ {{M = S.+-InfinityMonoid}}
  module sumʰ where
    open InfinityMonoidʰ sumʰ public
    preserves-+ = preserves-∙

  sum-inject-++ : {a b : List Domain} -> sum (a ++ b) == sum a + sum b
  sum-inject-++ {a} {b} = sumʰ.preserves-+ a b

  sum-map-inject-++ : (f : A -> Domain) {a1 a2 : List A}
                      -> (sum (map f (a1 ++ a2))) == (sum (map f a1)) + (sum (map f a2))
  sum-map-inject-++ f {a1} {a2} = InfinityMonoidʰ.preserves-∙ (sumʰ infinity-monoid.∘ʰ (mapʰ f)) a1 a2

  sum-map-Permutation : {as1 as2 : (List A)} -> (f : A -> Domain) -> (Permutation A as1 as2)
                       -> (sum (map f as1)) == (sum (map f as2))
  sum-map-Permutation f (permutation-empty) = refl
  sum-map-Permutation f (permutation-cons a p) =
    cong (f a +_) (sum-map-Permutation f p)
  sum-map-Permutation f (permutation-swap a b p) =
    sym (+-assoc) >=> (+-left +-commute) >=> (+-assoc)
  sum-map-Permutation f (permutation-compose p1 p2) =
    sum-map-Permutation f p1 >=> sum-map-Permutation f p2

  sum-map-* : (k : Domain) (as : List Domain)
              -> sum (map (k *_) as) == k * (sum as)
  sum-map-* k []        = sym *-right-zero
  sum-map-* k (a :: as) =
    begin
      sum (map (k *_) (a :: as))
    ==<>
      (k * a) + (sum (map (k *_) as))
    ==< +-right (sum-map-* k as) >
      (k * a) + (k * (sum as))
    ==< sym *-distrib-+-left >
      k * (sum (a :: as))
    end


  sum-cartesian-product : (a1 a2 : List Domain)
                          -> sum (cartesian-product' _*_ a1 a2)
                             == (sum a1) * (sum a2)
  sum-cartesian-product [] a2 = sym *-left-zero
  sum-cartesian-product (a :: a1) a2 =
    begin
      sum (cartesian-product' _*_ (a :: a1) a2)
    ==<>
      sum (map curry-* ((map (a ,_) a2) ++ (cartesian-product a1 a2)))
    ==< sum-map-inject-++ curry-* {map (a ,_) a2} >
      sum (map curry-* (map (a ,_) a2)) + (sum (cartesian-product' _*_ a1 a2))
    ==< +-right (sum-cartesian-product a1 a2) >
      sum (map curry-* (map (a ,_) a2)) + (sum a1) * (sum a2)
    ==< +-left (cong sum (double-map curry-* (a ,_) a2)) >
      sum (map (a *_) a2) + (sum a1) * (sum a2)
    ==< +-left (sum-map-* a a2) >
      a * (sum a2) + (sum a1) * (sum a2)
    ==< sym *-distrib-+-right >
      (sum (a :: a1)) * (sum a2)
    end
    where
    curry-* = \ (x , y) -> x * y


  product : List Domain -> Domain
  product = concat {{S.*-InfinityMonoid}}


  productʰ : InfinityMonoidʰᵉ ListInfinityMonoid S.*-InfinityMonoid product
  productʰ = concatʰ {{S.*-InfinityMonoid}}

  module productʰ where
    open InfinityMonoidʰ productʰ public
    preserves-* = preserves-∙

  product-inject-++ : {a b : List Domain} -> product (a ++ b) == product a * product b
  product-inject-++ {a} {b} = productʰ.preserves-* a b

  product-map-inject-++ : (f : A -> Domain) {a1 a2 : List A}
    -> (product (map f (a1 ++ a2))) == (product (map f a1)) * (product (map f a2))
  product-map-inject-++ f {a1} {a2} = InfinityMonoidʰ.preserves-∙ (productʰ infinity-monoid.∘ʰ (mapʰ f)) a1 a2

  product-map-Permutation : {as1 as2 : (List A)} -> (f : A -> Domain) -> (Permutation A as1 as2)
                            -> (product (map f as1)) == (product (map f as2))
  product-map-Permutation f (permutation-empty) = refl
  product-map-Permutation f (permutation-cons a p) =
    cong (f a *_) (product-map-Permutation f p)
  product-map-Permutation f (permutation-swap a b p) =
    sym (S.*-assoc {f a} {f b})
    >=> (*-left (S.*-commute {f a} {f b}))
    >=> (S.*-assoc {f b} {f a})
  product-map-Permutation f (permutation-compose p1 p2) =
    product-map-Permutation f p1 >=> product-map-Permutation f p2

-- Unordered sums/products
module _ where
  open unordered-list.base
  open unordered-list.operations
  open commutative-monoid

  unordered-sum : UList Domain -> Domain
  unordered-sum = concat {{S.+-CommMonoid}} S.isSet-Domain

  unordered-sumʰ : CommMonoidʰᵉ _ _ unordered-sum
  unordered-sumʰ = concatʰ {{S.+-CommMonoid}}

  unordered-product : UList Domain -> Domain
  unordered-product = concat {{S.*-CommMonoid}} S.isSet-Domain

  unordered-productʰ : CommMonoidʰᵉ _ _ unordered-product
  unordered-productʰ = concatʰ {{S.*-CommMonoid}}
