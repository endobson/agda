{-# OPTIONS --cubical --safe --exact-split #-}

module additive-group.instances.int where

open import additive-group
open import base
open import equality-path
open import int.add1
open import int.addition
open import int.base
open import int.cover
open import int.elimination

private
  ℤ+-assoc : (m n o : Int) -> (m ℤ+ n) ℤ+ o == m ℤ+ (n ℤ+ o)
  ℤ+-assoc m n o =
    IntElim-add1sub1-elim {P = \m -> (m ℤ+ n) ℤ+ o == m ℤ+ (n ℤ+ o)}
      (ℤ+-left (ℤ+-left-zero _) >=> sym (ℤ+-left-zero _))
      (\m p -> ℤ+-left add1-extract-left >=>
               add1-extract-left >=>
               cong add1 p >=>
               sym add1-extract-left)
      (\m p -> ℤ+-left sub1-extract-left >=>
               sub1-extract-left >=>
               cong sub1 p >=>
               sym sub1-extract-left)
      m

  ℤ+-commute : {m n : Int} -> (m ℤ+ n) == (n ℤ+ m)
  ℤ+-commute {m} {n} =
    IntElim-add1sub1-elim {P = \m -> (m ℤ+ n) == (n ℤ+ m)}
      (ℤ+-left-zero _ >=> sym (ℤ+-right-zero _))
      (\m p -> add1-extract-left >=> cong add1 p >=> sym add1-extract-right)
      (\m p -> sub1-extract-left >=> cong sub1 p >=> sym sub1-extract-right)
      m


add-minus-zero : {n : Int} -> n ℤ+ (ℤ- n) == zero-int
add-minus-zero {n} =
  IntElim-add1sub1-elim {P = \n -> (n ℤ+ (ℤ- n)) == zero-int }
    (ℤ+-left-zero _)
    (\n p -> add1-extract-left >=>
             cong add1 (ℤ+-right (sym sub1-minus->minus-add1) >=>
                        sub1-extract-right) >=>
             add1-sub1-id >=> p)
    (\n p -> sub1-extract-left >=>
             cong sub1 (ℤ+-right (sym add1-minus->minus-sub1) >=>
                        add1-extract-right) >=>
             sub1-add1-id >=> p)
    n

instance
  AdditiveCommMonoid-Int : AdditiveCommMonoid Int
  AdditiveCommMonoid-Int = record
    { comm-monoid = record
      { monoid = record
        { ε = (int 0)
        ; _∙_ = _ℤ+_
        ; ∙-assoc = ℤ+-assoc _ _ _
        ; ∙-left-ε = ℤ+-left-zero _
        ; ∙-right-ε = ℤ+-right-zero _
        ; isSet-Domain = isSetInt
        }
      ; ∙-commute = ℤ+-commute
      }
    }

  AdditiveGroup-Int : AdditiveGroup AdditiveCommMonoid-Int
  AdditiveGroup-Int = record
    { -_ = ℤ-_
    ; +-inverse = add-minus-zero
    }
