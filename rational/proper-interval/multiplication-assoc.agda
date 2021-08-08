{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.multiplication-assoc where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import rational
open import rational.minmax
open import rational.proper-interval
open import relation hiding (_⊆_)
open import ring.implementations.rational
open import sign
open import sign.instances.rational
open import truncation

private
  i∪-swap : (a b c d : Iℚ) -> (a i∪ b) i∪ (c i∪ d) == (a i∪ c) i∪ (b i∪ d)
  i∪-swap a b c d =
    i∪-assoc a b (c i∪ d) >=>
    cong (a i∪_) (sym (i∪-assoc b c d) >=> (cong (_i∪ d) (i∪-commute b c)) >=>
                  (i∪-assoc c b d)) >=>
    sym (i∪-assoc a c (b i∪ d))

  i*-assoc' : (a b c : Iℚ) -> a i* (b i* c) == b i* (a i* c)
  i*-assoc' a@(Iℚ-cons al au al≤au) b@(Iℚ-cons bl bu bl≤bu) c = p5
    where
    p1 : i-scale al (b i* c) == (i-scale (bl r* al) c) i∪ (i-scale (bu r* al) c)
    p1 = i-scale-distrib-∪ al (i-scale bl c) (i-scale bu c) >=>
         cong2 _i∪_ (i-scale-twice al bl c >=> cong (\x -> i-scale x c) (r*-commute al bl))
                    (i-scale-twice al bu c >=> cong (\x -> i-scale x c) (r*-commute al bu))

    p2 : i-scale au (b i* c) == (i-scale (bl r* au) c) i∪ (i-scale (bu r* au) c)
    p2 = i-scale-distrib-∪ au (i-scale bl c) (i-scale bu c) >=>
         cong2 _i∪_ (i-scale-twice au bl c >=> cong (\x -> i-scale x c) (r*-commute au bl))
                    (i-scale-twice au bu c >=> cong (\x -> i-scale x c) (r*-commute au bu))

    p3 : i-scale bl (a i* c) == (i-scale (bl r* al) c) i∪ (i-scale (bl r* au) c)
    p3 = i-scale-distrib-∪ bl (i-scale al c) (i-scale au c) >=>
         cong2 _i∪_ (i-scale-twice bl al c) (i-scale-twice bl au c)

    p4 : i-scale bu (a i* c) == (i-scale (bu r* al) c) i∪ (i-scale (bu r* au) c)
    p4 = i-scale-distrib-∪ bu (i-scale al c) (i-scale au c) >=>
         cong2 _i∪_ (i-scale-twice bu al c)
                    (i-scale-twice bu au c)


    p5 : a i* (b i* c) == b i* (a i* c)
    p5 = cong2 _i∪_ p1 p2 >=>
         i∪-swap (i-scale (bl r* al) c) (i-scale (bu r* al) c)
                 (i-scale (bl r* au) c) (i-scale (bu r* au) c) >=>
         sym (cong2 _i∪_ p3 p4)

abstract
  i*-assoc : (a b c : Iℚ) -> a i* (b i* c) == (a i* b) i* c
  i*-assoc a b c =
    cong (a i*_) (i*-commute b c) >=>
    i*-assoc' a c b >=>
    i*-commute c (a i* b)
