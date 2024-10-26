{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-additive-group.bound where

open import additive-group
open import base
open import equality-path
open import functions
open import order
open import order.bound
open import ordered-additive-group
open import relation
open import truncation

private
  variable
    ℓI ℓD ℓ< : Level
    I : Type ℓI


module _ {D : Type ℓD} {D< : Rel D ℓ<} {{LO : isLinearOrder D<}}
         {{ACM : AdditiveCommMonoid D}}
         {{AG : AdditiveGroup ACM}}
         {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
         where
  opaque
    minus-flips-isInfimum : {f : I -> D} {v : D} -> isInfimum f v -> isSupremum (-_ ∘ f) (- v)
    minus-flips-isInfimum {I = I} {f = f} {v} (close , below) = close' , above
      where
      close' : ∀ v2 -> v2 < (- v) -> ∃[ i ∈ I ] (v2 < (- f i))
      close' v2 v2<-v =
        ∥-map (\ (i , fi<-v2) -> i , trans-=-< (sym minus-double-inverse) (minus-flips-< fi<-v2))
              (close (- v2) v<-v2)
        where
        v<-v2 : v < (- v2)
        v<-v2 = trans-=-< (sym minus-double-inverse) (minus-flips-< v2<-v)

      above : ∀ i v2 -> v2 < (- f i) -> v2 < (- v)
      above i v2 v2<-fi = trans-=-< (sym minus-double-inverse) (minus-flips-< (below i (- v2) fi<-v2))
        where
        fi<-v2 : f i < (- v2)
        fi<-v2 = trans-=-< (sym minus-double-inverse) (minus-flips-< v2<-fi)

    minus-flips-isSupremum : {f : I -> D} {v : D} -> isSupremum f v -> isInfimum (-_ ∘ f) (- v)
    minus-flips-isSupremum {I = I} {f = f} {v} (close , above) = close' , below
      where
      close' : ∀ v2 -> (- v) < v2 -> ∃[ i ∈ I ] ((- f i) < v2)
      close' v2 -v<v2 =
        ∥-map (\ (i , -v2<fi) -> i , trans-<-= (minus-flips-< -v2<fi) minus-double-inverse)
              (close (- v2) -v2<v)
        where
        -v2<v : (- v2) < v
        -v2<v = trans-<-= (minus-flips-< -v<v2) minus-double-inverse

      below : ∀ i v2 -> (- f i) < v2 -> (- v) < v2
      below i v2 -fi<v2 = trans-<-= (minus-flips-< (above i (- v2) -v2<fi)) minus-double-inverse
        where
        -v2<fi : (- v2) < f i
        -v2<fi = trans-<-= (minus-flips-< -fi<v2) minus-double-inverse
