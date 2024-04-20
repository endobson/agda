{-# OPTIONS --cubical --safe --exact-split #-}

module ordered-ring.exponentiation.all-ones where

open import additive-group
open import additive-group.instances.nat
open import base
open import equality-path
open import finite-commutative-monoid
open import finite-commutative-monoid.small
open import finite-commutative-monoid.instances
open import finset.instances
open import finsum
open import finsum.order
open import funext
open import isomorphism
open import nat
open import nat.even-odd
open import order
open import ordered-additive-group
open import ordered-additive-group.negated
open import ordered-ring.exponentiation.poly-index
open import ordered-ring.exponentiation.poly-index.eval
open import ordered-ring.exponentiation.poly-index.ends
open import ordered-semiring
open import ordered-semiring.exponentiation
open import ordered-semiring.negated
open import ordered-semiring.squares
open import relation
open import ring.exponentiation
open import semiring
open import semiring.exponentiation
open import subset
open import subset.indicator
open import truncation

module _
  {ℓD ℓ< : Level} {D : Type ℓD} {D< : Rel D ℓ<} {LO : isLinearOrder D<}
  {ACM : AdditiveCommMonoid D} {S : Semiring ACM}
  {{AG : AdditiveGroup ACM}}
  {{LOA : LinearlyOrderedAdditiveStr ACM LO}}
  {{LOS : LinearlyOrderedSemiringStr S LO}}
  {{SOS : StronglyLinearlyOrderedSemiringStr S LO}}
  where
  private
    instance ILO = LO
    instance IAG = AG
    instance IACM = ACM
    instance IS = S
    CM = AdditiveCommMonoid.comm-monoid ACM
    instance
      PO = isLinearOrder->isPartialOrder-≯ LO
      CPO = CompatibleNegatedLinearOrder LO
      ITA = isLinearOrder->isTightApartness-<> LO
      POA = PartiallyOrderedAdditiveStr-Negated ACM LO
      POS = PartiallyOrderedSemiringStr-Negated S LO


  private
    EvenSubtype : Subtype Nat ℓ-zero
    EvenSubtype n = Even n , isProp-Even n

    DetEven : Detachable EvenSubtype
    DetEven zero = yes tt
    DetEven (suc zero) = no (\x -> x)
    DetEven (suc (suc n)) = DetEven n

    private
      iEven = indicator EvenSubtype DetEven
      iEven-=1 : (n : Nat) -> Even n -> iEven n == 1#
      iEven-=1 n e =
        proj₁ (∃!-prop (∃!indicator EvenSubtype DetEven)) (n , e)
      iEven-=0 : (n : Nat) -> ¬ (Even n) -> iEven n == 0#
      iEven-=0 n e =
        proj₂ (∃!-prop (∃!indicator EvenSubtype DetEven)) (n , e)
      iEven-=0' : (n : Nat) -> (Odd n) -> iEven n == 0#
      iEven-=0' n o = iEven-=0 n (Odd->¬Even n o)


    iEven-ss-path : (i : ℕ) -> iEven (suc (suc i)) == iEven i
    iEven-ss-path i = indicator-= (\x -> x) (\x -> x)


    alt-ones-pif : (n : Nat) -> (PolyIndex n -> D)
    alt-ones-pif n (i , j , p) = iEven i * iEven j


    shift-xy : {n : Nat} -> (PolyIndex n -> D) -> (PolyIndex (suc n) -> D)
    shift-xy f pi = shift₁ f pi + shift₂ f pi

    sum₁-pif : (n : Nat) -> (PolyIndex (suc n) -> D)
    sum₁-pif n = shift-xy (alt-ones-pif n)

    sum₁-pif-path : (n : Nat) (pi : PolyIndex (suc n)) ->
                    sum₁-pif n pi == iEven n
    sum₁-pif-path n (zero  , zero  , p) = bot-elim (zero-suc-absurd p)
    sum₁-pif-path n (zero  , suc j , p) =
      +-left-zero >=> *-left (indicator-=1 tt) >=>
      *-left-one >=> cong iEven (cong pred p)
    sum₁-pif-path n (suc i , zero  , p) =
      +-right-zero >=> *-right (indicator-=1 tt) >=>
      *-right-one >=> cong iEven (sym +-right-zero >=> cong pred p)
    sum₁-pif-path n pi@(suc i , suc j , p) = handle (DetEven i) (DetEven j)
      where
      check : sum₁-pif n pi == iEven i * iEven (suc j) +
                               iEven (suc i) * iEven j
      check = refl
      handle : (Dec (Even i)) -> (Dec (Even j)) -> sum₁-pif n pi == iEven n
      handle (yes ei) (yes ej) =
        +-left (*-right (iEven-=0' (suc j) ej) >=> *-right-zero) >=>
        +-left-zero >=>
        *-left (iEven-=0' (suc i) ei) >=>
        *-left-zero >=>
        sym (iEven-=0' (i + suc j) (Iso.inv (sum-Odd-iso i (suc j)) (inj-r (ei , ej)))) >=>
        cong iEven (cong pred p)
      handle (no ¬ei) (no ¬ej) =
        +-left (*-left (iEven-=0 i ¬ei) >=> *-left-zero) >=>
        +-left-zero >=>
        *-right (iEven-=0 j ¬ej) >=>
        *-right-zero >=>
        sym (iEven-=0' (i + suc j)
              (Iso.inv (sum-Odd-iso i (suc j)) (inj-l (¬Even->Odd i ¬ei , ¬Odd->Even (suc j) ¬ej)))) >=>
        cong iEven (cong pred p)
      handle (yes ei) (no ej) =
        +-left (*-right (iEven-=1 (suc j) (¬Even->Odd j ej)) >=> *-right-one >=>
                iEven-=1 i ei) >=>
        +-right (*-left (iEven-=0' (suc i) ei) >=> *-left-zero) >=>
        +-right-zero >=>
        sym (iEven-=1 (i + suc j) (Iso.inv (sum-Even-iso i (suc j)) (inj-l (ei , ¬Even->Odd j ej)))) >=>
        cong iEven (cong pred p)
      handle (no ei) (yes ej) =
        +-left (*-right (iEven-=0' (suc j) ej) >=> *-right-zero) >=>
        +-right (*-left (iEven-=1 (suc i) (¬Even->Odd i ei)) >=> *-left-one >=> (iEven-=1 j ej)) >=>
        +-left-zero >=>
        sym (iEven-=1 (i + suc j) (Iso.inv (sum-Even-iso i (suc j)) (inj-r (¬Even->Odd i ei , ej)))) >=>
        cong iEven (cong pred p)


    one-ends-pif : (n : Nat) -> (PolyIndex (suc (suc n)) -> D)
    one-ends-pif n = ends-pif (suc n) 1# 1#

    sum₂-pif : (n : Nat) -> (PolyIndex (suc (suc n)) -> D)
    sum₂-pif n pi = shift-xy (sum₁-pif n) pi + one-ends-pif n pi

    module _ (x : D) where
      0≤i*x^n : (n : Nat) -> 0# ≤ (iEven n * (x ^ℕ n))
      0≤i*x^n n = handle (DetEven n)
        where
        handle : Dec (Even n) -> _
        handle (yes even-n) =
          trans-≤-= (^ℕ-even-0≤ x n even-n)
            (sym *-left-one >=> *-left (sym (indicator-=1 even-n)))
        handle (no ¬even-n) =
          path-≤ (sym *-left-zero >=> *-left (sym (indicator-=0 ¬even-n)))

    module _ (n : Nat) (en : Even n) where
      sum₂-pif-path : (pi : PolyIndex (suc (suc n))) -> sum₂-pif n pi == (1# + 1#)
      sum₂-pif-path    (zero  , zero  , p) = bot-elim (zero-suc-absurd p)
      sum₂-pif-path pi@(zero  , suc j , p) =
        +-left (+-left-zero >=> sum₁-pif-path n (zero , j , _) >=> indicator-=1 en)
      sum₂-pif-path pi@(suc i , zero  , p) =
        +-left (+-right-zero >=> sum₁-pif-path n (i , zero , _) >=> indicator-=1 en)
      sum₂-pif-path pi@(suc i , suc j , p) =
        +-right-zero >=> (+-cong (sum₁-pif-path n (i , (suc j) , _) >=> indicator-=1 en)
                                 (sum₁-pif-path n ((suc i) , j , _) >=> indicator-=1 en))


    module _ (x y : D) where
      eval-all-ones-zero : finiteSum (eval-PI x y (all-ones-pif 0)) == 1#
      eval-all-ones-zero =
        finiteMerge-convert-iso CM (iso⁻¹ PolyIndex<->Fin) _ >=>
        finiteMerge-Fin1 CM _ >=>
        *-left-one >=> *-left-one


    module _ (x y : D) where
      module _ (n : Nat) where
        one-ends-eval-path : finiteSum (eval-PI x y (one-ends-pif n)) ==
                             ((y ^ℕ (suc (suc n))) + (x ^ℕ (suc (suc n))))
        one-ends-eval-path =
          ends-eval-path (suc n) 1# 1# x y >=>
          +-cong *-left-one *-left-one

      eval-alt-ones-pif-0≤ : {n : Nat} -> 0# ≤ finiteSum (eval-PI x y (alt-ones-pif n))
      eval-alt-ones-pif-0≤ {n} = finiteSum-preserves-0≤ lt
        where
        lt : (pi : PolyIndex n) -> 0# ≤ (eval-PI x y (alt-ones-pif n) pi)
        lt (i , j , p) = trans-≤-= (*-preserves-0≤ (0≤i*x^n x i) (0≤i*x^n y j)) *-swap


      module _ (n : Nat) (en : Even n)
               (0<powers : 0# < ((y ^ℕ (suc (suc n))) + (x ^ℕ (suc (suc n)))))
        where

        eval-one-ends-0< : 0# < finiteSum (eval-PI x y (one-ends-pif n))
        eval-one-ends-0< = trans-<-= 0<powers (sym (one-ends-eval-path n))

        shift-xy-eval-path : {n : Nat} -> (f : PolyIndex n -> D) ->
                             finiteSum (eval-PI x y (shift-xy f)) ==
                             (x + y) * finiteSum (eval-PI x y f)
        shift-xy-eval-path {n} f =
          cong finiteSum (eval-+-path x y (suc n) (shift₁ f) (shift₂ f)) >=>
          finiteMerge-split CM >=>
          +-cong (shift₁-eval-path x y f) (shift₂-eval-path x y f) >=>
          sym *-distrib-+-right

        sum₂-pif-eval-path :
          finiteSum (eval-PI x y (sum₂-pif n)) ==
            ((x + y) * (x + y)) * finiteSum (eval-PI x y (alt-ones-pif n)) +
            finiteSum (eval-PI x y (one-ends-pif n))
        sum₂-pif-eval-path =
          cong finiteSum (eval-+-path x y _ _ _) >=>
          finiteMerge-split CM >=>
          +-left (shift-xy-eval-path (sum₁-pif n) >=>
                  *-right (shift-xy-eval-path (alt-ones-pif n)) >=>
                  sym *-assoc)

        sum₂-pif-one-path :
          finiteSum (eval-PI x y (sum₂-pif n)) ==
          finiteSum (eval-PI x y (all-ones-pif (suc (suc n)))) +
          finiteSum (eval-PI x y (all-ones-pif (suc (suc n))))
        sum₂-pif-one-path =
          cong finiteSum (
            cong (eval-PI x y) (funExt (\pi -> sum₂-pif-path n en pi)) >=>
            (eval-+-path x y _ _ _)) >=>
          finiteMerge-split CM


        eval-sum₂-pif-0< : 0# < finiteSum (eval-PI x y (sum₂-pif n))
        eval-sum₂-pif-0< =
          trans-<-=
            (trans-<-≤
              (trans-<-= eval-one-ends-0< (sym +-left-zero))
              (+₂-preserves-≤ (*-preserves-0≤ square-≮0 eval-alt-ones-pif-0≤)))
            (sym sum₂-pif-eval-path)

        all-ones-pif-0< : 0# < finiteSum (eval-PI x y (all-ones-pif (suc (suc n))))
        all-ones-pif-0< =
          unsquash isProp-< (∥-map handle (+-reflects-0< (trans-<-= eval-sum₂-pif-0< sum₂-pif-one-path)))
          where
          handle : _ -> _
          handle (inj-l lt) = lt
          handle (inj-r lt) = lt

  all-ones-eval-0< :
    (x y : D) (n : Nat)
    (0<powers : 0# < ((y ^ℕ n) + ((- x) ^ℕ n)))
    (en : Even n) ->
    0# < finiteSum (eval-PI x y (all-ones-pif n))
  all-ones-eval-0< x y (suc (suc n)) 0<powers en =
    all-ones-pif-0< x y n en (trans-<-= 0<powers (+-right (minus-^ℕ-even x (suc (suc n)) en)))
  all-ones-eval-0< x y zero 0<powers _ =
    trans-<-= 0<1 (sym (eval-all-ones-zero x y))
    where
    0<1 : 0# < 1#
    0<1 = unsquash isProp-< (∥-map handle (+-reflects-0< 0<powers))
      where
      handle : (0# < 1#) ⊎ (0# < 1#) -> 0# < 1#
      handle (inj-l lt) = lt
      handle (inj-r lt) = lt
