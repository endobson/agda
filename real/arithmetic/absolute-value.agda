{-# OPTIONS --cubical --safe --exact-split #-}

module real.arithmetic.absolute-value where

open import base
open import equality
open import hlevel
open import order
open import order.instances.rational
open import sign
open import sign.instances.rational
open import rational
open import rational.order hiding (_<_ ; _>_ ; irrefl-< ; trans-<)
open import real
open import real.sequence
open import relation hiding (U)
open import ring
open import ring.implementations.rational
open import truncation

module _ (x : ℝ)
  where
  private
    module x = Real x

    L' : Pred ℚ ℓ-zero
    L' q = (x.L q) ⊎ (x.U (r- q))

    L : Pred ℚ ℓ-zero
    L q = ∥ L' q ∥

    U : Pred ℚ ℓ-zero
    U q = (x.L (r- q)) × (x.U q)

    isProp-L : (q : ℚ) -> isProp (L q)
    isProp-L _ = squash

    isProp-U : (q : ℚ) -> isProp (U q)
    isProp-U q (l1 , u1) (l2 , u2) i =
      (x.isProp-L (r- q) l1 l2 i) , (x.isProp-U q u1 u2 i)

    L-neg : (q : ℚ⁻) -> L ⟨ q ⟩
    L-neg (q , nq) = x.located q (r- q) q<-q
      where
      pmq : Pos (r- q)
      pmq = r--flips-sign _ _ nq

      q<-q : q < (r- q)
      q<-q = r+-preserves-Pos _ _ pmq pmq

    Inhabited-L : Inhabited L
    Inhabited-L = ∣ (r- 1r) , L-neg (_ , r--flips-sign _ _ Pos-1r) ∣

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-map2 handle (ℝ->Neg-L x) (ℝ->Pos-U x)
      where
      handle : Σ[ q ∈ ℚ⁻ ] (x.L ⟨ q ⟩) -> Σ[ r ∈ ℚ⁺ ] (x.U ⟨ r ⟩) -> Σ ℚ U
      handle (q⁻@(q , _) , xl-q) (r⁺@(r , _) , xu-r) = handle2 (trichotomous-< q (r- r))
        where
        handle2 : Tri (q < (r- r)) (q == (r- r)) ((r- r) < q) -> Σ ℚ U
        handle2 (tri< q<-r _ _) =
          (r- q) , (subst x.L (sym minus-double-inverse) xl-q) ,
                   (x.isUpperSet-U r (r- q) r<-q xu-r)
          where
          r<-q : r < (r- q)
          r<-q = subst Pos (r+-commute (r- r) (r- q)) q<-r
        handle2 (tri= _ q=-r _ ) = r , (subst x.L q=-r xl-q) , xu-r
        handle2 (tri> _ _ -r<q) = r , (x.isLowerSet-L (r- r) q -r<q xl-q) , xu-r

    isLowerSet-L : isLowerSet L
    isLowerSet-L q r q<r = ∥-map handle
      where
      handle : L' r -> L' q
      handle (inj-l xl-r) = inj-l (x.isLowerSet-L q r q<r xl-r)
      handle (inj-r xu-r) = inj-r (x.isUpperSet-U (r- r) (r- q) (r--flips-order q r q<r) xu-r)

    isUpperSet-U : isUpperSet U
    isUpperSet-U q r q<r (xl-q , xu-q) =
      (x.isLowerSet-L (r- r) (r- q) (r--flips-order q r q<r) xl-q) ,
      (x.isUpperSet-U q r q<r xu-q)

    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q = ∥-bind handle
      where
      handle : L' q -> ∃[ r ∈ ℚ ] (q < r × L r)
      handle (inj-l xl-q) = ∥-map (\ (r , lt , l) -> r , lt , ∣ (inj-l l) ∣) (x.isUpperOpen-L q xl-q)
      handle (inj-r xu-q) = ∥-map handle2 (x.isLowerOpen-U (r- q) xu-q)
        where
        handle2 : Σ[ r ∈ ℚ ] (r < (r- q) × x.U r ) -> Σ[ r ∈ ℚ ] (q < r × L r)
        handle2 (r , lt , xu-r) =
          (r- r) , subst Pos (r+-commute (r- q) (r- r)) lt
                 , ∣ inj-r (subst x.U (sym minus-double-inverse) xu-r) ∣


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q (xl-q , xu-q) =
      ∥-map2 handle (x.isUpperOpen-L (r- q) xl-q) (x.isLowerOpen-U q xu-q)
      where
      handle : Σ[ r1 ∈ ℚ ] ((r- q) < r1 × x.L r1) -> Σ[ r2 ∈ ℚ ] (r2 < q × x.U r2) ->
               Σ[ r3 ∈ ℚ ] (r3 < q × U r3)
      handle (r1 , -q<r1 , xl-r1) (r2 , r2<q , xu-r2) = handle2 (trichotomous-< r1 (r- r2))
        where
        handle2 : Tri (r1 < (r- r2)) (r1 == (r- r2)) ((r- r2) < r1) ->
                  Σ[ r3 ∈ ℚ ] (r3 < q × U r3)
        handle2 (tri< r1<-r2 _ _) =
          (r- r1) , -r1<q , (subst x.L (sym minus-double-inverse) xl-r1) ,
                            (x.isUpperSet-U r2 (r- r1) r2<-r1 xu-r2)
          where
          r2<-r1 : r2 < (r- r1)
          r2<-r1 = subst Pos (r+-commute (r- r2) (r- r1)) r1<-r2

          -r1<q : (r- r1) < q
          -r1<q = subst ((r- r1) <_) minus-double-inverse
                        (r--flips-order (r- q) r1 -q<r1)

        handle2 (tri= _ r1=-r2 _) =
          r2 , r2<q , (subst x.L r1=-r2 xl-r1) , xu-r2
        handle2 (tri> _ _ -r2<r1) =
          r2 , r2<q , (x.isLowerSet-L (r- r2) r1 -r2<r1 xl-r1) , xu-r2


    disjoint : Universal (Comp (L ∩ U))
    disjoint q (l , (xl-mq , xu-q)) = unsquash isPropBot (∥-map handle l)
      where
      handle : (x.L q ⊎ x.U (r- q)) -> Bot
      handle (inj-l xl-q) = x.disjoint q (xl-q , xu-q)
      handle (inj-r xu-mq) = x.disjoint (r- q) (xl-mq , xu-mq)


    located : (q r : ℚ) -> (q < r) -> ∥ L q ⊎ U r ∥
    located q r q<r =  ∥-map2 handle (x.located q r q<r)
                                     (x.located (r- r) (r- q) (r--flips-order q r q<r))
      where
      handle : (x.L q ⊎ x.U r) -> (x.L (r- r) ⊎ x.U (r- q)) -> L q ⊎ U r
      handle (inj-l xl-q) _ = inj-l (∣ (inj-l xl-q) ∣)
      handle (inj-r xu-r) (inj-r xu-mq) = inj-l (∣ (inj-r xu-mq) ∣)
      handle (inj-r xu-r) (inj-l xl-mr) = inj-r (xl-mr , xu-r)

  absℝ : ℝ
  absℝ = record
    { L = L
    ; U = U
    ; isProp-L = isProp-L
    ; isProp-U = isProp-U
    ; Inhabited-L = Inhabited-L
    ; Inhabited-U = Inhabited-U
    ; isLowerSet-L = isLowerSet-L
    ; isUpperSet-U = isUpperSet-U
    ; isUpperOpen-L = isUpperOpen-L
    ; isLowerOpen-U = isLowerOpen-U
    ; disjoint = disjoint
    ; located = located
    }
