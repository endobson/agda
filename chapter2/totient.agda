{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.totient where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.modular-integers
open import additive-group.instances.nat
open import base
open import chapter2.divisors
open import chapter2.multiplicative
open import decision
open import div hiding (remainder)
open import equality
open import equivalence
open import fin
open import fin-algebra
open import finset
open import finset.cardinality
open import finset.instances
open import finset.instances.base
open import finset.instances.sigma
open import finset.subset
open import finsum
open import finsum.arithmetic
open import finsum.cardinality
open import gcd.computational
open import gcd.euclidean-algorithm
open import gcd.propositional hiding (gcd'-unique)
open import hlevel.base
open import hlevel.htype
open import hlevel.sigma
open import int.base
open import isomorphism
open import linear-combo
open import modular-integers
open import modular-integers.binary-product
open import modular-integers.representative
open import nat
open import nat.bounded
open import nat.order
open import order
open import order.instances.nat
open import ordered-additive-group
open import ordered-additive-group.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import prime
open import prime-gcd
open import quotient-remainder
open import relation
open import relatively-prime
open import ring.implementations.int
open import semiring
open import semiring.exponentiation
open import semiring.initial
open import semiring.instances.modular-integers
open import semiring.instances.nat
open import semiring.unit
open import set-quotient
open import sigma
open import sigma.base
open import truncation
open import type-algebra
open import univalence

open EqReasoning

private
  module _ (n⁺@(n , pos-n) : Nat⁺) where
    CoprimeN' : (x : ℤ/nℤ n) -> hProp ℓ-zero
    CoprimeN' = SetQuotientElim.rec isSet-hProp
                  (\ x -> RelativelyPrime (int n) x , isProp-RelativelyPrime)
                  (\ x y r -> ΣProp-path isProp-isProp (rp-eq x y r))
      where
      opaque
        rp-f : (x y : ℤ) -> (ℤ/nℤ~ n x y) -> RelativelyPrime (int n) x -> RelativelyPrime (int n) y
        rp-f x y n%xy rp-x d nn-d d%n d%y = rp-x d nn-d d%n d%x
          where
          d%xyy : d div (y + (- (diff x y)))
          d%xyy = div-sum d%y (div-negate⁺ (div-trans d%n n%xy))
          d%x : d div x
          d%x = subst (d div_) (+-right (sym diff-anticommute) >=> diff-step) d%xyy


        rp-eq : (x y : ℤ) -> (ℤ/nℤ~ n x y) -> RelativelyPrime (int n) x == RelativelyPrime (int n) y
        rp-eq x y r = ua (isoToEquiv i)
          where
          open Iso
          i : Iso (RelativelyPrime (int n) x) (RelativelyPrime (int n) y)
          i .fun = rp-f x y r
          i .inv = rp-f y x (isEquivRel.symmetric isEquivRel-ℤ/nℤ~ r)
          i .rightInv _ = isProp-RelativelyPrime _ _
          i .leftInv _ = isProp-RelativelyPrime _ _

    CoprimeN : (x : ℤ/nℤ n) -> Type₀
    CoprimeN x = fst (CoprimeN' x)
    isProp-CoprimeN : {x : ℤ/nℤ n} -> isProp (CoprimeN x)
    isProp-CoprimeN {x} = snd (CoprimeN' x)

    opaque
      unit->coprime' : (x y : ℤ/nℤ n) -> (x * y == 1#) -> (CoprimeN x)
      unit->coprime' = SetQuotientElim.elimProp2 (\x y -> (isPropΠ (\_ -> isProp-CoprimeN {x}))) handle
        where
        module _ where
          handle : (x y : ℤ) -> ([ x * y ] == 1#) -> (CoprimeN [ x ])
          handle x y p d nn-d d%n d%x = div-one->one nn-d d%1
            where
            c : ℤ/nℤ~ n (x * y) (int 1)
            c = SetQuotientElim.pathRec (isProp-ℤ/nℤ~ n⁺) isEquivRel-ℤ/nℤ~ _ _ p

            d%1-xy : d div (diff (x * y) (int 1))
            d%1-xy = div-trans d%n c

            d%xy : d div (x * y)
            d%xy = div-mult' d%x y

            d%1 : d div (int 1)
            d%1 = subst (d div_) diff-step (div-sum d%xy d%1-xy)

      is-unit->coprime : (x : ℤ/nℤ n) -> (isUnit x) -> (CoprimeN x)
      is-unit->coprime x (is-unit y p) = unit->coprime' x y p

      coprime->is-unit : (x : ℤ/nℤ n) -> (CoprimeN x) -> (isUnit x)
      coprime->is-unit = SetQuotientElim.elimProp (\x -> (isPropΠ (\_ -> isProp-isUnit))) handle
        where
        module _ where
          lc->is-unit : {x : ℤ} -> LinearCombination (int n) x (int 1) -> isUnit [ x ]
          lc->is-unit {x} lc = is-unit [ y ] (eq/ (x * y) (int 1) (lc.x , path))
            where
            module lc = LinearCombination lc
            y : Int
            y = lc.y

            path : lc.x * (int n) == diff (x * lc.y) (int 1)
            path = sym +-right-zero >=> +-right (sym +-inverse) >=>
                   sym +-assoc >=> +-left lc.path >=> +-right (cong -_ *-commute)

          handle : (x : ℤ) -> (RelativelyPrime (int n) x) -> (isUnit [ x ])
          handle x rp = lc->is-unit (gcd->linear-combo (relatively-prime->gcdⁱ rp))

    Unit-CoprimeN-eq : (x : ℤ/nℤ n) -> (isUnit x) ≃ (CoprimeN x)
    Unit-CoprimeN-eq x = isoToEquiv i
      where
      open Iso
      i : Iso (isUnit x) (CoprimeN x)
      i .fun = is-unit->coprime x
      i .inv = coprime->is-unit x
      i .rightInv c = isProp-CoprimeN {x} _ c
      i .leftInv u = isProp-isUnit _ u


record Totient (n : Nat) (k : Nat) : Type₀ where
  field
    pos-k : Pos' k
    k≤n : k ≤ n
    rp : RelativelyPrime⁰ k n

  k<n : n > 1 -> k < n
  k<n n>1 = strengthen-≤ k≤n k!=n
    where
    k!=n : k != n
    k!=n k==n = <->!= n>1 (sym (rp n (transport (\i -> (k==n i) div' k) div'-refl) div'-refl))

isTotativeOf : Nat -> Nat -> Type₀
isTotativeOf = Totient

isProp-isTotativeOf : {n k : Nat} -> isProp (isTotativeOf n k)
isProp-isTotativeOf t1 t2 i = record
  { pos-k = isPropPos' (t1 .Totient.pos-k) (t2 .Totient.pos-k) i
  ; k≤n = isProp-≤ (t1 .Totient.k≤n) (t2 .Totient.k≤n) i
  ; rp = isPropΠ3 (\ _ _ _ -> isSetNat _ _) (t1 .Totient.rp) (t2 .Totient.rp) i
  }

isBoundedTotient : {n : Nat} -> isBounded (Totient n)
isBoundedTotient {n} = (suc n) , (\ t -> trans-≤-< (Totient.k≤n t) refl-≤)

decide-rp : (k n : Nat) -> Dec (RelativelyPrime⁰ k n)
decide-rp k n = handle (decide-nat (gcd' k n) 1)
  where
  handle : Dec ((gcd' k n) == 1) -> Dec (RelativelyPrime⁰ k n)
  handle (no ¬p) = no (\ rp -> ¬p (gcd'-unique (relatively-prime->gcd rp)))
  handle (yes p) = yes (gcd->relatively-prime (transport (cong (GCD' k n) p) (gcd'-proof k n)))


decide-totient : (n k : Nat) -> Dec (Totient n k)
decide-totient n zero      = no (\ t -> (Totient.pos-k t))
decide-totient n k@(suc _) = handle (decide-nat≤ k n) (decide-rp k n)
  where
  handle : Dec (k ≤ n) -> Dec (RelativelyPrime⁰ k n) -> Dec (Totient n k)
  handle (no ¬k≤n) _        = no (\ t -> ¬k≤n (Totient.k≤n t))
  handle (yes k≤n) (no ¬rp) = no (\ t -> ¬rp (Totient.rp t))
  handle (yes k≤n) (yes rp) = yes (record { k≤n = k≤n ; rp = rp })

Totatives : Nat -> Type₀
Totatives n = Σ Nat (isTotativeOf n)

abstract
  isFinSet-Totatives : {n : Nat} -> isFinSet (Totatives n)
  isFinSet-Totatives {n} =
    boundedDecidableProp->isFinSet isBoundedTotient (decide-totient n) isProp-isTotativeOf

FinSet-Totatives : Nat -> FinSet ℓ-zero
FinSet-Totatives n = Totatives n , isFinSet-Totatives

φ : Nat⁺ -> Nat
φ (n , _) = cardinality (FinSet-Totatives n)

private
  totient-one-one : (Totient 1 1)
  totient-one-one = record
    { k≤n = refl-≤
    ; rp = rp-one
    }

  totatives-one-eq : Totatives 1 ≃ Top
  totatives-one-eq = isoToEquiv i
    where
    open Iso
    i : Iso (Totatives 1) Top
    i .fun _ = tt
    i .inv _ = 1 , totient-one-one
    i .rightInv tt = refl
    i .leftInv (x , tot) = (ΣProp-path isProp-isTotativeOf path)
      where
      path : 1 == x
      path = antisym-≤ (Pos'->< (Totient.pos-k tot)) (Totient.k≤n tot)

φ-one : φ 1⁺ == 1
φ-one = cong cardinality path >=> cardinality-path FinSet-Top top-finΣ
  where
  path : (Totatives 1 , isFinSet-Totatives) == FinSet-Top
  path = (ΣProp-path isProp-isFinSet (ua totatives-one-eq))

  top-finΣ : isFinSetΣ Top
  top-finΣ = 1 , ∣ equiv⁻¹ Fin-Top-eq ∣



module _ (p : Prime') where
  private
    p' = ⟨ p ⟩
    p⁺ = Prime'.nat⁺ p

    totient-prime : {k : Nat} -> Pos' k -> k < p' -> Totient p' k
    totient-prime {k} pos-k k<p = record
      { k≤n = weaken-< k<p
      ; pos-k = pos-k
      ; rp = rp
      }
      where
      ¬p%k : ¬(p' div' k)
      ¬p%k p%k = irrefl-< (trans-<-≤ k<p (div'->≤ p%k {pos-k}))

      rp : RelativelyPrime⁰ k p'
      rp = rp-sym (prime->relatively-prime p ¬p%k)


    Fin1 : Nat -> Type₀
    Fin1 n = Σ[ i ∈ Nat⁺ ] (⟨ i ⟩ ≤ n)

    Fin1-Fin-eq : {n : Nat} -> Fin1 n ≃ Fin n
    Fin1-Fin-eq {n} = isoToEquiv i
      where
      open Iso
      i : Iso (Fin1 n) (Fin n)
      i .fun ((zero  , ()) , _)
      i .fun ((suc j , _) , lt) = j , lt
      i .inv (j , lt) = (suc j , tt) , lt
      i .rightInv _ = refl
      i .leftInv ((zero  , ()) , _)
      i .leftInv ((suc j , tt) , lt) = refl

    totatives-prime-eq : Totatives p' ≃ Fin1 (pred p')
    totatives-prime-eq = isoToEquiv i
      where
      open Iso
      i : Iso (Totatives p') (Fin1 (pred p'))
      i .fun (x , t) = ((x , Totient.pos-k t) , pred-≤ (Totient.k<n t (Prime'.>1 p)))
      i .inv ((x , pos-x) , lt) = x , totient-prime pos-x (pos-pred-≤ (Prime'.pos p) lt)
      i .rightInv _ = ΣProp-path isProp-≤ (ΣProp-path isPropPos' refl)
      i .leftInv _ = ΣProp-path isProp-isTotativeOf refl


  φ-prime : φ p⁺ == (pred p')
  φ-prime = cong cardinality path >=> cardinality-path (FinSet-Fin (pred p')) finΣ
    where
    path : (Totatives p' , isFinSet-Totatives) == FinSet-Fin (pred p')
    path = (ΣProp-path isProp-isFinSet (ua totatives-prime-eq >=> ua Fin1-Fin-eq))

    finΣ : isFinSetΣ (Fin (pred p'))
    finΣ = (pred p') , ∣ idEquiv _ ∣




  private
    is-totative-of-prime-power :
      {k : Nat} (n : Nat⁺) (i : Fin p') ->
      Totient (prime-power p ⟨ n ⟩) k ->
      Totient (prime-power p (suc ⟨ n ⟩)) ((Fin.i i *' (prime-power p ⟨ n ⟩)) +' k)
    is-totative-of-prime-power {k} n⁺@(n@(suc n-1) , _) (i , i<p) t = record
      { pos-k = pos-ipnk
      ; k≤n = ipnk≤psn
      ; rp = rp
      }
      where
      pos-ipnk : Pos' ((i *' prime-power p n) +' k)
      pos-ipnk = +'-Pos-right (Totient.pos-k t)

      prime-power≥prime : (prime-power p n) ≥ p'
      prime-power≥prime = div'->≤ (prime-power-div p n⁺) {snd (prime-power⁺ p n)}

      i<p-check : i < p'
      i<p-check = i<p
      pn>1 : (prime-power p n) > 1
      pn>1 = trans-≤ (Prime'.>1 p) prime-power≥prime
      i≤p : i ≤ pred p'
      i≤p = pred-≤ i<p
      ipn≤ppn : (i *' prime-power p n) ≤ (pred p' *' (prime-power p n))
      ipn≤ppn = *₂-preserves-≤ i≤p zero-≤

      k≤pn : k ≤ (prime-power p n)
      k≤pn = Totient.k≤n t

      k<pn : k < (prime-power p n)
      k<pn = Totient.k<n t pn>1

      ipnk≤ppnpn : ((i *' prime-power p n) +' k) ≤ (pred p' *' (prime-power p n) +' (prime-power p n))
      ipnk≤ppnpn = +-preserves-≤ ipn≤ppn k≤pn

      kipn<pnppn : (k +' (i *' prime-power p n)) < ((prime-power p n) +' pred p' *' (prime-power p n))
      kipn<pnppn = +-preserves-≤ k<pn ipn≤ppn


      suc-pred-path : (n : Nat⁺) -> suc (pred ⟨ n ⟩) == ⟨ n ⟩
      suc-pred-path (suc _ , _) = refl

      ppnpn==psn : (pred p' *' (prime-power p n) +' (prime-power p n)) == prime-power p (suc n)
      ppnpn==psn = +'-commute {_} {prime-power p n}
                   >=> (cong (_*' (prime-power p n)) (suc-pred-path (Prime'.nat⁺ p)))

      pnppn==psn : (prime-power p n) +' (pred p' *' (prime-power p n)) == prime-power p (suc n)
      pnppn==psn = (cong (_*' (prime-power p n)) (suc-pred-path (Prime'.nat⁺ p)))


      ipnk≤psn : ((i *' (prime-power p n)) +' k) ≤ (prime-power p (suc n))
      ipnk≤psn = (fst ipnk≤ppnpn) , (snd ipnk≤ppnpn) >=> ppnpn==psn

      kipn<psn : (k +' (i *' (prime-power p n))) < (prime-power p (suc n))
      kipn<psn = (fst kipn<pnppn) , (snd kipn<pnppn) >=> pnppn==psn

      ipnk<psn : ((i *' (prime-power p n)) +' k) < (prime-power p (suc n))
      ipnk<psn = transport (\j -> (+'-commute {k} {i *' (prime-power p n)} j) < (prime-power p (suc n)))
                           kipn<psn



      rp : RelativelyPrime⁰ (i *' (prime-power p n) +' k) (prime-power p (suc n))
      rp a a%ipnk a%psn = Totient.rp t a a%k a%pn
        where
        a<psn : a < (prime-power p (suc n))
        a<psn = trans-≤-< (div'->≤ a%ipnk {pos-ipnk}) ipnk<psn


        a%pn : a div' (prime-power p n)
        a%pn = case (split-prime-power-divisor p n a a%psn) of
         (\{ (inj-l path) -> bot-elim (<->!= a<psn path)
           ; (inj-r a%pn) -> a%pn
           })

        a%k : a div' k
        a%k = div'-+'-left (div'-mult a%pn i) a%ipnk


    is-totative-of-prime-power-pred :
      {k : Nat} (n : Nat⁺) -> (qr : QuotientRemainder (prime-power⁺ p ⟨ n ⟩) k) ->
      Totient (prime-power p (suc ⟨ n ⟩)) k ->
      (Fin p' × Totient (prime-power p ⟨ n ⟩) (Fin.i (QuotientRemainder.r qr)))
    is-totative-of-prime-power-pred {k} n⁺@(n , _) qr t = (q , q<p) , record
      { pos-k = pos-r
      ; k≤n = weaken-< (Fin.i<n r)
      ; rp = rp
      }
      where
      module qr = QuotientRemainder qr
      r : Fin (prime-power p n)
      r = qr.r
      r' = Fin.i r
      q : Nat
      q = qr.q

      r!=0 : r' != 0
      r!=0 r==0 = Prime'.!=1 p (Totient.rp t p' p%k (prime-power-div p (suc n , tt)))
        where
        pn%k : (prime-power p n) div' k
        pn%k = q , sym (+'-right-zero)
               >=> (cong ((q *' (prime-power p n)) +'_) (sym r==0))
               >=> qr.path
        p%k : p' div' k
        p%k = div'-trans (prime-power-div p n⁺) pn%k

      !=0->Pos : (x : Nat) -> (x != 0) -> Pos' x
      !=0->Pos zero    f = f refl
      !=0->Pos (suc _) f = tt

      pos-r : Pos' r'
      pos-r = !=0->Pos r' r!=0

      k-path : q *' (prime-power p n) +' r' == k
      k-path = qr.path

      k≤psn : k ≤ (p' *' (prime-power p n))
      k≤psn = Totient.k≤n t
      0<r : 0 < r'
      0<r = Pos'->< pos-r
      qpn0<qpnr : (q *' (prime-power p n) +' 0) < ((q *' (prime-power p n)) +' r')
      qpn0<qpnr = +₁-preserves-< 0<r
      qpn<k : (q *' (prime-power p n)) < k
      qpn<k = transport (\i -> (+'-right-zero {q *' (prime-power p n)} i) < (k-path i)) qpn0<qpnr
      qpn<psn : (q *' (prime-power p n)) < (p' *' (prime-power p n))
      qpn<psn = trans-≤ qpn<k k≤psn
      q<p : q < p'
      q<p = *₂-reflects-< qpn<psn (asym-< (Pos'->< (snd (prime-power⁺ p n))))

      rp : RelativelyPrime⁰ r' (prime-power p n)
      rp a a%r a%pn = Totient.rp t a a%k a%psn
        where
        a%qpnr : a div' (q *' (prime-power p n) +' r')
        a%qpnr = div'-+' (div'-mult a%pn q) a%r
        a%k : a div' k
        a%k = fst a%qpnr , snd a%qpnr >=> qr.path
        a%psn : a div' (prime-power p (suc n))
        a%psn = (div'-mult a%pn p')


    totatives-prime-power-eq'-1 : (n : Nat⁺) ->
      (Σ[ k ∈ Nat ] (Totient (prime-power p (suc ⟨ n ⟩)) k ×
                     QuotientRemainder (prime-power⁺ p ⟨ n ⟩) k)) ≃
      (Fin p' × (Totatives (prime-power p ⟨ n ⟩)))
    totatives-prime-power-eq'-1 n⁺@(n , _) = isoToEquiv i
      where
      open Iso
      i : Iso
          (Σ[ k ∈ Nat ] (Totient (prime-power p (suc n)) k × QuotientRemainder (prime-power⁺ p n) k))
          (Fin p' × (Totatives (prime-power p n)))
      i .fun (k , (t , qr)) =  fst ans , (Fin.i (QuotientRemainder.r qr) , snd ans)
        where
        ans = is-totative-of-prime-power-pred n⁺ qr t
      i .inv (i , (k , t)) =
        (ipnk , (is-totative-of-prime-power n⁺ i t , quotient-remainder (prime-power⁺ p n) ipnk))
        where
        ipnk = (Fin.i i *' (prime-power p n)) +' k
      i .rightInv (i , (k , t)) =
        cong2 _,_ (fin-i-path i'-path) (ΣProp-path isProp-isTotativeOf k-path)
        where
        prime-power≥prime : (prime-power p n) ≥ p'
        prime-power≥prime = div'->≤ (prime-power-div p n⁺) {snd (prime-power⁺ p n)}
        pn>1 : (prime-power p n) > 1
        pn>1 = trans-≤ (Prime'.>1 p) prime-power≥prime
        i'-path : quotient ((Fin.i i *' (prime-power p n)) +' k) (prime-power⁺ p n) == Fin.i i
        i'-path = quotient-path (prime-power⁺ p n) _ (k , (Totient.k<n t pn>1))
        k-path : Fin.i (remainder ((Fin.i i *' (prime-power p n)) +' k) (prime-power⁺ p n)) == k
        k-path = cong Fin.i (remainder-path (prime-power⁺ p n)
                                            (Fin.i i)
                                            (k , (Totient.k<n t pn>1)))
      i .leftInv (k , (t , qr)) =
        ΣProp-path (isProp× isProp-isTotativeOf (isContr->isProp isContr-QuotientRemainder))
                   (QuotientRemainder.path qr)

    private
      eqSym = equiv⁻¹
    totatives-prime-power-eq'-2 : (n : Nat⁺) ->
      (Totatives (prime-power p (suc ⟨ n ⟩))) ≃
      (Fin p' × (Totatives (prime-power p ⟨ n ⟩)))
    totatives-prime-power-eq'-2 n =
      existential-eq
        (\k -> eqSym (×-Top-eq _) >eq>
               ×-flip-eq >eq>
               (×-equiv (idEquiv _) (eqSym (Contr-Top-eq (isContr-QuotientRemainder))))) >eq>
      totatives-prime-power-eq'-1 n

  φ-prime-power : (n : Nat⁺) ->
    φ (prime-power⁺ p ⟨ n ⟩) == (prime-power p ⟨ n ⟩) -' (prime-power p (pred ⟨ n ⟩))
  φ-prime-power ((suc zero) , _) =
    begin
      φ (prime-power⁺ p 1)
    ==< cong φ p^1=p >
      φ p⁺
    ==< φ-prime >
      pred p'
    ==< cong (_-' 1) (cong fst (sym p^1=p)) >
      (prime-power p 1) -' (prime-power p 0)
    end
    where
    p^1=p : (prime-power⁺ p 1) == p⁺
    p^1=p = ΣProp-path isPropPos' ^ℕ-one

  φ-prime-power (suc n@(suc _) , _) =
    begin
      φ (prime-power⁺ p (suc n))
    ==< cong cardinality fs-path >
      cardinality (FinSet-Σ (FinSet-Fin p') (\_ -> (FinSet-Totatives pⁿ)))
    ==< cardinality-Σ (FinSet-Fin p') (\_ -> (FinSet-Totatives pⁿ)) >
      finiteSumᵉ (FinSet-Fin p') (\_ -> cardinality (FinSet-Totatives pⁿ))
    ==< cong (\x -> finiteSumᵉ (FinSet-Fin p') (\_ -> x))
             (φ-prime-power (n , tt) >=> sym *-right-one) >
      finiteSumᵉ (FinSet-Fin p') (\_ -> (pⁿ -' pⁿ⁻¹) * 1)
    ==< finiteSum-* {k = pⁿ -' pⁿ⁻¹} {f = \_ -> 1} >
      (pⁿ -' pⁿ⁻¹) * finiteSumᵉ (FinSet-Fin p') (\_ -> 1)
    ==< cong ((pⁿ -' pⁿ⁻¹) *_) finiteSum-one >
      (pⁿ -' pⁿ⁻¹) * p'
    ==< *'-distrib-minus {pⁿ} {pⁿ⁻¹} {p'} >
      (pⁿ * p') -' (pⁿ⁻¹ * p')
    ==< cong2 _-'_ (*-commuteᵉ pⁿ p') (*-commuteᵉ pⁿ⁻¹ p') >
      (prime-power p (suc n) -' (prime-power p n))
    end
    where
    pⁿ⁺¹ : ℕ
    pⁿ⁺¹ = prime-power p (suc n)
    pⁿ⁻¹ : ℕ
    pⁿ⁻¹ = prime-power p (pred n)
    pⁿ : ℕ
    pⁿ = prime-power p n
    opaque
      fs-path : (FinSet-Totatives (prime-power p (suc n))) ==
                (FinSet-Σ (FinSet-Fin p') (\_ -> (FinSet-Totatives (prime-power p n))))
      fs-path = (ΣProp-path isProp-isFinSet (ua (totatives-prime-power-eq'-2 (n , tt))))

-- (ℤ/nℤ* a) has φ(a) elements
-- (ℤ/nℤ* b) has φ(b) elements
-- if RP a b then
-- and (i ∈ ℤ/nℤ* a) (i ∈ ℤ/nℤ* b)

-- 1 2
-- 1 2 3 4
-- 1 2 4 7 8 11 13 14
--
-- 1 4 7 13
-- 2 8 11 14

-- 5 10
-- 3 6 9 12

-- 8 11 14 17
-- 13 16 19 22

-- 8 11 14 2
-- 13 1 4 7

-- 0 5 10
-- 1 6 11
-- 2 7 12
-- 3 8 13
-- 4 9 14


-- 0 7  14
-- 1 8  15
-- 2 9  16
-- 3 10 17
-- 4 11 18
-- 5 12 19
-- 6 13 20




-- 3
-- 5
-- 3 5 6 9 10 12 15

private
  Fin1 : Nat -> Type₀
  Fin1 n = Σ[ i ∈ Nat⁺ ] (⟨ i ⟩ ≤ n)

  isoFin1 : {n : Nat} -> Iso (Fin1 n) (Fin n)
  isoFin1 .Iso.fun (((suc x) , tt) , lt) = (x , lt)
  isoFin1 .Iso.inv (x , lt) = (((suc x) , tt) , lt)
  isoFin1 .Iso.rightInv _ = refl
  isoFin1 .Iso.leftInv (((suc x) , tt) , lt) = refl

  module _ (n⁺ : Nat⁺) where
    private
      n = ⟨ n⁺ ⟩

    uc : (x : ℤ/nℤ n) -> (isUnit x) ≃ (CoprimeN n⁺ x)
    uc = Unit-CoprimeN-eq n⁺

  private
    module _ {n : Nat} (n>1 : n > 1) where
      FinSucRP-FinRP->1-eq : (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n (suc i))) ≃
                             (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n i))
      FinSucRP-FinRP->1-eq = isoToEquiv i
        where
        open Iso
        i : Iso (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n (suc i)))
                (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n i))
        i .fun ((i , (zero  , path)) , rp) =
          bot-elim (<->!= n>1 (sym ((subst (RelativelyPrime⁰ n) path rp) n div'-refl div'-refl)))
        i .fun ((i , (suc j , path)) , rp) = (suc i , (j , +'-right-suc >=> path)) , rp
        i .inv ((zero  , lt) , rp) = bot-elim (<->!= n>1 (sym (rp-zero (rp-sym rp))))
        i .inv ((suc i , lt) , rp) = (i , pred-≤ (right-suc-≤ lt)) , rp
        i .rightInv ((zero  , lt) , rp) = bot-elim (<->!= n>1 (sym (rp-zero (rp-sym rp))))
        i .rightInv ((suc i , (j , path)) , rp) =
          ΣProp-path isProp-RelativelyPrime⁰ (fin-i-path refl)
        i .leftInv ((i , (zero  , path)) , rp) =
          bot-elim (<->!= n>1 (sym ((subst (RelativelyPrime⁰ n) path rp) n div'-refl div'-refl)))
        i .leftInv ((i , (suc j , path)) , rp) =
          ΣProp-path isProp-RelativelyPrime⁰ (fin-i-path refl)

    FinSucRP-FinRP-1-eq : (Σ (Fin 1) (\(i , _) -> RelativelyPrime⁰ 1 (suc i))) ≃
                          (Σ (Fin 1) (\(i , _) -> RelativelyPrime⁰ 1 i))
    FinSucRP-FinRP-1-eq = existential-eq (\ (a , a<1) -> handle a a<1)
      where
      handle : (a : Nat) -> (a < 1) -> RelativelyPrime⁰ 1 (suc a) ≃ RelativelyPrime⁰ 1 a
      handle (suc a) lt = bot-elim (zero-≮ (pred-≤ lt))
      handle zero _ = isoToEquiv i
        where
        open Iso
        i : Iso (RelativelyPrime⁰ 1 1) (RelativelyPrime⁰ 1 0)
        i .fun _ = rp-sym rp-one
        i .inv _ = rp-one
        i .rightInv _ = isProp-RelativelyPrime⁰ _ _
        i .leftInv _ = isProp-RelativelyPrime⁰ _ _

    FinSucRP-FinRP-0-eq : (Σ (Fin 0) (\(i , _) -> RelativelyPrime⁰ 0 (suc i))) ≃
                          (Σ (Fin 0) (\(i , _) -> RelativelyPrime⁰ 0 i))
    FinSucRP-FinRP-0-eq =
      (reindexΣ (equiv⁻¹ Fin-Bot-eq) _) >eq> Σ-Bot-eq >eq> (equiv⁻¹ Σ-Bot-eq) >eq>
      (equiv⁻¹ (reindexΣ (equiv⁻¹ Fin-Bot-eq) _))

    FinSucRP-FinRP-eq : {n : Nat} -> (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n (suc i))) ≃
                                     (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n i))
    FinSucRP-FinRP-eq {zero} = FinSucRP-FinRP-0-eq
    FinSucRP-FinRP-eq {suc zero} = FinSucRP-FinRP-1-eq
    FinSucRP-FinRP-eq {suc (suc n)} = FinSucRP-FinRP->1-eq (suc-≤ (suc-≤ zero-≤))


  module _ where
    opaque
      Totatives-FinRP-eq :
        {n : Nat} -> Totatives n ≃
                     Σ (Fin1 n) (\((i , _) , _) -> RelativelyPrime⁰ n i)
      Totatives-FinRP-eq {n} = isoToEquiv i
        where
        open Iso
        i : Iso (Totatives n)
                (Σ (Fin1 n) (\((i , _) , _) -> RelativelyPrime⁰ n i))
        i .fun (i , t) = ((i , t.pos-k) , t.k≤n) , (rp-sym t.rp)
          where
          module t = Totient t
        i .inv (((i , p) , lt) , rp) = i , record { pos-k = p ; k≤n = lt ; rp = (rp-sym rp) }
        i .rightInv _ = refl
        i .leftInv _ = refl

      Fin1RP-FinRP-eq : {n : Nat} -> (Σ (Fin1 n) (\((i , _) , _) -> RelativelyPrime⁰ n i)) ≃
                                     (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n (suc i)))
      Fin1RP-FinRP-eq = reindexΣ (equiv⁻¹ (isoToEquiv isoFin1)) _


      FinRP-FinRPⁱ-eq : {n : Nat} -> (Σ (Fin n) (\(i , _) -> RelativelyPrime⁰ n i)) ≃
                                     (Σ (Fin n) (\(i , _) -> RelativelyPrime (int n) (int i)))
      FinRP-FinRPⁱ-eq = existential-eq (\_ -> RelativelyPrime-RelativelyPrime-eq)

      FinRP-ℤ/nℤCoprime-eq : (n⁺ : Nat⁺) ->
        (Σ (Fin ⟨ n⁺ ⟩) (\(i , _) -> RelativelyPrime (int ⟨ n⁺ ⟩) (int i))) ≃
        (Σ (ℤ/nℤ ⟨ n⁺ ⟩) (CoprimeN n⁺))
      FinRP-ℤ/nℤCoprime-eq n⁺ = equiv⁻¹ (reindexΣ (equiv⁻¹ (ℤ/nℤ-Fin-eq n⁺)) (CoprimeN n⁺))



    module _ (n⁺ : Nat⁺) where
      private
        n = ⟨ n⁺ ⟩

      ℤ/nℤCoprime-ℤ/nℤ*-eq : (Σ (ℤ/nℤ n) (CoprimeN n⁺)) ≃ ℤ/nℤˣ n
      ℤ/nℤCoprime-ℤ/nℤ*-eq = existential-eq (\x -> (equiv⁻¹ (Unit-CoprimeN-eq n⁺ x)))

      opaque
        Totatives-ℤ/nℤ*-eq : Totatives n ≃ (ℤ/nℤˣ n)
        Totatives-ℤ/nℤ*-eq =
          Totatives-FinRP-eq >eq>
          Fin1RP-FinRP-eq >eq>
          FinSucRP-FinRP-eq >eq>
          FinRP-FinRPⁱ-eq >eq>
          FinRP-ℤ/nℤCoprime-eq n⁺ >eq>
          ℤ/nℤCoprime-ℤ/nℤ*-eq

    module _ (a⁺ b⁺ : Nat⁺) (rp : RelativelyPrime⁺ a⁺ b⁺) where
      private
        a = ⟨ a⁺ ⟩
        b = ⟨ b⁺ ⟩

      opaque
        Totatives-rp-eq : Totatives (a * b) ≃ (Totatives a × Totatives b)
        Totatives-rp-eq =
          Totatives-ℤ/nℤ*-eq (a⁺ *⁺ b⁺) >eq>
          equiv⁻¹ (ℤ/nℤˣ-×-eq rp) >eq>
          ×-equiv (equiv⁻¹ (Totatives-ℤ/nℤ*-eq a⁺)) (equiv⁻¹ (Totatives-ℤ/nℤ*-eq b⁺))


Multiplicative-φ : Multiplicative φ
Multiplicative-φ .fst = φ-one
Multiplicative-φ .snd a b rp =
  begin
    φ (a *⁺ b)
  ==<>
    cardinality (FinSet-Totatives (a' *' b'))
  ==< cong cardinality path1 >
    cardinality (FinSet-× (FinSet-Totatives a') (FinSet-Totatives b'))
  ==< cardinality-× _ _ >
    cardinality (FinSet-Totatives a') *' cardinality (FinSet-Totatives b')
  ==<>
    φ a *' φ b
  end
  where
  a' = ⟨ a ⟩
  b' = ⟨ b ⟩
  path1 : (FinSet-Totatives (a' * b')) == (FinSet-× (FinSet-Totatives a') (FinSet-Totatives b'))
  path1 = ΣProp-path isProp-isFinSet (ua (Totatives-rp-eq a b rp))

φ-0< : (n : Nat⁺) -> 0 < φ n
φ-0< (n , n-pos) = eqFun (inhabited-0<cardinality (FinSet-Totatives n)) ∣ 1 , t ∣
  where
  t : Totient n 1
  t = record
    { pos-k = tt
    ; k≤n = Pos'->< n-pos
    ; rp = rp-sym rp-one
    }
