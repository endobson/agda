{-# OPTIONS --cubical --safe --exact-split #-}

module unique-prime-factorization where

open import base
open import div
open import equality
open import functions
open import gcd
open import hlevel
open import nat
open import prime
open import prime-factorization
open import relation
open import unordered-list

private
  record DivisionCount (d : Nat) (n : Nat) : Type₀ where
    constructor division-count

    field
      d-pos : Pos' d
      n-pos : Pos' n
      k : Nat
      d^k%n : (d ^' k) div' n
      ¬d^[suc-k]%n : ¬ ((d ^' (suc k)) div' n)

  division-count-suc : {d n : Nat} -> DivisionCount d n -> DivisionCount d (d *' n)
  division-count-suc {d} {n} (division-count d-pos n-pos k (x , pr) f) = record
    { d-pos        = d-pos
    ; n-pos        = *'-Pos'-Pos' {d} {n} d-pos n-pos
    ; k            = (suc k)
    ; d^k%n        = positive
    ; ¬d^[suc-k]%n = negative
    }
    where
    d^k = d ^' k

    positive : (d ^' (suc k)) div' (d *' n)
    positive = (x , adjusted-proof)
      where
      adjusted-proof : x *' (d *' d^k) == d *' n
      adjusted-proof = (sym (*'-assoc {x} {d})) >=> (*'-left (*'-commute {x} {d})) >=> (*'-assoc {d} {x})
                       >=> (cong (d *'_) pr)
    negative : ¬ ((d ^' (suc (suc k))) div' (d *' n))
    negative (x , pr) = f d^sk%n
      where
      adjusted-proof : x *' d ^' (suc k) == n
      adjusted-proof = *'-left-injective {d} d-pos
        (begin
           d *' (x *' (d ^' (suc k)))
         ==< (sym (*'-assoc {d} {x})) >
           (d *' x) *' (d ^' (suc k))
         ==< (*'-left (*'-commute {d} {x})) >
           (x *' d) *' (d ^' (suc k))
         ==< (*'-assoc {x} {d}) >
           x *' (d *' (d ^' (suc k)))
         ==< pr >
           d *' n
         end)

      d^sk%n : (d ^' (suc k)) div' n
      d^sk%n = x , adjusted-proof

  compute-division-count' : (d n bound : Nat) -> {Pos' n} -> 1 < d -> n < bound -> DivisionCount d n
  compute-division-count' _ _ zero                _                  n<bound = bot-elim (zero-≮ n<bound)
  compute-division-count' d n (suc bound) {n-pos} 1<d@(d' , d'+2==d) sn≤sbound
    with (decide-div d n)
  ... | (no ¬d%n) = record
    { d-pos        = transport (\i -> Pos' (ssd'==d i)) tt
    ; n-pos        = n-pos
    ; k            = 0
    ; d^k%n        = div'-one
    ; ¬d^[suc-k]%n = (transport (\i -> ¬ ((*'-right-one {d} (~ i)) div' n)) ¬d%n)
    }
    where

    ssd'==d : (suc (suc d')) == d
    ssd'==d = +'-commute {2} {d'} >=> d'+2==d
  ... | (yes (zero       , pr)) = bot-elim (transport (\i -> Pos' (pr (~ i))) n-pos)
  ... | (yes (x@(suc x') , pr)) =
    (transport (\i -> DivisionCount d ((*'-commute {d} {x} >=> pr) i))
               (division-count-suc rec-div-count))
    where

    ssd'==d : (suc (suc d')) == d
    ssd'==d = +'-commute {2} {d'} >=> d'+2==d


    sx+?==n : (suc x) +' (x' +' d' *' x) == n
    sx+?==n = (sym (+'-right-suc {x}))
              >=> (*'-commute {suc (suc d')} {x})
              >=> (*'-right {x} ssd'==d)
              >=> pr

    x<n : suc x ≤ n
    x<n = (x' +' d' *' x) , +'-commute {_} {suc x} >=> sx+?==n

    x<bound : x < bound
    x<bound = trans-<-≤ x<n (pred-≤ sn≤sbound)

    rec-div-count : DivisionCount d x
    rec-div-count = (compute-division-count' d x bound 1<d x<bound)

  compute-division-count : (d n : Nat) -> {Pos' n} -> 1 < d -> DivisionCount d n
  compute-division-count d n {pos-n} 1<d =
    compute-division-count' d n (suc n) {pos-n} 1<d (same-≤ (suc n))


  compute-prime-division-count : (p : Prime')  (n : Nat) -> {Pos' n} -> DivisionCount ⟨ p ⟩ n
  compute-prime-division-count (p , (is-prime' p>1 _)) n@(suc _) =
    compute-division-count p n p>1


  isPropDivisionCount : {d n : Nat} -> isProp (DivisionCount d n)
  isPropDivisionCount {d} {n@(suc _)}
                      (division-count d-pos1 _ k1 div-k1 ¬div-sk1)
                      (division-count d-pos2 _ k2 div-k2 ¬div-sk2) i =
      (division-count
        (isProp->PathP (\i -> isPropPos') d-pos1 d-pos2 i)
        _
        (p-k i)
        (isProp->PathP (\i -> isPropDiv' {d ^' (p-k i)}) div-k1 div-k2 i)
        (isProp->PathP (\i -> isProp¬ ((d ^' (suc (p-k i))) div' n)) ¬div-sk1 ¬div-sk2 i))
    where
      lesser-power : ∀ {k1 k2 n} -> ¬ ((d ^' suc k1) div' n) -> (d ^' k2) div' n -> k2 ≤ k1
      lesser-power {k1}     {zero}   {n} _    _ = zero-≤
      lesser-power {suc k1} {suc k2} {n} ¬div (x , pr) =
         suc-≤ (lesser-power ¬div-next div-next)
        where
        n' : Nat
        n' = x *' d ^' k2

        d-proof : (x *' d) *' (d ^' k2) == n
        d-proof = (*'-assoc {x}) >=> pr


        div-next : (d ^' k2) div' n'
        div-next = x , refl

        ¬div-next : ¬ ((d ^' (suc k1)) div' n')
        ¬div-next (y , pr2) = ¬div proof
          where
          inner-pr : y *' (d ^' (suc (suc k1))) == n
          inner-pr =
            begin
              y *' (d ^' (suc (suc k1)))
            ==< (sym (*'-assoc {y} {d})) >
              (y *' d) *' (d ^' (suc k1))
            ==< (*'-left (*'-commute {y})) >
              (d *' y) *' (d ^' (suc k1))
            ==< (*'-assoc {d}) >
              d *' (y *' (d ^' (suc k1)))
            ==< (cong (d *'_) pr2) >
              d *' (x *' d ^' k2)
            ==< sym (*'-assoc {d}) >
              (d *' x) *' d ^' k2
            ==< *'-left (*'-commute {d}) >
              (x *' d) *' d ^' k2
            ==< *'-assoc {x}  >
              x *' (d *' d ^' k2)
            ==< pr >
              n
            end

          proof : ((d ^' (suc (suc k1))) div' n)
          proof = y , inner-pr


      lesser-power {zero}   {suc k2} {n} ¬div (x , pr) = bot-elim (¬d-div d-div)
        where
        d-proof : (x *' (d ^' k2)) *' d == n
        d-proof = (*'-assoc {x}) >=> (*'-right {x} (*'-commute {d ^' k2})) >=> pr

        d-div : (d div' n)
        d-div = (x *' (d ^' k2)) , d-proof

        ¬d-div : ¬ (d div' n)
        ¬d-div = (transport (\i -> ¬ ((*'-right-one {d} i) div' n)) ¬div)

      proof-1 : k1 ≤ k2
      proof-1 = lesser-power ¬div-sk2 div-k1
      proof-2 : k2 ≤ k1
      proof-2 = lesser-power ¬div-sk1 div-k2
      p-k : k1 == k2
      p-k = (≤-antisym proof-1 proof-2)

  prime->Pos' : ∀ (p : Prime') -> Pos' ⟨ p ⟩
  prime->Pos' (zero  , (is-prime' p>1 _)) = bot-elim (zero-≮ p>1)
  prime->Pos' (suc _ , _                ) = tt

  module _ (p : Prime') where

    prime-product-pos : ∀ (ps : UList Prime') -> Pos' (prime-product ps)
    prime-product-pos = UListElim.prop isPropPos' []* ::*
      where
      []* : Pos' (prime-product [])
      []* = tt
      ::* : ∀ (p : Prime') {ps : UList Prime'}
            -> Pos' (prime-product ps) -> Pos' (prime-product (p :: ps))
      ::* p ps-pos = *'-Pos'-Pos' (prime->Pos' p) ps-pos


    primes-division-count : (p : Prime') -> (ps : UList Prime')
                            -> DivisionCount ⟨ p ⟩ (prime-product ps)
    primes-division-count p ps =
      compute-prime-division-count p (prime-product ps) {prime-product-pos ps}

    product-division-count : Prime' -> UList Prime' -> Nat
    product-division-count p ps = DivisionCount.k (primes-division-count p ps)

    prime-doesn't-divide-1 : ∀ (p : Prime') -> DivisionCount ⟨ p ⟩ 1
    prime-doesn't-divide-1 p@(pv , (is-prime' p>1 _)) = record
      { d-pos        = prime->Pos' p
      ; n-pos        = tt
      ; k            = 0
      ; d^k%n        = (1 , refl)
      ; ¬d^[suc-k]%n = transport (\i -> ¬(^'-right-one {pv} (~ i) div' 1)) no-divides
      }
      where
      no-divides : ¬ (pv div' 1)
      no-divides pv%1 = same-≮ (trans-≤-< (div'->≤ pv%1) p>1)

    product-division-count-empty : product-division-count p [] == 0
    product-division-count-empty =
      cong DivisionCount.k
      (isPropDivisionCount (primes-division-count p []) (prime-doesn't-divide-1 p))

    product-division-count-same :
      (p2 : Prime') {ps : UList Prime'}
       -> p == p2
       -> product-division-count p (p2 :: ps) == suc (product-division-count p ps)
    product-division-count-same p2 {ps} path = (\i -> DivisionCount.k (path-part1 i))

      where
      c2 : DivisionCount ⟨ p ⟩ (⟨ p ⟩ *' (prime-product ps))
      c2 = division-count-suc (primes-division-count p ps)

      path-part1 : PathP (\i -> DivisionCount ⟨ p ⟩ ((path (~ i) .fst) *' (prime-product ps)))
                         (primes-division-count p (p2 :: ps)) c2
      path-part1 = isProp->PathP (\_ -> isPropDivisionCount) (primes-division-count p (p2 :: ps)) c2

    prime-product-same-division-count :
      ∀ {n : Nat} (p2 : Prime') -> p != p2 -> DivisionCount ⟨ p ⟩ n -> DivisionCount ⟨ p ⟩ (⟨ p2 ⟩ *' n)
    prime-product-same-division-count {n} p2 ¬path (division-count d-pos n-pos k d^k%n ¬d^sk%n) = record
      { d-pos        = d-pos
      ; n-pos        = *'-Pos'-Pos' (prime->Pos' p2) n-pos
      ; k            = k
      ; d^k%n        = div'-mult d^k%n ⟨ p2 ⟩
      ; ¬d^[suc-k]%n = no-divides
      }
      where
      pv = ⟨ p ⟩
      p2v = ⟨ p2 ⟩

      gcd1' : GCD' pv p2v 1
      gcd1' = distinct-primes->relatively-prime ¬path

      gcd1 : GCD' (pv ^' (suc k)) p2v 1
      gcd1 = gcd'-sym (relatively-prime-^' (gcd'-sym gcd1') (suc k))

      no-divides : ¬ ((pv ^' (suc k)) div' (p2v *' n))
      no-divides p^sk%p2*n = ¬d^sk%n (euclids-lemma' p^sk%p2*n gcd1)


    product-division-count-different :
      (p2 : Prime') {ps : UList Prime'}
       -> p != p2
       -> product-division-count p (p2 :: ps) == (product-division-count p ps)
    product-division-count-different p2 {ps} ¬path = cong DivisionCount.k path
      where
      other-count : DivisionCount ⟨ p ⟩ (⟨ p2 ⟩ *' (prime-product ps))
      other-count = prime-product-same-division-count p2 ¬path (primes-division-count p ps)

      path : Path (DivisionCount ⟨ p ⟩ (⟨ p2 ⟩ *' (prime-product ps)))
                  (primes-division-count p (p2 :: ps)) other-count
      path = isPropDivisionCount _ _


    P : (ps : UList Prime') -> Type₀
    P ps = count p ps == product-division-count p ps

    count-path : (ps : UList Prime') -> P ps
    count-path = UListElim.prop (isSetNat _ _) []* ::*
      where
      []* : P []
      []* = sym product-division-count-empty
      ::* : ∀ (p2 : Prime') {ps : UList Prime'} -> P ps -> P (p2 :: ps)
      ::* p2 {ps} path = handle (discretePrime' p p2)
        where
        handle : (Dec (p == p2)) -> P (p2 :: ps)
        handle (yes p-path) =
          (count-== ps p-path)
          >=> (cong suc path)
          >=> sym (product-division-count-same p2 {ps} p-path)
        handle (no p-path) =
          (count-!= ps p-path)
          >=> path
          >=> sym (product-division-count-different p2 {ps} p-path)

    same-count : {n : Nat}
                 -> (f1 : PrimeFactorization n)
                 -> (f2 : PrimeFactorization n)
                 ->   count p (PrimeFactorization.primes f1)
                   == count p (PrimeFactorization.primes f2)
    same-count {n} (prime-factorization primes1 path1) (prime-factorization primes2 path2) =
      count-path primes1
      >=>
      middle-path1'
      >=>
      (sym middle-path2')
      >=>
      (sym (count-path primes2))

      where
      n-pos : Pos' n
      n-pos = transport (\i -> Pos' (path1 i)) (prime-product-pos primes1)


      check-count-path1 :
        count p primes1 ==
        DivisionCount.k (compute-prime-division-count p (prime-product primes1) {prime-product-pos primes1})
      check-count-path1 = count-path primes1

      check-count-path2 :
        count p primes2 ==
        DivisionCount.k (compute-prime-division-count p (prime-product primes2) {prime-product-pos primes2})
      check-count-path2 = count-path primes2

      middle-path1 :
        PathP (\i -> DivisionCount ⟨ p ⟩ (path1 i) )
        (compute-prime-division-count p (prime-product primes1) {prime-product-pos primes1})
        (compute-prime-division-count p n {n-pos})
      middle-path1 = isProp->PathP (\_ -> isPropDivisionCount) _ _

      middle-path2 :
        PathP (\i -> DivisionCount ⟨ p ⟩ (path2 i) )
        (compute-prime-division-count p (prime-product primes2) {prime-product-pos primes2})
        (compute-prime-division-count p n {n-pos})
      middle-path2 = isProp->PathP (\_ -> isPropDivisionCount) _ _

      middle-path1' :
        DivisionCount.k (compute-prime-division-count p (prime-product primes1) {prime-product-pos primes1})
        ==
        DivisionCount.k (compute-prime-division-count p n {n-pos})
      middle-path1' i = DivisionCount.k (middle-path1 i)

      middle-path2' :
        DivisionCount.k (compute-prime-division-count p (prime-product primes2) {prime-product-pos primes2})
        ==
        DivisionCount.k (compute-prime-division-count p n {n-pos})
      middle-path2' i = DivisionCount.k (middle-path2 i)

isPropPrimeFactorization : {n : Nat} -> isProp (PrimeFactorization n)
isPropPrimeFactorization p1@(prime-factorization ps1 product1)
                         p2@(prime-factorization ps2 product2) = full-path
  where
  primes-path : ps1 == ps2
  primes-path = (countExtUList ps1 ps2 (\x -> same-count x p1 p2))

  full-path : p1 == p2
  full-path i = prime-factorization (primes-path i) (product-path i)
    where
    product-path :
      PathP (\i -> (prime-product (primes-path i)) == _) product1 product2
    product-path =
      isProp->PathP (\i -> isSetNat _ _) product1 product2
