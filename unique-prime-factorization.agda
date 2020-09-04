{-# OPTIONS --cubical --safe --exact-split #-}

module unique-prime-factorization where

open import base
open import div
open import equality
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import lcm
open import nat
open import prime
open import prime-div-count
open import prime-factorization
open import prime-gcd
open import relation
open import relatively-prime
open import unordered-list
open import unordered-list.discrete

private
  record DivisionCount (d : Nat) (n : Nat) : Type₀ where
    constructor division-count

    field
      d-pos : Pos' d
      n-pos : Pos' n
      k : Nat
      d^k%n : (d ^' k) div' n
      ¬d^[suc-k]%n : ¬ ((d ^' (suc k)) div' n)

    n⁺ : Nat⁺
    n⁺ = n , n-pos

    d⁺ : Nat⁺
    d⁺ = d , d-pos

  division-count-suc : {d n : Nat} -> DivisionCount d n -> DivisionCount d (d *' n)
  division-count-suc {d} {n} dc@(division-count d-pos n-pos k (x , pr) f) = record
    { d-pos        = d-pos
    ; n-pos        = *'-Pos'-Pos' {d} {n} d-pos n-pos
    ; k            = (suc k)
    ; d^k%n        = positive
    ; ¬d^[suc-k]%n = negative
    }
    where
    d^k = d ^' k

    d⁺ = DivisionCount.d⁺ dc

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
      adjusted-proof = *'-left-injective d⁺
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

  compute-division-count' : (d : Nat) (n : Nat⁺) (bound : Nat) -> 1 < d -> ⟨ n ⟩ < bound
                             -> DivisionCount d ⟨ n ⟩
  compute-division-count' _ _           zero        _                  n<bound = bot-elim (zero-≮ n<bound)
  compute-division-count' d (n , n-pos) (suc bound) 1<d@(d' , d'+2==d) sn≤sbound
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
    rec-div-count = (compute-division-count' d (x , tt) bound 1<d x<bound)

  compute-division-count : (d : Nat) -> (n : Nat⁺) -> 1 < d -> DivisionCount d ⟨ n ⟩
  compute-division-count d n@(n' , _) 1<d =
    compute-division-count' d n (suc n') 1<d (same-≤ (suc n'))


  isPropDivisionCount : {d n : Nat} -> isProp (DivisionCount d n)
  isPropDivisionCount {d} {n}
                      dc1@(division-count d-pos1 n-pos1 k1 div-k1 ¬div-sk1)
                      dc2@(division-count d-pos2 n-pos2 k2 div-k2 ¬div-sk2) i =
      (division-count
        (isProp->PathP (\i -> isPropPos') d-pos1 d-pos2 i)
        (isProp->PathP (\i -> isPropPos') n-pos1 n-pos2 i)
        (p-k i)
        (isProp->PathP (\i -> isPropDiv' {d ^' (p-k i)} n1⁺) div-k1 div-k2 i)
        (isProp->PathP (\i -> isProp¬ ((d ^' (suc (p-k i))) div' n)) ¬div-sk1 ¬div-sk2 i))
    where
      n1⁺ = DivisionCount.n⁺ dc1

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


compute-prime-division-count : (p : Prime')  (n : Nat⁺) -> DivisionCount ⟨ p ⟩ ⟨ n ⟩
compute-prime-division-count p@(p' , _) n =
  compute-division-count p' n (Prime'.>1 p)

private

  prime-product-pos : ∀ (ps : UList Prime') -> Pos' (prime-product ps)
  prime-product-pos = UListElim.prop isPropPos' []* ::*
    where
    []* : Pos' (prime-product [])
    []* = tt
    ::* : ∀ (p : Prime') {ps : UList Prime'}
          -> Pos' (prime-product ps) -> Pos' (prime-product (p :: ps))
    ::* p ps-pos = *'-Pos'-Pos' (prime->Pos' p) ps-pos

  prime-product⁺ : UList Prime' -> Nat⁺
  prime-product⁺ ps = prime-product ps , prime-product-pos ps


  primes-division-count : (p : Prime') -> (ps : UList Prime')
                          -> DivisionCount ⟨ p ⟩ (prime-product ps)
  primes-division-count p ps =
    compute-prime-division-count p (prime-product⁺ ps)

  product-division-count : Prime' -> UList Prime' -> Nat
  product-division-count p ps = DivisionCount.k (primes-division-count p ps)

  module _ (p : Prime') where

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

      rp' : RelativelyPrime⁰ pv p2v
      rp' = distinct-primes->relatively-prime ¬path

      rp : RelativelyPrime⁰ (pv ^' (suc k)) p2v
      rp = (rp-sym (relatively-prime-^' (rp-sym rp') (suc k)))

      no-divides : ¬ ((pv ^' (suc k)) div' (p2v *' n))
      no-divides p^sk%p2*n = ¬d^sk%n (euclids-lemma/rp p^sk%p2*n rp)


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
      n⁺ : Nat⁺
      n⁺ = n , n-pos

      middle-path1 :
        PathP (\i -> DivisionCount ⟨ p ⟩ (path1 i) )
        (compute-prime-division-count p (prime-product⁺ primes1))
        (compute-prime-division-count p n⁺)
      middle-path1 = isProp->PathP (\_ -> isPropDivisionCount) _ _

      middle-path2 :
        PathP (\i -> DivisionCount ⟨ p ⟩ (path2 i) )
        (compute-prime-division-count p (prime-product⁺ primes2))
        (compute-prime-division-count p n⁺)
      middle-path2 = isProp->PathP (\_ -> isPropDivisionCount) _ _

      middle-path1' :
        DivisionCount.k (compute-prime-division-count p (prime-product⁺ primes1))
        ==
        DivisionCount.k (compute-prime-division-count p n⁺)
      middle-path1' i = DivisionCount.k (middle-path1 i)

      middle-path2' :
        DivisionCount.k (compute-prime-division-count p (prime-product⁺ primes2))
        ==
        DivisionCount.k (compute-prime-division-count p n⁺)
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

isContrPrimeFactorization⁺ : {n : Nat⁺} -> isContr (PrimeFactorization⁺ n)
isContrPrimeFactorization⁺ {n} = pf , isPropPrimeFactorization pf
  where
  pf = compute-prime-factorization n


module _ (p : Prime') {a : Nat} (pf : PrimeFactorization a) where
  private
    p' = fst p

    div->∈-primes : (⟨ p ⟩ div' a) -> (contains p (PrimeFactorization.primes pf))
    div->∈-primes (x , div-path) =
      primes-x , full-path
      where
      pos-a : Pos' a
      pos-a = (PrimeFactorization.pos pf)

      pos-x : Pos' x
      pos-x = div'-pos->pos (p' , *'-commute {p'} {x} >=> div-path) pos-a

      pf-x : PrimeFactorization x
      pf-x = compute-prime-factorization (x , pos-x)

      primes-x = PrimeFactorization.primes pf-x
      product-x = PrimeFactorization.product pf-x

      pf' : PrimeFactorization a
      pf' = prime-factorization
        (p :: primes-x)
        (*'-right {p'} product-x
         >=> *'-commute {p'} {x}
         >=> div-path)

      full-path : p :: primes-x == PrimeFactorization.primes pf
      full-path = cong PrimeFactorization.primes (isPropPrimeFactorization pf' pf)


    ∈-primes->div : (contains p (PrimeFactorization.primes pf)) -> (⟨ p ⟩ div' a)
    ∈-primes->div (ps' , ul-path) =
      (prime-product ps' ,
       *'-commute {prime-product ps'} {p'}
       >=> cong prime-product ul-path
       >=> PrimeFactorization.product pf)


  prime-div-prime-factorization-∈-iso : Iso (p' div' a) (contains p (PrimeFactorization.primes pf))
  prime-div-prime-factorization-∈-iso = record
    { fun = div->∈-primes
    ; inv = ∈-primes->div
    ; rightInv = \c -> isPropContainsDiscrete (div->∈-primes (∈-primes->div c)) c
    ; leftInv = \d -> isPropDiv' (PrimeFactorization.nat⁺ pf) (∈-primes->div (div->∈-primes d)) d
    }

  prime-div==prime-factorization-∈ : (⟨ p ⟩ div' a) == contains p (PrimeFactorization.primes pf)
  prime-div==prime-factorization-∈ = ua (isoToEquiv prime-div-prime-factorization-∈-iso)


private
  prime-div-count->division-count :
    {p : Prime'} {a n : Nat} -> PrimeDivCount p a n -> DivisionCount ⟨ p ⟩ a
  prime-div-count->division-count {p} {a} {n} dc = record
    { d-pos = (Prime'.pos p)
    ; n-pos = (PrimeDivCount.a-pos dc)
    ; k = n
    ; d^k%n        = (PrimeDivCount.%a dc)
    ; ¬d^[suc-k]%n = (PrimeDivCount.¬p^sn%a dc)
    }

  division-count->prime-div-count :
    {p : Prime'} {a : Nat} -> (dc : DivisionCount ⟨ p ⟩ a) -> PrimeDivCount p a (DivisionCount.k dc)
  division-count->prime-div-count {p} {a} dc = record
    { %a = dc.d^k%n
    ; ¬p%r = ¬p%r
    }
    where
    module dc = DivisionCount dc
    p' = ⟨ p ⟩

    r = fst dc.d^k%n
    r-path : r *' (prime-power p dc.k) == a
    r-path = snd dc.d^k%n

    ¬p%r : ¬ (p' div' r)
    ¬p%r (x , x-path) = dc.¬d^[suc-k]%n p^sk%a
      where
      p^sk%a : (prime-power p (suc dc.k)) div' a
      p^sk%a = x , sym (*'-assoc {x} {p'}) >=> *'-left x-path >=> r-path


same-division-count : (a b : Nat⁺) ->
  ((p : Prime')
   -> (d1 : DivisionCount ⟨ p ⟩ ⟨ a ⟩)
   -> (d2 : DivisionCount ⟨ p ⟩ ⟨ b ⟩)
   -> (DivisionCount.k d1) == (DivisionCount.k d2))
  -> ⟨ a ⟩ == ⟨ b ⟩
same-division-count a b f =
  sym pf-a.product
  >=> cong prime-product (countExtUList pf-a.primes pf-b.primes g)
  >=> pf-b.product
  where
  pf-a = compute-prime-factorization a
  pf-b = compute-prime-factorization b
  module pf-a = PrimeFactorization pf-a
  module pf-b = PrimeFactorization pf-b

  g : (p : Prime') -> count p pf-a.primes == count p pf-b.primes
  g p = count-path p pf-a.primes
        >=> (f' p (primes-division-count p pf-a.primes)
                  (primes-division-count p pf-b.primes))
        >=> sym (count-path p pf-b.primes)
    where
    f' : ((p : Prime')
          -> (d1 : DivisionCount ⟨ p ⟩ (prime-product pf-a.primes))
          -> (d2 : DivisionCount ⟨ p ⟩ (prime-product pf-b.primes))
          -> (DivisionCount.k d1) == (DivisionCount.k d2))
    f' = transport (\i -> ((p : Prime')
                            -> (d1 : DivisionCount ⟨ p ⟩ (pf-a.product (~ i)))
                            -> (d2 : DivisionCount ⟨ p ⟩ (pf-b.product (~ i)))
                            -> (DivisionCount.k d1) == (DivisionCount.k d2))) f

prime-same-division-count : (a b : Nat⁺) ->
  ((p : Prime') {d1 d2 : Nat}
   -> PrimeDivCount p ⟨ a ⟩ d1
   -> PrimeDivCount p ⟨ b ⟩ d2
   -> d1 == d2)
  -> ⟨ a ⟩ == ⟨ b ⟩
prime-same-division-count a b f = same-division-count a b g
  where
  g : (p : Prime')
      -> (d1 : DivisionCount ⟨ p ⟩ ⟨ a ⟩)
      -> (d2 : DivisionCount ⟨ p ⟩ ⟨ b ⟩)
      -> (DivisionCount.k d1) == (DivisionCount.k d2)
  g p d1 d2 = f p (division-count->prime-div-count d1) (division-count->prime-div-count d2)
