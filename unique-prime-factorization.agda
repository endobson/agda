{-# OPTIONS --cubical --safe --exact-split #-}

module unique-prime-factorization where

open import base
open import div
open import equality
open import gcd.computational
open import gcd.propositional
open import hlevel
open import isomorphism
open import nat
open import nat.order
open import order
open import order.instances.nat
open import prime
open import prime-div-count
open import prime-div-count.computational
open import prime-factorization
open import prime-gcd
open import relation
open import relatively-prime
open import semiring
open import semiring.exponentiation
open import semiring.instances.nat
open import sigma.base
open import univalence
open import unordered-list
open import unordered-list.discrete

open EqReasoning

private
  record DivisionCount (d : Nat) (n : Nat) : Type₀ where
    constructor division-count

    field
      d-pos : Pos' d
      n-pos : Pos' n
      k : Nat
      d^k%n : (d ^ℕ k) div' n
      ¬d^[suc-k]%n : ¬ ((d ^ℕ (suc k)) div' n)

    n⁺ : Nat⁺
    n⁺ = n , n-pos

    d⁺ : Nat⁺
    d⁺ = d , d-pos

    upper-bound : (k2 : Nat) -> ((d ^ℕ k2) div' n) -> k2 ≤ k
    upper-bound k2 d^k2%n = convert-≮ k≮k2
      where
      k≮k2 : k ≮ k2
      k≮k2 sk≤k2 = ¬d^[suc-k]%n (div'-trans (div'-^ℕ sk≤k2) d^k2%n)


  division-count-suc : {d n : Nat} -> DivisionCount d n -> DivisionCount d (d *' n)
  division-count-suc {d} {n} dc@(division-count d-pos n-pos k (x , pr) f) = record
    { d-pos        = d-pos
    ; n-pos        = *'-Pos'-Pos' {d} {n} d-pos n-pos
    ; k            = (suc k)
    ; d^k%n        = positive
    ; ¬d^[suc-k]%n = negative
    }
    where
    d^k = d ^ℕ k

    d⁺ = DivisionCount.d⁺ dc

    positive : (d ^ℕ (suc k)) div' (d *' n)
    positive = (x , adjusted-proof)
      where
      adjusted-proof : x *' (d *' d^k) == d *' n
      adjusted-proof = (sym (*'-assoc {x} {d})) >=> (*'-left (*'-commute {x} {d})) >=> (*'-assoc {d} {x})
                       >=> (cong (d *'_) pr)
    negative : ¬ ((d ^ℕ (suc (suc k))) div' (d *' n))
    negative (x , pr) = f d^sk%n
      where
      adjusted-proof : x *' d ^ℕ (suc k) == n
      adjusted-proof = *'-left-injective d⁺
        (begin
           d *' (x *' (d ^ℕ (suc k)))
         ==< (sym (*'-assoc {d} {x})) >
           (d *' x) *' (d ^ℕ (suc k))
         ==< (*'-left (*'-commute {d} {x})) >
           (x *' d) *' (d ^ℕ (suc k))
         ==< (*'-assoc {x} {d}) >
           x *' (d *' (d ^ℕ (suc k)))
         ==< pr >
           d *' n
         end)

      d^sk%n : (d ^ℕ (suc k)) div' n
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
    compute-division-count' d n (suc n') 1<d refl-≤


  isPropDivisionCount : {d n : Nat} -> isProp (DivisionCount d n)
  isPropDivisionCount {d} {n}
                      dc1@(division-count d-pos1 n-pos1 k1 div-k1 ¬div-sk1)
                      dc2@(division-count d-pos2 n-pos2 k2 div-k2 ¬div-sk2) i =
      (division-count
        (isProp->PathPᵉ (\i -> isPropPos') d-pos1 d-pos2 i)
        (isProp->PathPᵉ (\i -> isPropPos') n-pos1 n-pos2 i)
        (p-k i)
        (isProp->PathPᵉ (\i -> isPropDiv' {d ^ℕ (p-k i)} n1⁺) div-k1 div-k2 i)
        (isProp->PathPᵉ (\i -> isProp¬ ((d ^ℕ (suc (p-k i))) div' n)) ¬div-sk1 ¬div-sk2 i))
    where
      n1⁺ = DivisionCount.n⁺ dc1

      lesser-power : ∀ {k1 k2 n} -> ¬ ((d ^ℕ suc k1) div' n) -> (d ^ℕ k2) div' n -> k2 ≤ k1
      lesser-power {k1}     {zero}   {n} _    _ = zero-≤
      lesser-power {suc k1} {suc k2} {n} ¬div (x , pr) =
         suc-≤ (lesser-power ¬div-next div-next)
        where
        n' : Nat
        n' = x *' d ^ℕ k2

        div-next : (d ^ℕ k2) div' n'
        div-next = x , refl

        ¬div-next : ¬ ((d ^ℕ (suc k1)) div' n')
        ¬div-next (y , pr2) = ¬div proof
          where
          inner-pr : y *' (d ^ℕ (suc (suc k1))) == n
          inner-pr =
            begin
              y *' (d ^ℕ (suc (suc k1)))
            ==< (sym (*'-assoc {y} {d})) >
              (y *' d) *' (d ^ℕ (suc k1))
            ==< (*'-left (*'-commute {y})) >
              (d *' y) *' (d ^ℕ (suc k1))
            ==< (*'-assoc {d}) >
              d *' (y *' (d ^ℕ (suc k1)))
            ==< (cong (d *'_) pr2) >
              d *' (x *' d ^ℕ k2)
            ==< sym (*'-assoc {d}) >
              (d *' x) *' d ^ℕ k2
            ==< *'-left (*'-commute {d}) >
              (x *' d) *' d ^ℕ k2
            ==< *'-assoc {x}  >
              x *' (d *' d ^ℕ k2)
            ==< pr >
              n
            end

          proof : ((d ^ℕ (suc (suc k1))) div' n)
          proof = y , inner-pr


      lesser-power {zero}   {suc k2} {n} ¬div (x , pr) = bot-elim (¬d-div d-div)
        where
        d-proof : (x *' (d ^ℕ k2)) *' d == n
        d-proof = (*'-assoc {x}) >=> (*'-right {x} (*'-commute {d ^ℕ k2})) >=> pr

        d-div : (d div' n)
        d-div = (x *' (d ^ℕ k2)) , d-proof

        ¬d-div : ¬ (d div' n)
        ¬d-div = (transport (\i -> ¬ ((*'-right-one {d} i) div' n)) ¬div)

      proof-1 : k1 ≤ k2
      proof-1 = lesser-power ¬div-sk2 div-k1
      proof-2 : k2 ≤ k1
      proof-2 = lesser-power ¬div-sk1 div-k2
      p-k : k1 == k2
      p-k = (antisym-≤ proof-1 proof-2)

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
      ; ¬d^[suc-k]%n = transport (\i -> ¬(^ℕ-one {x = pv} (~ i) div' 1)) no-divides
      }
      where
      no-divides : ¬ (pv div' 1)
      no-divides pv%1 = irrefl-< (trans-≤-< (div'->≤ pv%1) p>1)

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
      path-part1 = isProp->PathP (\_ -> isPropDivisionCount)

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

      rp : RelativelyPrime⁰ (pv ^ℕ (suc k)) p2v
      rp = (rp-sym (relatively-prime-^ℕ (rp-sym rp') (suc k)))

      no-divides : ¬ ((pv ^ℕ (suc k)) div' (p2v *' n))
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
      middle-path1 = isProp->PathP (\_ -> isPropDivisionCount)

      middle-path2 :
        PathP (\i -> DivisionCount ⟨ p ⟩ (path2 i) )
        (compute-prime-division-count p (prime-product⁺ primes2))
        (compute-prime-division-count p n⁺)
      middle-path2 = isProp->PathP (\_ -> isPropDivisionCount)

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
    product-path = isProp->PathP (\i -> isSetNat _ _)

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


prime-div-count->division-count :
  {p : Prime'} {a n : Nat} -> PrimeDivCount p a n -> DivisionCount ⟨ p ⟩ a
prime-div-count->division-count {p} {a} {n} dc = record
  { d-pos = (Prime'.pos p)
  ; n-pos = (PrimeDivCount.a-pos dc)
  ; k = n
  ; d^k%n        = (PrimeDivCount.%a dc)
  ; ¬d^[suc-k]%n = \dsk%n -> irrefl-< (PrimeDivCount.upper-bound dc _ dsk%n)
  }

division-count->prime-div-count :
  {p : Prime'} {a : Nat} -> (dc : DivisionCount ⟨ p ⟩ a) -> PrimeDivCount p a (DivisionCount.k dc)
division-count->prime-div-count dc = record
  { %a = dc.d^k%n
  ; upper-bound = dc.upper-bound
  }
  where
  module dc = DivisionCount dc



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

prime-same-division-count⁺ : (a b : Nat⁺) ->
  ((p : Prime') -> prime-div-count p a == prime-div-count p b)
  -> a == b
prime-same-division-count⁺ a b f = ΣProp-path isPropPos' (prime-same-division-count a b g)
  where
  g : ((p : Prime') {d1 d2 : Nat}
      -> PrimeDivCount p ⟨ a ⟩ d1
      -> PrimeDivCount p ⟨ b ⟩ d2
      -> d1 == d2)
  g p {d1} {d2} dc1 dc2 =
    prime-div-count-unique dc1 (prime-div-count-proof p a)
    >=> (f p)
    >=> prime-div-count-unique (prime-div-count-proof p b) dc2

prime-different-division-count : (a b : Nat⁺) -> a <⁺ b
                                 -> Σ[ p ∈ Prime' ] (prime-div-count p a < prime-div-count p b)
prime-different-division-count a@(a' , a-pos) b@(b' , b-pos) a<b =
  p , (prime-div-count p db2⁺ , dc-full-path)
  where
  g = gcd⁺ a b
  g' = ⟨ g ⟩

  g%a : g div⁺ a
  g%a = GCD'.%a (gcd⁺-proof a b)

  g%b : g div⁺ b
  g%b = GCD'.%b (gcd⁺-proof a b)

  da = fst g%a
  db = fst g%b
  da⁺ = div⁺->multiple⁺ {g} {a} g%a
  db⁺ = div⁺->multiple⁺ {g} {b} g%b

  da-path : da *' g' == a'
  da-path = snd g%a
  da⁺-path : da⁺ *⁺ g == a
  da⁺-path = ΣProp-path isPropPos' da-path

  db-path : db *' g' == b'
  db-path = snd g%b
  db⁺-path : db⁺ *⁺ g == b
  db⁺-path = ΣProp-path isPropPos' db-path

  db>1 : db > 1
  db>1 = handle db refl
    where
    handle : (x : Nat) -> (x == db) -> db > 1
    handle zero path = bot-elim (transport (cong Pos' (sym path)) (snd db⁺))
    handle (suc (suc x)) path = x , +'-commute {x} {2} >=> path
    handle (suc zero) path = bot-elim (irrefl-< (trans-<-≤ a<b b≤a))
      where
      g=b : g' == b'
      g=b = sym *'-left-one >=> *'-left path >=> db-path

      b%a : b div⁺ a
      b%a = transport (\i -> (g=b i) div' a') g%a

      b≤a : b ≤⁺ a
      b≤a = div'->≤ b%a {a-pos}

  Σp : Σ[ p ∈ Prime' ] (⟨ p ⟩ div' db)
  Σp = exists-prime-divisor db>1

  p = fst Σp
  p%db = snd Σp
  p' = ⟨ p ⟩

  db2⁺ : Nat⁺
  db2⁺ = div⁺->multiple⁺ {Prime'.nat⁺ p} {db⁺} p%db

  ¬p%da : ¬( p' div' da)
  ¬p%da p%da = Prime'.!=1 p p'=1
    where
    pg%a : (p' *' g') div' a'
    pg%a = transport (\i -> (p' *' g') div' (da-path i)) (div'-mult-both p%da div'-refl)
    pg%b : (p' *' g') div' b'
    pg%b = transport (\i -> (p' *' g') div' (db-path i)) (div'-mult-both p%db div'-refl)

    pg%g : (p' *' g') div' g'
    pg%g = GCD'.f (gcd⁺-proof a b) (p' *' g') pg%a pg%b

    g%pg : g' div' (p' *' g')
    g%pg = p' , refl

    g=pg : g' == p' *' g'
    g=pg = div'-antisym g%pg pg%g

    p'=1 : p' == 1
    p'=1 = sym (*'-right-injective g (*'-left-one >=> g=pg))

  dc-a-path : prime-div-count p a == prime-div-count p g
  dc-a-path =
    cong (prime-div-count p) (sym da⁺-path)
    >=> *'-prime-div-count⁺ p da⁺ g
    >=> +'-left (zero-prime-div-count p ¬p%da)

  dc-b-path : prime-div-count p b == suc (prime-div-count p db2⁺) +' (prime-div-count p g)
  dc-b-path =
    cong (prime-div-count p) (sym db⁺-path)
    >=> *'-prime-div-count⁺ p db⁺ g
    >=> +'-left (suc-prime-div-count p p%db)

  dc-full-path : (prime-div-count p db2⁺) +' (suc (prime-div-count p a)) == prime-div-count p b
  dc-full-path =
    +'-right-suc
    >=> +'-right {suc (prime-div-count p db2⁺)} dc-a-path
    >=> sym dc-b-path
