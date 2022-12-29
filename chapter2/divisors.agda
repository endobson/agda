{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.divisors where

open import base
open import div hiding (remainder)
open import equality
open import equivalence
open import fin
open import finset
open import fin-algebra
open import finsubset
open import functions
open import gcd.properties
open import gcd.propositional using (GCD'; GCD⁺)
open import gcd.computational
open import hlevel
open import isomorphism
open import lcm
open import lcm.exists
open import list
open import list.nat
open import list.sorted
open import maybe
open import nat
open import nat.bounded
open import prime
open import prime-div-count
open import prime-div-count.computational
open import prime-gcd
open import quotient
open import relation
open import relatively-prime
open import ring.implementations
open import sigma
open import sigma.base
open import sum
open import type-algebra
open import unique-prime-factorization


import unordered-list as ul

private
  variable
    ℓ : Level
    A : Type ℓ


Divisor : Nat⁺ -> Type₀
Divisor (n , _) = Σ[ d ∈ Nat ] (d div' n)

-- private
module _ where
  isBoundedDiv' : (n : Nat⁺) -> isBounded (_div' ⟨ n ⟩)
  isBoundedDiv' (n , pos-n) = (suc n) , (\p -> suc-≤ (div'->≤ p {pos-n}))

private
  abstract
    isFinSet-Divisor : (n : Nat⁺) -> isFinSet (Σ Nat (_div' ⟨ n ⟩))
    isFinSet-Divisor n⁺@(n , _) =
      boundedDecidableProp->isFinSet (isBoundedDiv' n⁺) (\d -> decide-div d n) (isPropDiv' n⁺)

FinSet-Divisor : Nat⁺ -> FinSet ℓ-zero
FinSet-Divisor n = Divisor n , isFinSet-Divisor n

private
  divisors-full : (n : Nat⁺) -> Σ (List Nat) (CanonicalList≥ (_div' ⟨ n ⟩))
  divisors-full n = list-reify (isBoundedDiv' n) (\d -> decide-div d ⟨ n ⟩)

divisors : (n : Nat⁺) -> List Nat
divisors n = fst (divisors-full n)

divisors-canonical : (n : Nat⁺) -> (CanonicalList≥ (_div' ⟨ n ⟩) (divisors n))
divisors-canonical n = (snd (divisors-full n))

divisors-contains-only : (n : Nat⁺) -> (ContainsOnly (_div' ⟨ n ⟩) (divisors n))
divisors-contains-only n = fst (fst (fst (snd (divisors-full n))))

divisors-contains-all : (n : Nat⁺) -> (ContainsAll (_div' ⟨ n ⟩) (divisors n))
divisors-contains-all n = snd (fst (fst (snd (divisors-full n))))

divisors-no-duplicates : (n : Nat⁺) -> (NoDuplicates (divisors n))
divisors-no-duplicates n = snd (fst (snd (divisors-full n)))

num-divisors : (n : Nat⁺) -> Nat
num-divisors n = length (divisors n)

num-divisors⁺ : (n : Nat⁺) -> Nat⁺
num-divisors⁺ n = length (divisors n) , pos-n (divisors n) refl
  where
  pos-n : (divs : List Nat) -> (divs == divisors n) -> Pos' (length (divisors n))
  pos-n (_ :: _) p = transport (\i -> (Pos' (length (p i)))) tt
  pos-n [] p = bot-elim ([]-¬contains {x = 1} (transport (\i -> contains 1 (p (~ i))) div1))
    where
    div1 : contains 1 (divisors n)
    div1 = divisors-contains-all n div'-one


module _ where
  divisors-of-one : List Nat
  divisors-of-one = 1 :: []

  divisors-of-one-canonical : CanonicalList≥ (_div' 1) divisors-of-one
  divisors-of-one-canonical = ((c-o , c-a) , nd) , sorted
    where
    c-o : ContainsOnly (_div' 1) divisors-of-one
    c-o (0 , path) = transport (cong (_div' 1) (sym path)) div'-one
    c-a : ContainsAll (_div' 1) divisors-of-one
    c-a {d} (x , path) = (0 , (*'-only-one-right {x} {d} path))
    nd : NoDuplicates divisors-of-one
    nd = (\()) , lift tt
    sorted : Sorted _≥_ divisors-of-one
    sorted = (\()) , lift tt


  one-divisors-path : divisors 1⁺ == 1 :: []
  one-divisors-path = canonical-list-== (divisors-canonical 1⁺) divisors-of-one-canonical

  Divisor-one-eq : Divisor 1⁺ ≃ Top
  Divisor-one-eq = isoToEquiv i
    where
    open Iso
    i : Iso (Divisor 1⁺) Top
    i .fun _ = tt
    i .inv tt = 1 , div'-one
    i .rightInv _ = refl
    i .leftInv (d , d%1) = ΣProp-path (isPropDiv' 1⁺) (sym (div'-one->one d%1))


module _ (p : Prime') where
  private
    p' = ⟨ p ⟩
    p⁺ = (Prime'.nat⁺ p)
    is-prime = snd p

    divisors-of-prime : List Nat
    divisors-of-prime = p' :: 1 :: []

    divisors-of-prime-canonical : CanonicalList≥ (_div' p') divisors-of-prime
    divisors-of-prime-canonical = ((c-o , c-a) , nd) , sorted
      where
      c-o : ContainsOnly (_div' ⟨ p ⟩) divisors-of-prime
      c-o (0 , path) = transport (cong (_div' p') (sym path)) div'-refl
      c-o (1 , path) = transport (cong (_div' p') (sym path)) div'-one
      c-a : ContainsAll (_div' ⟨ p ⟩) divisors-of-prime
      c-a {d} dp = handle (prime-only-divisors p dp)
        where
        handle : (d == p' ⊎ d == 1) -> contains d divisors-of-prime
        handle (inj-l path) = (0 , path)
        handle (inj-r path) = (1 , path)
      nd : NoDuplicates divisors-of-prime
      nd = ((\{(0 , path) -> p!=1 path}) , (\()) , lift tt)
        where
        p!=1 : p' != 1
        p!=1 p==1 = <->!= (Prime'.>1 p) (sym p==1)
      sorted : Sorted _≥_ divisors-of-prime
      sorted = ((\{(0 , path) -> p≥a path}) , (\()) , lift tt)
        where
        p≥a : {a : Nat} -> (a == 1) -> p' ≥ a
        p≥a a==1 = transport (\i -> p' ≥ (a==1 (~ i))) (weaken-< (Prime'.>1 p))

  prime-divisors-path : divisors p⁺ == (p' :: 1 :: [])
  prime-divisors-path =
    canonical-list-== (divisors-canonical p⁺) divisors-of-prime-canonical

  Divisor-prime-eq : Divisor p⁺ ≃ Fin 2
  Divisor-prime-eq = isoToEquiv i
    where
    forward' : {d : Nat} -> d div' p' -> (d == p') ⊎ (d == 1) -> Fin 2
    forward' _ (inj-l _) = zero-fin
    forward' _ (inj-r _) = suc-fin zero-fin

    forward'-constant : (d : Divisor p⁺) -> 2-Constant (forward' (snd d))
    forward'-constant (d , d%p) (inj-l _) (inj-l _) = refl
    forward'-constant (d , d%p) (inj-l pa1) (inj-r pa2) =
      bot-elim (1-is-¬prime (subst IsPrime' (sym pa1 >=> pa2) is-prime))
    forward'-constant (d , d%p) (inj-r pa1) (inj-l pa2) =
      bot-elim (1-is-¬prime (subst IsPrime' (sym pa2 >=> pa1) is-prime))
    forward'-constant (d , d%p) (inj-r _) (inj-r _) = refl

    forward : (Divisor p⁺) -> Fin 2
    forward (d , d%p) = forward' d%p (prime-only-divisors p d%p)

    backward : Fin 2 -> (Divisor p⁺)
    backward (0 , lt) = p' , div'-refl
    backward (1 , lt) = 1 , div'-one
    backward ((suc (suc _)) , lt) = bot-elim (zero-≮ (pred-≤ (pred-≤ lt)))

    forward-backward : (i : Fin 2) -> (forward (backward i)) == i
    forward-backward (0 , lt) = path >=> fin-i-path refl
      where
      path : (forward (backward (0 , lt))) == zero-fin
      path = (forward'-constant (p' , div'-refl) _ (inj-l refl))
    forward-backward (1 , lt) = path >=> fin-i-path refl
      where
      path : (forward (backward (1 , lt))) == suc-fin zero-fin
      path = (forward'-constant (1 , div'-one) _ (inj-r refl))
    forward-backward ((suc (suc _)) , lt) = bot-elim (zero-≮ (pred-≤ (pred-≤ lt)))

    backward-forward : (d : Divisor p⁺) -> (backward (forward d)) == d
    backward-forward (d , d%p) = ΣProp-path (isPropDiv' p⁺) (handle (prime-only-divisors p d%p))
      where
      handle : (s : (d == p') ⊎ (d == 1)) -> fst (backward (forward' d%p s)) == d
      handle (inj-l pa) = sym pa
      handle (inj-r pa) = sym pa

    open Iso
    i : Iso (Divisor p⁺) (Fin 2)
    i .fun = forward
    i .inv = backward
    i .rightInv = forward-backward
    i .leftInv = backward-forward


-- Divisors of prime powers

module _ (p : Prime') where

  private
    p' = fst p
    is-prime = snd p
    p-pos = Prime'.pos p
    p⁺ = Prime'.nat⁺ p



module _ (p : Prime') where

  private
    p' = fst p
    is-prime = snd p
    p-pos = Prime'.pos p
    p⁺ = Prime'.nat⁺ p

    ¬p-divides->1 : (n : Nat) {d : Nat} -> d div' (prime-power p n)
                    -> ¬ (p' div' d) -> d == 1
    ¬p-divides->1 zero    {d} d%pn  _    = div'-one->one d%pn
    ¬p-divides->1 (suc n) {d} d%psn ¬d%p = ¬p-divides->1 n d%pn ¬d%p
      where
      d%pn : d div' (prime-power p n)
      d%pn = euclids-lemma/rp d%psn (rp-sym (prime->relatively-prime p ¬d%p))

    ¬p-divides->pn : (n x d : Nat) -> (x *' d == (prime-power p n))
                     -> ¬(p' div' x) -> d == (prime-power p n)
    ¬p-divides->pn n x d x-path ¬p%x =
      sym (*'-left-one {d}) >=> *'-left (sym x==1) >=> x-path
      where
      x==1 : x == 1
      x==1 = (¬p-divides->1 n (d , *'-commute {d} {x} >=> x-path) ¬p%x)


    p-divides->%pn : (n x d : Nat) -> (x *' d == (prime-power p (suc n)))
                     -> p' div' x -> d div' (prime-power p n)
    p-divides->%pn n x d x-path (z , z-path) =
      (z , *'-left-injective p⁺ path)
      where
      path : p' *' (z *' d) == (prime-power p (suc n))
      path = sym (*'-assoc {p'} {z} {d})
             >=> *'-left (*'-commute {p'} {z} >=> z-path)
             >=> x-path

  module _ (n : Nat) (d : Nat) where
    split-prime-power-divisor :
      d div' (prime-power p (suc n))
      -> (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
    split-prime-power-divisor (x , x-path) =
      handle (decide-div p' x)
      where
      handle : (Dec (p' div' x)) -> (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
      handle (yes p%x) = inj-r (p-divides->%pn n x d x-path p%x)
      handle (no ¬p%x) = inj-l (¬p-divides->pn (suc n) x d x-path ¬p%x)
    unsplit-prime-power-divisor :
      (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
      -> d div' (prime-power p (suc n))
    unsplit-prime-power-divisor (inj-l pa) =
      subst (\x -> x div' (prime-power p (suc n))) (sym pa) div'-refl
    unsplit-prime-power-divisor (inj-r d%pn) = div'-mult d%pn p'

    isProp-prime-power : isProp (d div' (prime-power p (suc n)))
    isProp-prime-power = isPropDiv' (prime-power⁺ p (suc n))

    isProp-split-prime-power : isProp (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
    isProp-split-prime-power = isProp⊎ (isSetNat _ _) (isPropDiv' (prime-power⁺ p n)) handle
      where
      handle : (d == (prime-power p (suc n))) -> ¬ (d div' (prime-power p n))
      handle path d%pn = same-≮ (trans-≤ gt lt)
        where
        lt : (prime-power p (suc n)) ≤ (prime-power p n)
        lt = div'->≤ (subst (\x -> x div' (prime-power p n)) path d%pn)
                     {snd (prime-power⁺ p n)}
        gt : (prime-power p (suc n)) > (prime-power p n)
        gt = ^-suc-< (Prime'.>1 p) n

    split-prime-power-eq : (d div' (prime-power p (suc n))) ≃
                           (d == (prime-power p (suc n)) ⊎ (d div' (prime-power p n)))
    split-prime-power-eq =
      isoToEquiv (isProp->iso split-prime-power-divisor
                              unsplit-prime-power-divisor
                              isProp-prime-power
                              isProp-split-prime-power)

  private

    Divisor-prime-power-suc-eq' :
      (n : Nat) -> Divisor (prime-power⁺ p (suc n)) ≃
                   (Top ⊎ (Divisor (prime-power⁺ p n)))
    Divisor-prime-power-suc-eq' n =
      existential-eq (split-prime-power-eq n)
      >eq> Σ-distrib-⊎
      >eq> ⊎-equiv top-eq (idEquiv _)
      where
      Σpath-prop : isProp (Σ[ d ∈ Nat ] d == (prime-power p (suc n)))
      Σpath-prop (d1 , path1) (d2 , path2) =
        ΣProp-path (isSetNat _ _) (path1 >=> (sym path2))

      top-eq : (Σ[ d ∈ Nat ] d == (prime-power p (suc n))) ≃ Top
      top-eq = (pathToEquiv (\i -> (∥-Prop Σpath-prop (~ i))))
               >eq> (∥-Top-eq ((prime-power p (suc n)) , refl))

    Divisor-prime-power-eq :
      (n : Nat) -> Divisor (prime-power⁺ p n) ≃ Fin (suc n)
    Divisor-prime-power-eq zero = Divisor-one-eq >eq> (equiv⁻¹ Fin-Top-eq)
    Divisor-prime-power-eq (suc n) =
      Divisor-prime-power-suc-eq' n
      >eq> (⊎-equiv (idEquiv _) (Divisor-prime-power-eq n))
      >eq> (equiv⁻¹ (Fin-suc-⊎-eq (suc n)))

  Divisor-prime-power-Maybe-eq :
    (n : Nat) -> Divisor (prime-power⁺ p (suc n)) ≃
                 (Maybe (Divisor (prime-power⁺ p n)))
  Divisor-prime-power-Maybe-eq n = isoToEquiv i
    where
    psn = prime-power p (suc n)


    switch : (d : Nat) -> (d%p : d div' psn) -> (Dec (p' div' ⟨ d%p ⟩)) ->
             (Maybe (Divisor (prime-power⁺ p n)))
    switch d (x , x-path) (yes p%x) = just (d , (p-divides->%pn n x d x-path p%x))
    switch d (x , x-path) (no ¬p%x) = nothing


    switch-psn : (d%p : psn div' psn) ->
                 (dec : (Dec (p' div' ⟨ d%p ⟩))) ->
                 switch psn d%p dec == nothing
    switch-psn d%p (no ¬p%x) = refl
    switch-psn (x , x-path) (yes p%x) = bot-elim (Prime'.¬%1 p (subst (p' div'_) path p%x))
      where
      path : x == 1
      path = *'-right-injective (prime-power⁺ p (suc n)) (x-path >=> sym (*'-left-one))

    switch-pn : (d : Nat) (d%p : d div' (prime-power p n)) ->
                (dec : (Dec (p' div' ⟨ div'-mult d%p p' ⟩))) ->
                switch d (div'-mult d%p p') dec == just (d , d%p)
    switch-pn d d%p (yes p%x) = cong f (isPropDiv' (prime-power⁺ p n) _ _)
      where
      f : (d div' (prime-power p n)) -> (Maybe (Divisor (prime-power⁺ p n)))
      f x = just (d , x)
    switch-pn d (x , x-path) (no ¬p%px) = bot-elim (¬p%px p%px)
      where
      p%px : (p' div' (p' *' x))
      p%px = x , *'-commute {x} {p'}


    split-prime-power-divisor' : Divisor (prime-power⁺ p (suc n))
                                 -> Maybe (Divisor (prime-power⁺ p n))
    split-prime-power-divisor' (d , d%p) = switch d d%p (decide-div p' ⟨ d%p ⟩)

    unsplit-prime-power-divisor' :
      Maybe (Divisor (prime-power⁺ p n))
      -> (Divisor (prime-power⁺ p (suc n)))
    unsplit-prime-power-divisor' nothing = (prime-power p (suc n)) , div'-refl
    unsplit-prime-power-divisor' (just (d , d%pn)) = d , div'-mult d%pn p'

    unsplit-switch : (d : Nat) -> (d%p : d div' psn) -> (dec : (Dec (p' div' ⟨ d%p ⟩))) ->
                     fst (unsplit-prime-power-divisor' (switch d d%p dec)) == d
    unsplit-switch d d%p (yes p%x) = refl
    unsplit-switch d (x , x-path) (no ¬p%x) = ans
      where
      x%psn : x div' psn
      x%psn = d , *'-commute {d} {x} >=> x-path

      path : x == 1
      path = ¬p-divides->1 (suc n) x%psn ¬p%x

      ans : psn == d
      ans = sym x-path >=> (\i -> path i *' d) >=> *'-left-one {d}



    open Iso
    i : Iso (Divisor (prime-power⁺ p (suc n))) (Maybe (Divisor (prime-power⁺ p n)))
    i .fun = split-prime-power-divisor'
    i .inv = unsplit-prime-power-divisor'
    i .rightInv nothing          = switch-psn div'-refl (decide-div p' 1)
    i .rightInv (just (d , d%p)) = switch-pn d d%p (decide-div p' ⟨ div'-mult d%p p' ⟩)
    i .leftInv (d , d%p) = ΣProp-path (isPropDiv' (prime-power⁺ p (suc n)))
                                      (unsplit-switch d d%p (decide-div p' ⟨ d%p ⟩))




  divisors-of-prime-power : Nat -> List Nat
  divisors-of-prime-power zero       = 1 :: []
  divisors-of-prime-power n@(suc n') = (p' ^' n) :: (divisors-of-prime-power n')

  private
    contains-only-divisors-of-prime-power : (n : Nat) ->
      ContainsOnly (_div' (p' ^' n)) (divisors-of-prime-power n)
    contains-only-divisors-of-prime-power zero    (0 , path) =
      (1 , *'-left-one >=> path)
    contains-only-divisors-of-prime-power (suc n) (0 , path) =
      (1 , *'-left-one >=> path)
    contains-only-divisors-of-prime-power (suc n) (suc i , path) =
      div'-mult (contains-only-divisors-of-prime-power n (i , path)) p'

    sorted>-divisors-of-prime-power : (n : Nat) -> Sorted _>_ (divisors-of-prime-power n)
    sorted>-divisors-of-prime-power zero = sorted-singleton _>_ 1
    sorted>-divisors-of-prime-power (suc n) =
      (>all , sorted>-divisors-of-prime-power n)
      where
      >all : ContainsOnly (_< (p' *' (p' ^' n))) (divisors-of-prime-power n)
      >all {x} c = trans-≤-< x-lt p-lt
        where
        x-div : x div' (p' ^' n)
        x-div = contains-only-divisors-of-prime-power n c
        x-lt : x ≤ (p' ^' n)
        x-lt = div'->≤ x-div {^'-Pos' (Prime'.pos p) n}
        p-lt : (p' ^' n) < (p' ^' (suc n))
        p-lt = ^-suc-< (Prime'.>1 p) n


  divisors-of-prime-power-canonical :
    (n : Nat) -> CanonicalList≥ (_div' (p' ^' n)) (divisors-of-prime-power n)
  divisors-of-prime-power-canonical zero = divisors-of-one-canonical
  divisors-of-prime-power-canonical (suc n) = ((c-o , c-a) , nd) , sorted
    where
    c-o = contains-only-divisors-of-prime-power (suc n)
    c-a : ContainsAll (_div' (p' *' (p' ^' n))) (divisors-of-prime-power (suc n))
    c-a {d} dp = handle (split-prime-power-divisor n d dp)
      where
      handle : (d == (⟨ p ⟩ *' (⟨ p ⟩ ^' n)) ⊎ d div' (⟨ p ⟩ ^' n))
               -> contains d (divisors-of-prime-power (suc n))
      handle (inj-l path) = (0 , path)
      handle (inj-r rec) =
        cons-contains (⟨ p ⟩ *' (⟨ p ⟩ ^' n))
                      (canonical-contains-all (divisors-of-prime-power-canonical n) rec)

    nd : NoDuplicates (divisors-of-prime-power (suc n))
    nd = sorted>->no-duplicates (sorted>-divisors-of-prime-power (suc n))
    sorted : Sorted _≥_ (divisors-of-prime-power (suc n))
    sorted = sorted>->sorted≥ (sorted>-divisors-of-prime-power (suc n))

  prime-power-divisors-path : (n : Nat) -> divisors (prime-power⁺ p n)
                                           == divisors-of-prime-power n
  prime-power-divisors-path n =
    canonical-list-== (divisors-canonical (prime-power⁺ p n)) (divisors-of-prime-power-canonical n)

-- Divisors of product
private
  lcm-divides-product : {d1 d2 a b m : Nat} -> d1 div' a -> d2 div' b -> LCM' d1 d2 m -> m div' (a *' b)
  lcm-divides-product {d1} {d2} {a} {b} {m} d1%a d2%b l =
    LCM'.f l (a *' b) (div'-mult' d1%a b) (div'-mult d2%b a)

  relatively-prime-lcm : {a b : Nat} -> RelativelyPrime⁰ a b -> LCM' a b (a *' b)
  relatively-prime-lcm {a} {b} rp = transport (\ i -> LCM' a b (path (~ i))) l
    where
    m = lcm a b
    l = lcm-proof a b

    path : (a *' b) == m
    path = lcm-gcd-prod-path a b
           >=> *'-right {lcm a b} (relatively-prime-gcd-path rp)
           >=> *'-right-one

  curry-*' : (Nat × Nat) -> Nat
  curry-*' (x , y) = x *' y


module _ (a b : Nat⁺) where
  private
    a' = ⟨ a ⟩
    b' = ⟨ b ⟩

    cp = cartesian-product (divisors a) (divisors b)

  *'-divisors : List Nat
  *'-divisors = cartesian-product' _*'_ (divisors a) (divisors b)

  *'-divisors-co : ContainsOnly (_div' (a' *' b')) *'-divisors
  *'-divisors-co {x} c = transport (\i -> (x-path i) div' (a' *' b')) xab%ab
    where
    c-info : Σ[ p ∈ (Nat × Nat) ]
               ((contains p cp) × (proj₁ p *' proj₂ p == x))
    c-info = map-contains' curry-*' cp c

    xa : Nat
    xa = proj₁ (fst c-info)
    xb : Nat
    xb = proj₂ (fst c-info)

    c-xs : (contains xa (divisors a)) × (contains xb (divisors b))
    c-xs = cartesian-product-contains' (divisors a) (divisors b) (fst (snd c-info))
    x-path : (xa *' xb == x)
    x-path = (snd (snd c-info))

    xa%a : xa div' a'
    xa%a = divisors-contains-only a (proj₁ c-xs)
    xb%b : xb div' b'
    xb%b = divisors-contains-only b (proj₂ c-xs)

    xab%ab : (xa *' xb) div' (a' *' b')
    xab%ab = div'-mult-both xa%a xb%b

  module _ (rp : RelativelyPrime⁺ a b) where
    *'-divisors-ca : ContainsAll (_div' (a' *' b')) *'-divisors
    *'-divisors-ca {x'} x%ab = transport (\i -> contains (path i) *'-divisors) c-dab
      where
      x : Nat⁺
      x = x' , div'-pos->pos x%ab (snd (a *⁺ b))

      da = gcd⁺ x a
      ga = gcd⁺-proof x a
      db = gcd⁺ x b
      gb = gcd⁺-proof x b
      da' = ⟨ da ⟩
      db' = ⟨ db ⟩

      gcd-xab : GCD⁺ x (a *⁺ b) x
      gcd-xab = record
        { %a = div'-refl
        ; %b = x%ab
        ; f = \z z%x _ -> z%x
        }

      rp2 : RelativelyPrime⁺ da db
      rp2 z z%da z%db = rp z (div'-trans z%da (GCD'.%b ga)) (div'-trans z%db (GCD'.%b gb))

      c-dab : contains ⟨ da *⁺ db ⟩ *'-divisors
      c-dab = map-contains curry-*' cp
                (cartesian-product-contains (divisors a) (divisors b)
                  (divisors-contains-all a (GCD'.%b ga))
                  (divisors-contains-all b (GCD'.%b gb)))

      path : (da' *' db') == x'
      path = prime-same-division-count (da *⁺ db) x f
        where
        f : (p : Prime') -> {n1 n2 : Nat}
            -> PrimeDivCount⁺ p (da *⁺ db) n1 -> PrimeDivCount⁺ p x n2
            -> n1 == n2
        f p {n1} {n2} dc1 dc2 =
          begin
            n1
          ==< prime-div-count-unique dc1 (prime-div-count-proof p (da *⁺ db)) >
             ρ (da *⁺ db)
          ==< cong ρ (sym (relatively-prime-lcm-path⁺ {da} {db} rp2)) >
            ρ (lcm⁺ da db)
          ==<>
            ρ (lcm⁺ (gcd⁺ x a) (gcd⁺ x b))
          ==< cong ρ (sym (gcd-distrib-lcm⁺ x a b)) >
            ρ (gcd⁺ x (lcm⁺ a b))
          ==< (\i -> (ρ (gcd⁺ x (relatively-prime-lcm-path⁺ {a} {b} rp i)))) >
            ρ (gcd⁺ x (a *⁺ b))
          ==< cong ρ (ΣProp-path isPropPos' (gcd'-unique gcd-xab)) >
            ρ x
          ==< prime-div-count-unique (prime-div-count-proof p x) dc2 >
            n2
          end
          where
          ρ : Nat⁺ -> Nat
          ρ = prime-div-count p

    different-div<  : {a1 a2 b1 b2 : Nat}
                      -> a1 div' a' -> a2 div' a' -> b1 div' b' -> b2 div' b'
                      -> a1 *' b1 == a2 *' b2
                      -> a1 < a2 -> Bot
    different-div< {a1} {a2} {b1} {b2} a1%a a2%a b1%b b2%b ab-path a1<a2 = <->!= dc-< dc-=
      where
      a1⁺ : Nat⁺
      a2⁺ : Nat⁺
      b1⁺ : Nat⁺
      b2⁺ : Nat⁺
      a1⁺ = a1 , div'-pos->pos a1%a (snd a)
      a2⁺ = a2 , div'-pos->pos a2%a (snd a)
      b1⁺ = b1 , div'-pos->pos b1%b (snd b)
      b2⁺ = b2 , div'-pos->pos b2%b (snd b)

      ab-path⁺ : (a1⁺ *⁺ b1⁺) == (a2⁺ *⁺ b2⁺)
      ab-path⁺ = ΣProp-path isPropPos' ab-path

      Σp : Σ[ p ∈ Prime' ] (prime-div-count p a1⁺ < prime-div-count p a2⁺)
      Σp = prime-different-division-count a1⁺ a2⁺ a1<a2

      p = fst Σp
      p' = ⟨ p ⟩
      dc-< = snd Σp

      p%a2 : p' div' a2
      p%a2 = prime-div-count->prime-div p a2⁺ (trans-≤-< zero-≤ dc-<)

      p%a : p' div' a'
      p%a = div'-trans p%a2 a2%a

      ¬p%b : ¬ (p' div' b')
      ¬p%b p%b = Prime'.!=1 p (rp p' p%a p%b)

      b-dc : prime-div-count p b == 0
      b-dc = zero-prime-div-count p ¬p%b

      b1-dc : prime-div-count p b1⁺ == 0
      b1-dc = zero-≤->zero (trans-≤ (div-prime-div-count b1%b p) (0 , b-dc))
      b2-dc : prime-div-count p b2⁺ == 0
      b2-dc = zero-≤->zero (trans-≤ (div-prime-div-count b2%b p) (0 , b-dc))

      dc-= : prime-div-count p a1⁺ == prime-div-count p a2⁺
      dc-= =
        begin
          ρ a1⁺
        ==< sym +'-right-zero >
          ρ a1⁺ +' 0
        ==< +'-right {ρ a1⁺} (sym b1-dc) >
          ρ a1⁺ +' ρ b1⁺
        ==< sym (*'-prime-div-count⁺ p a1⁺ b1⁺) >
          ρ (a1⁺ *⁺ b1⁺)
        ==< cong ρ ab-path⁺ >
          ρ (a2⁺ *⁺ b2⁺)
        ==< (*'-prime-div-count⁺ p a2⁺ b2⁺) >
          ρ a2⁺ +' ρ b2⁺
        ==< +'-right {ρ a2⁺} b2-dc >
          ρ a2⁺ +' 0
        ==< +'-right-zero >
          ρ a2⁺
        end
        where
        ρ = prime-div-count p




    different-div  : {a1 a2 b1 b2 : Nat}
                     -> a1 div' a' -> a2 div' a' -> b1 div' b' -> b2 div' b'
                     -> a1 *' b1 == a2 *' b2
                     -> a1 != a2 -> Bot
    different-div {a1} {a2} {b1} {b2} a1%a a2%a b1%b b2%b ab-path ¬ap = handle (split-nat< a1 a2)
      where
      handle : (a1 < a2 ⊎ a2 ≤ a1) -> Bot
      handle (inj-l a1<a2) = different-div< a1%a a2%a b1%b b2%b ab-path a1<a2
      handle (inj-r a2≤a1) = different-div< a2%a a1%a b2%b b1%b (sym ab-path)
                                           (strengthen-≤ a2≤a1 (¬ap ∘ sym))

    *'-divisors-ndi : NoDuplicatesIndex *'-divisors
    *'-divisors-ndi {x'} c1@(i1 , at-i1) c2@(i2 , at-i2) =
        handle (decide-nat q1 q2) (decide-nat r1 r2)
      where
      #d = (num-divisors⁺ b)
      q1 = quotient  i1 #d
      r1 = remainder i1 #d
      q2 = quotient  i2 #d
      r2 = remainder i2 #d

      d-as = (divisors a)
      d-bs = (divisors b)

      at-i1' : Σ[ ab ∈ (Nat × Nat) ] ((AtIndex i1 cp ab) ×
                                      (proj₁ ab *' proj₂ ab == x'))
      at-i1' = map-at-index' curry-*' cp at-i1

      at-i2' : Σ[ ab ∈ (Nat × Nat) ] ((AtIndex i2 cp ab) ×
                                      (proj₁ ab *' proj₂ ab == x'))
      at-i2' = map-at-index' curry-*' cp at-i2

      a1 = fst (fst at-i1')
      b1 = snd (fst at-i1')
      a2 = fst (fst at-i2')
      b2 = snd (fst at-i2')

      ab-path : a1 *' b1 == a2 *' b2
      ab-path = snd (snd at-i1') >=> sym (snd (snd at-i2'))

      at-q1 : AtIndex q1 d-as a1
      at-q1 = fst (cartesian-product-at-index' d-as d-bs (fst (snd at-i1')) (snd #d))
      at-q2 : AtIndex q2 d-as a2
      at-q2 = fst (cartesian-product-at-index' d-as d-bs (fst (snd at-i2')) (snd #d))
      at-r1 : AtIndex r1 d-bs b1
      at-r1 = snd (cartesian-product-at-index' d-as d-bs (fst (snd at-i1')) (snd #d))
      at-r2 : AtIndex r2 d-bs b2
      at-r2 = snd (cartesian-product-at-index' d-as d-bs (fst (snd at-i2')) (snd #d))

      a1%a : a1 div' a'
      a1%a = divisors-contains-only a (q1 , at-q1)
      a2%a : a2 div' a'
      a2%a = divisors-contains-only a (q2 , at-q2)
      b1%b : b1 div' b'
      b1%b = divisors-contains-only b (r1 , at-r1)
      b2%b : b2 div' b'
      b2%b = divisors-contains-only b (r2 , at-r2)


      handle : Dec (q1 == q2) -> Dec (r1 == r2) -> i1 == i2
      handle (yes qp) (yes rp) =
        begin
          i1
        ==< quotient-remainder-path #d >
          q1 *' ⟨ #d ⟩ +' r1
        ==< (\j -> (qp j) *' ⟨ #d ⟩ +' (rp j)) >
          q2 *' ⟨ #d ⟩ +' r2
        ==< sym (quotient-remainder-path #d) >
          i2
        end
      handle (yes qp) (no ¬rp) =
        bot-elim (¬rp (no-duplicates->no-duplicates-index (divisors-no-duplicates b)
                                                          (r1 , at-r1) (r2 , at-r2')))
        where
        ap : a1 == a2
        ap = same-at-index' d-as at-q1 at-q2 qp
        ab-path' : a1 *' b1 == a1 *' b2
        ab-path' = ab-path >=> (cong (_*' b2) (sym ap))
        a1-pos : Pos' a1
        a1-pos = div'-pos->pos a1%a (snd a)
        bp : b1 == b2
        bp = *'-left-injective (a1 , a1-pos) ab-path'

        at-r2' : AtIndex r2 d-bs b1
        at-r2' = transport (\j -> AtIndex r2 d-bs (bp (~ j))) at-r2

      handle (no ¬qp) (yes rp) =
        bot-elim (¬qp (no-duplicates->no-duplicates-index (divisors-no-duplicates a)
                                                          (q1 , at-q1) (q2 , at-q2')))
        where
        bp : b1 == b2
        bp = same-at-index' d-bs at-r1 at-r2 rp
        ab-path' : a1 *' b1 == a2 *' b1
        ab-path' = ab-path >=> (cong (a2 *'_) (sym bp))
        b1-pos : Pos' b1
        b1-pos = div'-pos->pos b1%b (snd b)
        ap : a1 == a2
        ap = *'-right-injective (b1 , b1-pos) ab-path'

        at-q2' : AtIndex q2 d-as a1
        at-q2' = transport (\j -> AtIndex q2 d-as (ap (~ j))) at-q2

      handle (no ¬qp) (no ¬rp) =
        bot-elim (different-div a1%a a2%a b1%b b2%b ab-path ¬ap)
        where
        ¬ap : a1 != a2
        ¬ap ap =
            ¬qp (no-duplicates->no-duplicates-index (divisors-no-duplicates a)
                                                    (q1 , at-q1) (q2 , at-q2'))
          where
          at-q2' : AtIndex q2 d-as a1
          at-q2' = transport (\j -> AtIndex q2 d-as (ap (~ j))) at-q2

        ¬bp : b1 != b2
        ¬bp bp =
            ¬rp (no-duplicates->no-duplicates-index (divisors-no-duplicates b)
                                                    (r1 , at-r1) (r2 , at-r2'))
          where
          at-r2' : AtIndex r2 d-bs b1
          at-r2' = transport (\j -> AtIndex r2 d-bs (bp (~ j))) at-r2

    *'-divisors-nd : NoDuplicates *'-divisors
    *'-divisors-nd = no-duplicates-index->no-duplicates *'-divisors-ndi

    *'-divisors-permutation : Permutation Nat *'-divisors (divisors (a *⁺ b))
    *'-divisors-permutation =
      contains-exactly-once->permutation
        ((*'-divisors-co , *'-divisors-ca) , *'-divisors-nd)
        (fst (divisors-canonical (a *⁺ b)))




module _ (a b : Nat⁺) where
  private
    a' = ⟨ a ⟩
    b' = ⟨ b ⟩
  module _ (rp : RelativelyPrime⁺ a b) where
    private
      forward : Divisor (a *⁺ b) -> (Divisor a × Divisor b)
      forward (d , d%ab) = (gcd' d a' , (GCD'.%b (gcd'-proof d a'))) ,
                           (gcd' d b' , (GCD'.%b (gcd'-proof d b')))

      backward : (Divisor a × Divisor b) -> Divisor (a *⁺ b)
      backward ((da , da%a) , (db , db%b)) = (da *' db , div'-mult-both da%a db%b)

      forward-backward₁' : (ds : Divisor a × Divisor b) ->
                           fst (proj₁ (forward (backward ds))) == fst (proj₁ ds)
      forward-backward₁' ((da , da%a) , (db , db%b)) = check
        where
        da⁺ : Nat⁺
        da⁺ = da , div'-pos->pos da%a (snd a)
        db⁺ : Nat⁺
        db⁺ = db , div'-pos->pos db%b (snd b)

        proof-a : GCD' da a' da
        proof-a = record
          { %a = div'-refl
          ; %b = da%a
          ; f = \ _ z%da _ -> z%da
          }

        proof-b : GCD' db a' 1
        proof-b = record
          { %a = div'-one
          ; %b = div'-one
          ; f = \ z z%db z%a -> subst (\x -> x div' 1) (sym (rp z z%a (div'-trans z%db db%b))) div'-refl
          }

        rp2 : RelativelyPrime⁺ da⁺ db⁺
        rp2 z z%da z%db = rp z (div'-trans z%da da%a) (div'-trans z%db db%b)

        path3 : gcd' a' (da *' db) == (gcd' a' da) *' (gcd' a' db)
        path3 = cong fst (Multiplicative-gcd⁺₁ a .snd da⁺ db⁺ rp2)

        path1 : gcd' (da *' db) a' == (gcd' da a') *' (gcd' db a')
        path1 = (gcd'-sym-path (da *' db) a') >=> path3
                >=> cong2 _*'_ (gcd'-sym-path a' da) (gcd'-sym-path a' db)

        path2 : (gcd' da a') *' (gcd' db a') == da
        path2 = cong2 _*'_ (gcd'-unique proof-a) (gcd'-unique proof-b)
                >=> *'-right-one

        check : gcd' (da *' db) a' == da
        check = path1 >=> path2

      forward-backward₂' : (ds : Divisor a × Divisor b) ->
                           fst (proj₂ (forward (backward ds))) == fst (proj₂ ds)
      forward-backward₂' ((da , da%a) , (db , db%b)) = check
        where
        da⁺ : Nat⁺
        da⁺ = da , div'-pos->pos da%a (snd a)
        db⁺ : Nat⁺
        db⁺ = db , div'-pos->pos db%b (snd b)

        proof-b : GCD' db b' db
        proof-b = record
          { %a = div'-refl
          ; %b = db%b
          ; f = \ _ z%db _ -> z%db
          }

        proof-a : GCD' da b' 1
        proof-a = record
          { %a = div'-one
          ; %b = div'-one
          ; f = \ z z%da z%b -> subst (\x -> x div' 1) (sym (rp z (div'-trans z%da da%a) z%b)) div'-refl
          }

        rp2 : RelativelyPrime⁺ da⁺ db⁺
        rp2 z z%da z%db = rp z (div'-trans z%da da%a) (div'-trans z%db db%b)

        path3 : gcd' b' (da *' db) == (gcd' b' da) *' (gcd' b' db)
        path3 = cong fst (Multiplicative-gcd⁺₁ b .snd da⁺ db⁺ rp2)

        path1 : gcd' (da *' db) b' == (gcd' da b') *' (gcd' db b')
        path1 = (gcd'-sym-path (da *' db) b') >=> path3
                >=> cong2 _*'_ (gcd'-sym-path b' da) (gcd'-sym-path b' db)

        path2 : (gcd' da b') *' (gcd' db b') == db
        path2 = cong2 _*'_ (gcd'-unique proof-a) (gcd'-unique proof-b)
                >=> *'-left-one

        check : gcd' (da *' db) b' == db
        check = path1 >=> path2


      forward-backward : (ds : Divisor a × Divisor b) -> (forward (backward ds)) == ds
      forward-backward ds@(da , db) =
        cong2 _,_
          (ΣProp-path (isPropDiv' a) (forward-backward₁' ds))
          (ΣProp-path (isPropDiv' b) (forward-backward₂' ds))

      backward-forward' : (d : Divisor (a *⁺ b)) -> fst (backward (forward d)) == fst d
      backward-forward' (d' , d%ab) = path1 >=> path2
        where
        gcd-dab : GCD' d' (a' *' b') d'
        gcd-dab = record
          { %a = div'-refl
          ; %b = d%ab
          ; f = \z z%d _ -> z%d
          }

        path1 : (gcd' d' a' *' gcd' d' b') == (gcd' d' (a' *' b'))
        path1 = sym (Multiplicative-gcd'₁ d' .snd a' b' rp)

        path2 : (gcd' d' (a' *' b')) == d'
        path2 = gcd'-unique gcd-dab



      backward-forward : (d : Divisor (a *⁺ b)) -> (backward (forward d)) == d
      backward-forward d = ΣProp-path (isPropDiv' (a *⁺ b)) (backward-forward' d)

    Divisor-*-eq : Divisor (a *⁺ b) ≃ (Divisor a × Divisor b)
    Divisor-*-eq = isoToEquiv (iso forward backward forward-backward backward-forward)

    Divisor-*-eq⁻¹ : (Divisor a × Divisor b) ≃ Divisor (a *⁺ b)
    Divisor-*-eq⁻¹ = isoToEquiv (iso backward forward backward-forward forward-backward)
