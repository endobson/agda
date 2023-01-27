{-# OPTIONS --cubical --safe --exact-split #-}

module prime-div-count where

open import additive-group
open import additive-group.instances.nat
open import base
open import div
open import equality
open import gcd.propositional
open import lcm
open import nat
open import nat.order
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import prime
open import prime-gcd
open import relation
open import relatively-prime
open import ring.implementations
open import semiring
open import semiring.instances.nat


record PrimeDivCount (p : Prime') (a : Nat) (n : Nat)  : Type₀ where
  private
    p' = ⟨ p ⟩

  field
    %a : (prime-power p n) div' a
    upper-bound : ∀ m -> (prime-power p m) div' a -> m ≤ n

  r : Nat
  r = ⟨ %a ⟩

  r-path : r *' (prime-power p n) == a
  r-path = snd %a

  ¬p%r : ¬ (⟨ p ⟩ div' r)
  ¬p%r (x , x-path) = irrefl-< (upper-bound (suc n) (x , x-path2))
    where
    x-path2 : x * (prime-power p (suc n)) == a
    x-path2 =
      sym (*'-assoc {x}) >=>
      cong (_* (prime-power p n)) x-path >=>
      r-path


  a-pos : Pos' a
  a-pos = handle a refl
    where
    handle : (x : Nat) -> (x == a) -> Pos' a
    handle zero    path =
      bot-elim (irrefl-< (upper-bound (suc n) (0 , *-left-zeroᵉ (prime-power p (suc n)) >=> path)))
    handle (suc x) path = subst Pos' path tt


PrimeDivCount⁺ : Prime' -> Nat⁺ -> Nat -> Type₀
PrimeDivCount⁺ p (a , _) n = PrimeDivCount p a n

private
  OldPrimeDivCount : {p : Prime'} {a : Nat} {n : Nat} ->
                     (%a : (prime-power p n) div' a) ->
                     (¬ (⟨ p ⟩ div' ⟨ %a ⟩ )) -> PrimeDivCount p a n
  OldPrimeDivCount {p} %a ¬p%r = record
    { %a = %a
    ; upper-bound = prime-div-count-upper-bound p %a ¬p%r
    }
    where
    prime-div-count-upper-bound : (p : Prime') {a : Nat} {n : Nat} ->
                                  (%a : (prime-power p n) div' a) ->
                                  (¬ (⟨ p ⟩ div' ⟨ %a ⟩ )) ->
                                  (∀ m -> (prime-power p m) div' a -> m ≤ n)
    prime-div-count-upper-bound p {a} {n} %a ¬p%r m (x , x-path) = convert-≮ n≮m
      where
      p' = ⟨ p ⟩

      r : Nat
      r = ⟨ %a ⟩

      r-path : r *' (prime-power p n) == a
      r-path = snd %a

      n≮m : n ≮ m
      n≮m (i , i-path) = ¬p%r ((x * prime-power p i) , sym r-path2)
        where
        m-path : m == suc (i + n)
        m-path = sym i-path >=> +'-right-suc

        a-path : a == (x * (prime-power p (suc i))) * (prime-power p n)
        a-path =
          sym x-path >=>
          cong (x *_) (cong (prime-power p) m-path >=>
                       ^'-distrib-power {p'} {suc i} {n}) >=>
          sym (*'-assoc {x} {prime-power p (suc i)})

        r-path2 : r == (x * prime-power p i) * p'
        r-path2 = *'-right-injective (prime-power⁺ p n) (r-path >=> a-path) >=>
                  cong (x *_) (*'-commute {p'} {prime-power p i}) >=>
                  sym (*'-assoc {x} {prime-power p i})




prime-div-count-suc : {p : Prime'} {n : Nat} {a : Nat}
  -> PrimeDivCount p a n -> PrimeDivCount p (⟨ p ⟩ *' a) (suc n)
prime-div-count-suc {p@(p' , _)} {n} {a} dc = record
  { %a = dc.r , path
  ; upper-bound = upper-bound'
  }
  where
  module dc = PrimeDivCount dc

  path : dc.r *' (prime-power p (suc n)) == p' *' a
  path = sym (*'-assoc {dc.r} {p'})
         >=> *'-left (*'-commute {dc.r} {p'})
         >=> (*'-assoc {p'} {dc.r})
         >=> (*'-right {p'} dc.r-path)

  upper-bound' : ∀ m -> (prime-power p m) div' (p' * a) -> m ≤ (suc n)
  upper-bound' zero _ = zero-≤
  upper-bound' (suc m) (x , x-path) =
    suc-≤ (dc.upper-bound m (x , *'-left-injective (Prime'.nat⁺ p) (sym x-path2 >=> x-path)))
    where
    x-path2 : x *' (prime-power p (suc m)) == p' * (x *' (prime-power p m))
    x-path2 = sym (*'-assoc {x} {p'}) >=>
              cong (_* (prime-power p m)) (*'-commute {x} {p'}) >=>
              (*'-assoc {p'} {x})

¬div-prime-div-count : {p : Prime'} {a : Nat} -> ¬ (⟨ p ⟩ div' a) -> PrimeDivCount p a 0
¬div-prime-div-count {p} {a} ¬p%a = OldPrimeDivCount (a , *'-right-one) ¬p%a

private
  compute-prime-div-count' : (p : Prime') (a : Nat⁺) (bound : Nat)
                             -> (⟨ a ⟩ < bound)
                             -> Σ[ n ∈ Nat ] (PrimeDivCount p ⟨ a ⟩ n)
  compute-prime-div-count' p@(p' , _) a@(a' , a-pos) zero a<bound = bot-elim (zero-≮ a<bound)
  compute-prime-div-count' p@(p' , _) a@(a' , a-pos) (suc bound) a<sbound = handle (decide-div p' a')
    where
    handle : Dec (p' div' a') -> Σ[ n ∈ Nat ] (PrimeDivCount p a' n)
    handle (no ¬p%a) = 0 , ¬div-prime-div-count ¬p%a
    handle (yes p%a) = (suc n) , dc'
      where
      b = fst p%a
      b-path = snd p%a
      b⁺ = b , div'-pos->pos' p%a a-pos

      a≤bound : a' ≤ bound
      a≤bound = pred-≤ a<sbound
      b<a : b < a'
      b<a = (trans-=-< (sym *-right-one)
              (trans-<-= (*₁-preserves-< (Pos'->< (snd b⁺)) (Prime'.>1 p))
                         b-path))

      rec : Σ[ n ∈ Nat ] (PrimeDivCount p b n)
      rec = compute-prime-div-count' p b⁺ bound (trans-<-≤ b<a a≤bound)
      n = fst rec
      dc = snd rec

      pb==a : ⟨ p ⟩ *' b == a'
      pb==a = *'-commute {p'} {b} >=> b-path

      dc' : PrimeDivCount p a' (suc n)
      dc' = transport (\i -> PrimeDivCount p (pb==a i) (suc n))
                      (prime-div-count-suc dc)

compute-prime-div-count : (p : Prime') (a : Nat⁺) -> Σ[ n ∈ Nat ] (PrimeDivCount p ⟨ a ⟩ n)
compute-prime-div-count p a = compute-prime-div-count' p a (suc (fst a)) refl-≤

prime-div-count-unique : {p : Prime'} {a n1 n2 : Nat}
                         -> PrimeDivCount p a n1 -> PrimeDivCount p a n2
                         -> n1 == n2
prime-div-count-unique {p} {a} {n1} {n2} dc1 dc2 =
  antisym-≤ (dc2.upper-bound n1 dc1.%a) (dc1.upper-bound n2 dc2.%a)
  where
  module dc1 = PrimeDivCount dc1
  module dc2 = PrimeDivCount dc2

prime-power-div-count : (p : Prime') (n : Nat) -> PrimeDivCount p (prime-power p n) n
prime-power-div-count p n = OldPrimeDivCount div'-refl (Prime'.¬%1 p)


*'-prime-div-count : {a b : Nat}
  -> {p : Prime'}
  -> {na : Nat} (da : PrimeDivCount p a na)
  -> {nb : Nat} (db : PrimeDivCount p b nb)
  -> PrimeDivCount p (a *' b) (na +' nb)
*'-prime-div-count {a} {b} {p} {na} da {nb} db =
  OldPrimeDivCount (da.r *' db.r , path) ¬p%r
  where
  module da = PrimeDivCount da
  module db = PrimeDivCount db
  p' = ⟨ p ⟩

  path : (da.r *' db.r) *' (prime-power p (na +' nb)) == (a *' b)
  path =
    begin
      (da.r *' db.r) *' (prime-power p (na +' nb))
    ==<  *'-right {da.r *' db.r} (^'-distrib-power {p'} {na} {nb})  >
      (da.r *' db.r) *' ((prime-power p na) *' (prime-power p nb))
    ==< *'-assoc {da.r} {db.r} >
      da.r *' (db.r *' ((prime-power p na) *' (prime-power p nb)))
    ==< *'-right {da.r} (sym (*'-assoc {db.r} {prime-power p na}))>
      da.r *' ((db.r *' (prime-power p na)) *' (prime-power p nb))
    ==< *'-right {da.r} (*'-left (*'-commute {db.r} {prime-power p na}))>
      da.r *' (((prime-power p na) *' db.r) *' (prime-power p nb))
    ==< *'-right {da.r} (*'-assoc {prime-power p na} {db.r}) >
      da.r *' ((prime-power p na) *' (db.r *' (prime-power p nb)))
    ==< sym (*'-assoc {da.r} {prime-power p na}) >
      (da.r *' (prime-power p na)) *' (db.r *' (prime-power p nb))
    ==< (\i -> da.r-path i *' db.r-path i) >
      a *' b
    end

  ¬p%r : ¬ (⟨ p ⟩ div' (da.r *' db.r))
  ¬p%r p%r = handle (prime-divides-a-factor p p%r)
    where
    handle : ((⟨ p ⟩ div' da.r) ⊎ (⟨ p ⟩ div' db.r)) -> Bot
    handle (inj-l p%ar) = da.¬p%r p%ar
    handle (inj-r p%br) = db.¬p%r p%br


-- GCD/LCM prime div count at the propositional level
-- These are used to prove that the LCM exists

gcd-prime-div-count : {a b d : Nat}
  -> GCD' a b d
  -> (p : Prime')
  -> {na : Nat} (da : PrimeDivCount p a na)
  -> {nb : Nat} (db : PrimeDivCount p b nb)
  -> PrimeDivCount p d (min na nb)
gcd-prime-div-count {a} {b} {d} g p {na} da {nb} db =
  OldPrimeDivCount p^k%d ¬p%r
  where
  module da = PrimeDivCount da
  module db = PrimeDivCount db
  k = min na nb

  p^k%a : (prime-power p k) div' a
  p^k%a = div'-trans (div'-^' (≤-min-left {na} {nb})) (PrimeDivCount.%a da)
  p^k%b : (prime-power p k) div' b
  p^k%b = div'-trans (div'-^' (≤-min-right {na} {nb})) (PrimeDivCount.%a db)

  p^k%d : (prime-power p k) div' d
  p^k%d = (GCD'.f g (prime-power p k) p^k%a p^k%b)

  r = fst p^k%d
  r-path = snd p^k%d

  ¬p%r : ¬ (⟨ p ⟩ div' r)
  ¬p%r p%r = handle (split-min na nb)
    where
    x = fst p%r
    x-path = snd p%r

    p^sk%d : (prime-power p (suc k)) div' d
    p^sk%d = x , sym (*'-assoc {x} {⟨ p ⟩})
                 >=> *'-left x-path
                 >=> r-path

    handle : ((k == na) ⊎ (k == nb)) -> Bot
    handle (inj-l path) = irrefl-< (trans-<-= sk≤na (sym path))
      where
      p^sk%a : (prime-power p (suc k)) div' a
      p^sk%a = (div'-trans p^sk%d (GCD'.%a g))
      sk≤na : suc k ≤ na
      sk≤na = da.upper-bound (suc k) p^sk%a
    handle (inj-r path) = irrefl-< (trans-<-= sk≤nb (sym path))
      where
      p^sk%b : (prime-power p (suc k)) div' b
      p^sk%b = (div'-trans p^sk%d (GCD'.%b g))
      sk≤nb : suc k ≤ nb
      sk≤nb = db.upper-bound (suc k) p^sk%b


lcm-prime-div-count : {a b m : Nat}
  -> LCM' a b m
  -> (p : Prime')
  -> {na : Nat} (da : PrimeDivCount p a na)
  -> {nb : Nat} (db : PrimeDivCount p b nb)
  -> PrimeDivCount p m (max na nb)
lcm-prime-div-count {a} {b} {m} l p {na} da {nb} db =
  OldPrimeDivCount p^k%m ¬p%r
  where
  k = max na nb

  m-pos : Pos' m
  m-pos = LCM'.m-pos l (PrimeDivCount.a-pos da) (PrimeDivCount.a-pos db)


  xa = fst (PrimeDivCount.%a da)
  xa-path = snd (PrimeDivCount.%a da)
  xb = fst (PrimeDivCount.%a db)
  xb-path = snd (PrimeDivCount.%a db)

  ya = fst (LCM'.a%m l)
  ya-path = snd (LCM'.a%m l)
  yb = fst (LCM'.b%m l)
  yb-path = snd (LCM'.b%m l)

  p^k%m : (prime-power p k) div' m
  p^k%m = handle (split-max na nb)
    where
    handle : ((k == na) ⊎ (k == nb)) -> (prime-power p k) div' m
    handle (inj-l path) = div'-trans (transport (\i -> (prime-power p (path (~ i))) div' a)
                                                (PrimeDivCount.%a da))
                                     (LCM'.a%m l)
    handle (inj-r path) = div'-trans (transport (\i -> (prime-power p (path (~ i))) div' b)
                                                (PrimeDivCount.%a db))
                                     (LCM'.b%m l)
  r = fst p^k%m
  r-path = snd p^k%m

  ¬p%r : ¬ (⟨ p ⟩ div' r)
  ¬p%r p%r = Prime'.!=1 p (lcm-relatively-prime m-pos l ⟨ p ⟩ p%ya p%yb)
    where
    x = fst p%r
    x-path = snd p%r

    p%ya : ⟨ p ⟩ div' ya
    p%ya = euclids-lemma/rp p%prod (prime->relatively-prime p (PrimeDivCount.¬p%r da))
      where
      path : ((x *' ⟨ p ⟩) *' (prime-power p (nb -' (min na nb)))) *' (prime-power p na)
              == (ya *' xa) *' (prime-power p na)
      path =
        *'-assoc {x *' ⟨ p ⟩} {prime-power p (nb -' min na nb)}
        >=> *'-right {x *' ⟨ p ⟩} (sym (^'-distrib-power {⟨ p ⟩} {nb -' min na nb} {na}))
        >=> (\i -> (x *' ⟨ p ⟩) *'
                   (prime-power p ((+'-commute {nb -' (min na nb)} {na} >=> sym (max->min-path {na} {nb}))
                                   i)))
        >=> *'-left x-path
        >=> r-path
        >=> sym ya-path
        >=> *'-right {ya} (sym xa-path)
        >=> sym (*'-assoc {ya} {xa})

      p%prod : ⟨ p ⟩ div' (xa *' ya)
      p%prod = ((prime-power p (nb -' (min na nb))) *' x) ,
               *'-assoc {prime-power p (nb -' (min na nb))} {x} {⟨ p ⟩}
               >=> *'-commute {prime-power p (nb -' (min na nb))} {x *' ⟨ p ⟩}
               >=> *'-right-injective (prime-power⁺ p na) path
               >=> *'-commute {ya} {xa}


    p%yb : ⟨ p ⟩ div' yb
    p%yb = euclids-lemma/rp p%prod (prime->relatively-prime p (PrimeDivCount.¬p%r db))
      where
      path : ((x *' ⟨ p ⟩) *' (prime-power p (na -' (min nb na)))) *' (prime-power p nb)
              == (yb *' xb) *' (prime-power p nb)
      path =
        *'-assoc {x *' ⟨ p ⟩} {prime-power p (na -' min nb na)}
        >=> *'-right {x *' ⟨ p ⟩} (sym (^'-distrib-power {⟨ p ⟩} {na -' min nb na} {nb}))
        >=> (\i -> (x *' ⟨ p ⟩) *'
                   (prime-power p ((+'-commute {na -' (min nb na)} {nb}
                                    >=> sym (max->min-path {nb} {na})
                                    >=> max-commute {nb} {na})
                                   i)))
        >=> *'-left x-path
        >=> r-path
        >=> sym yb-path
        >=> *'-right {yb} (sym xb-path)
        >=> sym (*'-assoc {yb} {xb})

      p%prod : ⟨ p ⟩ div' (xb *' yb)
      p%prod = ((prime-power p (na -' (min nb na))) *' x) ,
               *'-assoc {prime-power p (na -' (min nb na))} {x} {⟨ p ⟩}
               >=> *'-commute {prime-power p (na -' (min nb na))} {x *' ⟨ p ⟩}
               >=> *'-right-injective (prime-power⁺ p nb) path
               >=> *'-commute {yb} {xb}
