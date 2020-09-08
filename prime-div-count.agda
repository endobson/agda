{-# OPTIONS --cubical --safe --exact-split #-}

module prime-div-count where

open import base
open import div
open import equality
open import gcd.propositional
open import gcd.euclidean-algorithm
open import lcm
open import nat
open import prime
open import prime-gcd
open import relation
open import relatively-prime
open import sigma


record PrimeDivCount (p : Prime') (a : Nat) (n : Nat)  : Type₀ where
  private
    p' = ⟨ p ⟩

  field
    %a : (prime-power p n) div' a

  r : Nat
  r = ⟨ %a ⟩

  r-path : r *' (prime-power p n) == a
  r-path = snd %a

  field
    ¬p%r : ¬ (⟨ p ⟩ div' r)

  ¬p^sn%a : ¬ (prime-power p (suc n) div' a)
  ¬p^sn%a (x , x-path) = ¬p%r (x , path')
    where
    path' : (x *' p') == r
    path' = *'-right-injective (prime-power⁺ p n) (*'-assoc {x} {p'} >=> x-path >=> sym r-path)

  a-pos : Pos' a
  a-pos = handle r refl
    where
    handle : (x : Nat) -> (x == r) -> Pos' a
    handle zero    path = bot-elim (¬p%r (transport (cong (p' div'_) path) div'-zero))
    handle (suc x) path = transport (cong Pos' r-path)
                                    (*'-Pos'-Pos' (transport (cong Pos' path) tt)
                                                             (snd (prime-power⁺ p n)))
PrimeDivCount⁺ : Prime' -> Nat⁺ -> Nat -> Type₀
PrimeDivCount⁺ p (a , _) n = PrimeDivCount p a n


prime-div-count-suc : {p : Prime'} {n : Nat} {a : Nat}
  -> PrimeDivCount p a n -> PrimeDivCount p (⟨ p ⟩ *' a) (suc n)
prime-div-count-suc {p@(p' , _)} {n} {a} dc = record
  { %a = dc.r , path
  ; ¬p%r = dc.¬p%r
  }
  where
  module dc = PrimeDivCount dc

  path : dc.r *' (prime-power p (suc n)) == p' *' a
  path = sym (*'-assoc {dc.r} {p'})
         >=> *'-left (*'-commute {dc.r} {p'})
         >=> (*'-assoc {p'} {dc.r})
         >=> (*'-right {p'} dc.r-path)

private
  compute-prime-div-count' : (p : Prime') (a : Nat⁺) (bound : Nat)
                             -> (⟨ a ⟩ < bound)
                             -> Σ[ n ∈ Nat ] (PrimeDivCount p ⟨ a ⟩ n)
  compute-prime-div-count' p@(p' , _) a@(a' , a-pos) zero a<bound = bot-elim (zero-≮ a<bound)
  compute-prime-div-count' p@(p' , _) a@(a' , a-pos) (suc bound) a<sbound = handle (decide-div p' a')
    where
    handle : Dec (p' div' a') -> Σ[ n ∈ Nat ] (PrimeDivCount p a' n)
    handle (no ¬p%a) = 0 , record { %a = (a' , *'-right-one) ; ¬p%r = ¬p%a}
    handle (yes p%a) = (suc n) , dc'
      where
      b = fst p%a
      b-path = snd p%a
      b⁺ = b , div'-pos->pos' p%a a-pos

      a≤bound : a' ≤ bound
      a≤bound = pred-≤ a<sbound
      b<a : b < a'
      b<a = *-prod-left-< (Prime'.>1 p) a b-path

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
compute-prime-div-count p a = compute-prime-div-count' p a (suc (fst a)) (same-≤ (suc (fst a)))

prime-div-count-unique : {p : Prime'} {a n1 n2 : Nat}
                         -> PrimeDivCount p a n1 -> PrimeDivCount p a n2
                         -> n1 == n2
prime-div-count-unique {p} {a} {zero} {zero} dc1 dc2 = refl
prime-div-count-unique {p} {a} {n1@(suc _)} {zero} dc1 dc2 =
  bot-elim (PrimeDivCount.¬p^sn%a dc2 p%a)
  where
  p%a : (prime-power p 1) div' a
  p%a = div'-trans (div'-^' {1} {n1} {⟨ p ⟩} (suc-≤ zero-≤)) (PrimeDivCount.%a dc1)
prime-div-count-unique {p} {a} {zero} {n2@(suc _)} dc1 dc2 =
  bot-elim (PrimeDivCount.¬p^sn%a dc1 p%a)
  where
  p%a : (prime-power p 1) div' a
  p%a = div'-trans (div'-^' {1} {n2} {⟨ p ⟩} (suc-≤ zero-≤)) (PrimeDivCount.%a dc2)
prime-div-count-unique {p} {a} {suc n1} {suc n2} dc1 dc2 = cong suc path
  where
  module dc1 = PrimeDivCount dc1
  module dc2 = PrimeDivCount dc2
  p' = ⟨ p ⟩

  p%a : p' div' a
  p%a = (prime-power p n1) *' dc1.r ,
        *'-commute {(prime-power p n1) *' dc1.r} {p'}
        >=> sym (*'-assoc {p'} {prime-power p n1})
        >=> *'-commute {prime-power p (suc n1)} {dc1.r}
        >=> dc1.r-path

  a' : Nat
  a' = fst p%a

  dc1' : PrimeDivCount p a' n1
  dc1' = record
    { %a = dc1.r , *'-left-injective (Prime'.nat⁺ p) path
    ; ¬p%r = dc1.¬p%r
    }
    where
    path : p' *' (dc1.r *' (prime-power p n1)) == p' *' a'
    path = sym (*'-assoc {p'} {dc1.r})
           >=> *'-left (*'-commute {p'} {dc1.r})
           >=> (*'-assoc {dc1.r} {p'})
           >=> dc1.r-path
           >=> sym (snd p%a ) >=> *'-commute {a'} {p'}

  dc2' : PrimeDivCount p a' n2
  dc2' = record
    { %a = dc2.r , *'-left-injective (Prime'.nat⁺ p) path
    ; ¬p%r = dc2.¬p%r
    }
    where
    path : p' *' (dc2.r *' (prime-power p n2)) == p' *' a'
    path = sym (*'-assoc {p'} {dc2.r})
           >=> *'-left (*'-commute {p'} {dc2.r})
           >=> (*'-assoc {dc2.r} {p'})
           >=> dc2.r-path
           >=> sym (snd p%a ) >=> *'-commute {a'} {p'}

  path : n1 == n2
  path = prime-div-count-unique {p} {a'} dc1' dc2'

prime-power-div-count : (p : Prime') (n : Nat) -> PrimeDivCount p (prime-power p n) n
prime-power-div-count p n = record
  { %a = div'-refl
  ; ¬p%r = Prime'.¬%1 p
  }

*'-prime-div-count : {a b : Nat}
  -> {p : Prime'}
  -> {na : Nat} (da : PrimeDivCount p a na)
  -> {nb : Nat} (db : PrimeDivCount p b nb)
  -> PrimeDivCount p (a *' b) (na +' nb)
*'-prime-div-count {a} {b} {p} {na} da {nb} db = record
  { %a = da.r *' db.r , path
  ; ¬p%r = ¬p%r
  }
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
gcd-prime-div-count {a} {b} {d} g p {na} da {nb} db = record
  { %a = p^k%d
  ; ¬p%r = ¬p%r
  }
  where
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
    handle (inj-l path) =
      PrimeDivCount.¬p^sn%a da (transport (\i -> (prime-power p (suc (path i))) div' a)
                                          (div'-trans p^sk%d (GCD'.%a g)))
    handle (inj-r path) =
      PrimeDivCount.¬p^sn%a db (transport (\i -> (prime-power p (suc (path i))) div' b)
                                          (div'-trans p^sk%d (GCD'.%b g)))

lcm-prime-div-count : {a b m : Nat}
  -> LCM' a b m
  -> (p : Prime')
  -> {na : Nat} (da : PrimeDivCount p a na)
  -> {nb : Nat} (db : PrimeDivCount p b nb)
  -> PrimeDivCount p m (max na nb)
lcm-prime-div-count {a} {b} {m} l p {na} da {nb} db = record
  { %a = p^k%m
  ; ¬p%r = ¬p%r
  }
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
