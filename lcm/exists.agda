{-# OPTIONS --cubical --safe --exact-split #-}

module lcm.exists where

open import additive-group.instances.nat
open import base
open import div
open import equality
open import lcm
open import nat
open import nat.order
open import order
open import order.minmax
open import order.minmax.instances.nat
open import order.instances.nat
open import prime-power-factorization
open import prime-div-count
open import prime
open import semiring.exponentiation
open import semiring.instances.nat

private
  OPPF = OrderedPrimePowerFactorization

  lcm-exists-helper : {m : Nat} (p : Prime') (n : Nat⁺)
                      -> (c : Nat⁺)
                      -> ¬ (⟨ p ⟩ div' ⟨ c ⟩)
                      -> (b : Nat⁺)
                      -> LCM' ⟨ c ⟩ ⟨ b ⟩ m
                      -> Σ[ m ∈ Nat ] (LCM' ((prime-power p ⟨ n ⟩) *' ⟨ c ⟩) ⟨ b ⟩ m)
  lcm-exists-helper {mc} p@(p' , _) n@(n' , _) c⁺@(c , c-pos) ¬p%c b@(b' , b-pos) lc =
    handle split-max
    where

    Σdc-b : Σ[ n ∈ Nat ] (PrimeDivCount p b' n)
    Σdc-b = compute-prime-div-count p b
    n-b : Nat
    n-b = fst Σdc-b
    dc-b : PrimeDivCount p b' n-b
    dc-b = snd Σdc-b

    mc⁺ : Nat⁺
    mc⁺ = mc , LCM'.m-pos lc c-pos b-pos

    dc-c : PrimeDivCount p c 0
    dc-c = ¬div-prime-div-count ¬p%c

    dc-m : PrimeDivCount p mc n-b
    dc-m = subst (PrimeDivCount p mc) (max-≤-path zero-≤)
                 (lcm-prime-div-count lc p dc-c dc-b)

    handle : ((max n' n-b) == n') ⊎ ((max n' n-b) == n-b)
             -> Σ[ m ∈ Nat ] (LCM' ((prime-power p n') *' c) ⟨ b ⟩ m)
    handle (inj-l n-path) =
      (prime-power p n') *' r , record
        { a%m = a%m
        ; b%m = b%m
        ; f = f
        }
      where

      r = PrimeDivCount.r dc-m
      r-path : r *' (prime-power p n-b) == mc
      r-path = PrimeDivCount.r-path dc-m

      r⁺ : Nat⁺
      r⁺ = div⁺->multiple⁺ {prime-power⁺ p n-b} {mc⁺} (PrimeDivCount.%a dc-m)


      c%r : c div' r
      c%r = y-r , *'-left-injective (prime-power⁺ p n-y) full-path
        where
        c%mc : c div' mc
        c%mc = LCM'.a%m lc
        y = fst c%mc
        y-path : y *' c == mc
        y-path = snd c%mc
        y⁺ = div⁺->multiple⁺ {c⁺} {mc⁺} c%mc

        Σdc-y : Σ[ n ∈ Nat ] (PrimeDivCount p y n)
        Σdc-y = compute-prime-div-count p y⁺

        n-y = fst Σdc-y
        dc-y = snd Σdc-y
        y-r = PrimeDivCount.r dc-y
        y-r-path = PrimeDivCount.r-path dc-y

        dc-m-y : PrimeDivCount p mc n-y
        dc-m-y = transport (\i -> PrimeDivCount p (y-path i) (+'-right-zero {n-y} i))
                            (*'-prime-div-count dc-y dc-c)

        n-b==n-y : n-b == n-y
        n-b==n-y = prime-div-count-unique dc-m dc-m-y

        full-path : (prime-power p n-y) *' (y-r *' c) == (prime-power p n-y) *' r
        full-path =
          sym (*'-assoc {prime-power p n-y} {y-r})
          >=> *'-left (*'-commute {prime-power p n-y} {y-r} >=> y-r-path)
          >=> y-path
          >=> sym r-path
          >=> *'-commute {r} {prime-power p n-b}
          >=> *'-left (\i -> prime-power p (n-b==n-y i))

      a%m : ((prime-power p n') *' c) div' ((prime-power p n') *' r)
      a%m = div'-mult-both (div'-refl {prime-power p n'}) c%r


      mc%m : mc div' ((prime-power p n') *' r)
      mc%m = div'-trans mc%nb-r pp-r-div
        where
        mc%nb-r : mc div' ((prime-power p n-b) *' r)
        mc%nb-r = 1 , *'-left-one >=> (sym r-path) >=> *'-commute {r} {prime-power p n-b}
        n-b≤n' : n-b ≤ n'
        n-b≤n' = transport (\i -> n-b ≤ n-path i) max-≤-right


        pp-r-div : ((prime-power p n-b) *' r) div' ((prime-power p n') *' r)
        pp-r-div = div'-mult-both (div'-^ℕ n-b≤n') div'-refl

      b%m : b' div' ((prime-power p n') *' r)
      b%m = div'-trans (LCM'.b%m lc) mc%m


      f : (x : Nat) -> (((prime-power p n') *' c) div' x) -> (b' div' x)
                    -> ((prime-power p n') *' r) div' x
      f zero _ _ = div'-zero
      f x@(suc _) p^nc%x b%x = p^nr%x
        where

        m%x : mc div' x
        m%x = LCM'.f lc x (div'-trans (div'-mult div'-refl (prime-power p n')) p^nc%x) b%x

        nb-r%x : ((prime-power p n-b) *' r) div' x
        nb-r%x = transport (\ i -> ((sym r-path >=> *'-commute {r} {prime-power p n-b}) i) div' x) m%x

        r%x : r div' x
        r%x = div'-trans (div'-mult div'-refl (prime-power p n-b)) nb-r%x

        z = fst r%x
        z-path : (z *' r) == x
        z-path = snd r%x
        z⁺ : Nat⁺
        z⁺ = div⁺->multiple⁺ {r⁺} r%x

        w = fst p^nc%x
        w-path : (w *' ((prime-power p n') *' c)) == x
        w-path = snd p^nc%x
        w⁺ : Nat⁺
        w⁺ = div⁺->multiple⁺ {(prime-power⁺ p n') *⁺ c⁺} p^nc%x

        Σdc-z : Σ[ n ∈ Nat ] (PrimeDivCount p z n)
        Σdc-z = compute-prime-div-count p z⁺
        n-z = fst Σdc-z
        dc-z = snd Σdc-z

        Σdc-w : Σ[ n ∈ Nat ] (PrimeDivCount p w n)
        Σdc-w = compute-prime-div-count p w⁺
        n-w = fst Σdc-w
        dc-w = snd Σdc-w

        dc-pnc : PrimeDivCount p ((prime-power p n') *' c) n'
        dc-pnc =
          transport (\i -> PrimeDivCount p ((prime-power p n') *' c) (+'-right-zero {n'} i))
                    (*'-prime-div-count (prime-power-div-count p n') dc-c)

        dc-x1 : PrimeDivCount p x (n-w +' n')
        dc-x1 =
          transport (\i -> PrimeDivCount p (w-path i) (n-w +' n'))
                    (*'-prime-div-count dc-w dc-pnc)

        dc-r : PrimeDivCount p r 0
        dc-r = ¬div-prime-div-count (PrimeDivCount.¬p%r dc-m)

        dc-x2 : PrimeDivCount p x n-z
        dc-x2 =
          transport (\i -> PrimeDivCount p (z-path i) (+'-right-zero {n-z} i))
                    (*'-prime-div-count dc-z dc-r)

        n-z-path : n-z == (n-w +' n')
        n-z-path = prime-div-count-unique dc-x2 dc-x1


        p^nr%x : ((prime-power p n') *' r) div' x
        p^nr%x = z-r *' (prime-power p n-w) , path
          where
          z-r = PrimeDivCount.r dc-z
          path : (z-r *' (prime-power p n-w)) *' ((prime-power p n') *' r) == x
          path =
            *'-assoc {z-r} {prime-power p n-w}
            >=> *'-right {z-r} (sym (*'-assoc {prime-power p n-w} {prime-power p n'} {r}))
            >=> *'-right {z-r} (*'-left (sym (^ℕ-distrib-+-left n-w n')))
            >=> (\i -> z-r *' ((prime-power p (n-z-path (~ i))) *' r))
            >=> sym (*'-assoc {z-r} {prime-power p n-z})
            >=> *'-left (PrimeDivCount.r-path dc-z)
            >=> z-path



    handle (inj-r n-path) =
      mc , record
        { a%m = a%m
        ; b%m = b%m
        ; f = f
        }
      where

      a%m : ((prime-power p n') *' c) div' mc
      a%m = p^nc%mc
        where
        c%mc : c div' mc
        c%mc = LCM'.a%m lc
        y = fst c%mc
        y-path : y *' c == mc
        y-path = snd c%mc
        y⁺ = div⁺->multiple⁺ {c⁺} {mc⁺} c%mc

        Σdc-y : Σ[ n ∈ Nat ] (PrimeDivCount p y n)
        Σdc-y = compute-prime-div-count p y⁺

        n-y = fst Σdc-y
        dc-y = snd Σdc-y

        dc-m-y : PrimeDivCount p mc n-y
        dc-m-y = transport (\i -> PrimeDivCount p (y-path i) (+'-right-zero {n-y} i))
                           (*'-prime-div-count dc-y dc-c)

        n-b==n-y : n-b == n-y
        n-b==n-y = prime-div-count-unique dc-m dc-m-y

        p^n%y : (prime-power p n') div' y
        p^n%y =
          div'-trans (transport (\i -> (prime-power p n') div' (prime-power p (path i)))
                                (div'-^ℕ max-≤-left))
                     (PrimeDivCount.%a dc-y)
          where
          path : (max n' n-b) == n-y
          path = n-path >=> n-b==n-y

        p^nc%mc : ((prime-power p n') *' c) div' mc
        p^nc%mc = x , path
          where
          x = fst p^n%y
          path : x *' ((prime-power p n') *' c) == mc
          path = sym (*'-assoc {x} {prime-power p n'}) >=> *'-left (snd p^n%y) >=> y-path


      b%m : b' div' mc
      b%m = LCM'.b%m lc

      f : (x : Nat) -> (((prime-power p n') *' c) div' x) -> (b' div' x)
                    -> (mc div' x)
      f x p^nc%x b%x = LCM'.f lc x (div'-trans (div'-mult div'-refl (prime-power p n')) p^nc%x) b%x


  lcm-exists⁺ : {a : Nat} -> OPPF a -> (b : Nat⁺) -> Σ[ m ∈ Nat ] (LCM' a ⟨ b ⟩ m)
  lcm-exists⁺ {a} oppf-[] (b' , _) = b' , record
    { a%m = div'-one
    ; b%m = div'-refl
    ; f = \x _ x%b -> x%b
    }
  lcm-exists⁺ {a} (oppf-cons {c} p@(p' , _) n@(n' , _) ¬p%c oppf-c) b@(b' , b-pos) =
    lcm-exists-helper p n (c , oppf->pos oppf-c) ¬p%c b (snd (lcm-exists⁺ oppf-c b))

lcm-exists : (a b : Nat) -> Σ[ m ∈ Nat ] (LCM' a b m)
lcm-exists a           zero    = 0 , lcm-sym lcm-zero
lcm-exists zero      b@(suc _) = 0 , lcm-zero
lcm-exists a@(suc _) b@(suc _) = lcm-exists⁺ (compute-oppf (a , tt)) (b , tt)

lcm : Nat -> Nat -> Nat
lcm a b = fst (lcm-exists a b)

lcm-proof : (a b : Nat) -> LCM' a b (lcm a b)
lcm-proof a b = snd (lcm-exists a b)

lcm⁺ : Nat⁺ -> Nat⁺ -> Nat⁺
lcm⁺ (a , a-pos) (b , b-pos) = fst (lcm-exists a b) , LCM'.m-pos (snd (lcm-exists a b)) a-pos b-pos

lcm⁺-proof : (a b : Nat⁺) -> LCM⁺ a b (lcm⁺ a b)
lcm⁺-proof (a , _) (b , _) = snd (lcm-exists a b)
