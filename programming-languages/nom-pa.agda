{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.nom-pa where

open import base
open import equality
open import relation
open import functions
open import sum

abstract

  Binder : Type₀
  Binder = Nat


  data World : Type₀ where
    empty-world' : World
    world-cons' : Binder -> World -> World

  world-cons : Binder -> World -> World
  world-cons = world-cons'

  empty-world : World
  empty-world = empty-world'
  


  data Name : World -> Type₀ where
    name' : {w : World} -> (b : Binder) -> Name (world-cons b w)
    name-skip' : {w : World} -> (b : Binder) -> Name w -> Name (world-cons b w)

  ¬Name-empty-world : ¬ (Name empty-world)
  ¬Name-empty-world ()

  name : {w : World} -> (b : Binder) -> Name (world-cons b w) 
  name = name'

  name-skip : {w : World} -> (b : Binder) -> Name w -> Name (world-cons b w)
  name-skip = name-skip'

  private
    name!=skip : {w : World} {b : Binder} {n : Name w} -> name b != name-skip b n
    name!=skip p = transport (cong f p) tt
      where
      f : {w : World} -> Name w -> Type₀
      f (name' b) = Top
      f (name-skip' b _) = Bot

    name-skip-inj : {w : World} {b : Binder} -> Injective (name-skip {w} b)
    name-skip-inj {w} {b} p = inj-r-injective (cong f p)
      where
      f : Name (world-cons b w) -> Top ⊎ (Name w)
      f (name' _) = inj-l tt
      f (name-skip' _ n) = inj-r n

  Decidable-Name : {w : World} -> (a b : Name w) -> Dec (a == b)
  Decidable-Name {w = empty-world'} ()
  Decidable-Name {w = world-cons' b w} (name' b) (name' b) = yes (refl)
  Decidable-Name {w = world-cons' b w} (name' b) (name-skip' b n) =
    no name!=skip
  Decidable-Name {w = world-cons' b w} (name-skip' b n) (name' b) =
    no (name!=skip ∘ sym)
  Decidable-Name {w = world-cons' b w} (name-skip' b n1) (name-skip' b n2) =
    handle (Decidable-Name n1 n2)
    where
    handle : Dec (n1 == n2) -> Dec (name-skip b n1 == name-skip b n2)
    handle (yes p) = yes (cong (name-skip' b) p)
    handle (no ¬p) = no (¬p ∘ name-skip-inj)

  export-name : {b : Binder} {w : World} -> Name (world-cons b w) ->
                (Name (world-cons b empty-world)) ⊎ Name w
  export-name (name' b) = inj-l (name' b)
  export-name (name-skip' _ n) = inj-r n

  binder-zero : Binder
  binder-zero = zero
  binder-suc : Binder -> Binder
  binder-suc = suc

  data _#_ : REL Binder World ℓ-zero where
    #-empty' : {b : Binder} -> b # empty-world
    #-suc' : {b : Binder} {w : World} -> b # w -> (binder-suc b) # (world-cons b w)

  #-suc : {b : Binder} {w : World} -> b # w -> (binder-suc b) # (world-cons b w)
  #-suc = #-suc'


  data _W⊆_ : Rel World ℓ-zero where
    W⊆-refl' : {w : World} -> w W⊆ w
    W⊆-trans : {w1 w2 w3 : World} -> w1 W⊆ w2 -> w2 W⊆ w3 -> w1 W⊆ w3
    W⊆-empty : {w : World} -> empty-world W⊆ w
    W⊆-cons' : {w1 w2 : World} (b : Binder) -> w1 W⊆ w2 -> 
               (world-cons b w1) W⊆ (world-cons b w2)
    W⊆-#' : {w : World} (b : Binder) -> b # w -> w W⊆ (world-cons b w)

  W⊆-refl : {w : World} -> w W⊆ w
  W⊆-refl = W⊆-refl'

  W⊆-cons : {w1 w2 : World} (b : Binder) -> w1 W⊆ w2 -> 
            (world-cons b w1) W⊆ (world-cons b w2)
  W⊆-cons = W⊆-cons'

  W⊆-# : {w : World} (b : Binder) -> b # w -> w W⊆ (world-cons b w)
  W⊆-# = W⊆-#'


  coerce-name : {w1 w2 : World} -> w1 W⊆ w2 -> Name w1 -> Name w2
  coerce-name (W⊆-refl') n = n
  coerce-name (W⊆-trans w⊆1 w⊆2) = (coerce-name w⊆2) ∘ (coerce-name w⊆1)
  coerce-name (W⊆-empty) = bot-elim ∘ ¬Name-empty-world 
  coerce-name (W⊆-cons' b w⊆) (name' b) = (name' b)
  coerce-name (W⊆-cons' b w⊆) (name-skip' b n) = name-skip' b (coerce-name w⊆ n)
  coerce-name (W⊆-#' b b#w) = name-skip b 


data Tm (w : World) : Type₀ where
  var : Name w -> Tm w
  app : Tm w -> Tm w -> Tm w
  lam : (b : Binder) -> Tm (world-cons b w) -> Tm w

-- record TrKit (Env : (w1 w2 : World) -> Type₀) (Res : World -> Type₀) where
--   field
--     trName : {w1 w2 : World} -> Env w1 w2 -> Name w1 -> Res w2
--     trBinder : {w1 w2 : World} -> Env w1 w2 -> Binder -> Binder
--     extEnv : {w1 w2 : World} -> (b : Binder) -> (e : Env w1 w2) -> 



module _ where
  private
    Env : {ℓ : Level} -> World -> Type ℓ -> Type ℓ
    Env w1 res = Name w1 -> res

    --record Env (w : World) (res : Type ℓ) : Type ℓ where
    --  fields
    --    lookup 

    record Supply (w : World) : Type₀ where
      field
        binder : Binder
        binder# : binder # w

      next : Supply (world-cons binder w)
      next = record
        { binder = binder-suc binder
        ; binder# = #-suc binder#
        }

    -- Supply w = Top

  coerce-term : {w1 w2 : World} -> w1 W⊆ w2 -> Tm w1 -> Tm w2
  coerce-term inc (var n) = (var (coerce-name inc n))
  coerce-term inc (app f a) = (app (coerce-term inc f) (coerce-term inc a))
  coerce-term inc (lam v b) = (lam v (coerce-term (W⊆-cons v inc) b))


  subst-term : {w1 w2 : World} -> Env w1 (Tm w2) -> Supply w2 -> Tm w1 -> Tm w2
  subst-term env s (app f a) = (app (subst-term env s f) (subst-term env s a))
  subst-term env s (var name) = env name
  subst-term {w1} {w2} env s (lam v body) = (lam v2 (subst-term new-env s2 body))
    where
    module s = Supply s
    v2 = s.binder
    v2# = s.binder#
    s2 = s.next

    new-env : Env (world-cons v w1) (Tm (world-cons v2 w2))
    new-env n = handle (export-name n)
      where
      handle : ((Name (world-cons v empty-world)) ⊎ Name w1) -> (Tm (world-cons v2 w2))
      handle (inj-l _) = (var (name v2))
      handle (inj-r n) = (coerce-term (W⊆-# v2 v2#) (env n))

  subst-term2 : {w1 w2 : World} -> Env w1 (Tm w2) -> w1 W⊆ w2 -> Tm w1 -> Tm w2
  subst-term2 env inc (app f a) = (app (subst-term2 env inc f) (subst-term2 env inc a))
  subst-term2 env inc (var name) = env name
  subst-term2 {w1} {w2} env inc (lam v body) = (lam v ?)
  --   where
  --   module s = Supply s
  --   v2 = s.binder
  --   v2# = s.binder#
  --   s2 = s.next

  --   new-env : Env (world-cons v w1) (Tm (world-cons v2 w2))
  --   new-env n = handle (export-name n)
  --     where
  --     handle : ((Name (world-cons v empty-world)) ⊎ Name w1) -> (Tm (world-cons v2 w2))
  --     handle (inj-l _) = (var (name v2))
  --     handle (inj-r n) = (coerce-term (W⊆-# v2 v2#) (env n))

-- data β-Step : {w : World} -> Rel (Tm w) ℓ-zero where
--   β-step : (v : Binder) (b a : RawTerm) -> β-Step (app (lam v b) a) (subst-term v a b)
