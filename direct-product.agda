{-# OPTIONS --cubical --safe --exact-split #-}

module direct-product where

open import base
open import commutative-monoid
open import equality
open import funext
open import group
open import heyting-field
open import hlevel
open import monoid
open import ring
open import semiring
open import vector-space

private
  variable
    ℓ ℓD ℓK ℓI : Level
    D K I : Type ℓ


record DirectProduct (D : Type ℓD) (I : Type ℓI) : Type (ℓ-max ℓI ℓD) where
  constructor direct-product-cons
  field
    f : I -> D

isSet-DirectProduct : (isSet D) -> isSet (DirectProduct D I)
isSet-DirectProduct h (direct-product-cons f1) (direct-product-cons f2) p1 p2 i j =
  direct-product-cons (isSetΠ (\_ -> h) f1 f2 (cong DirectProduct.f p1) (cong DirectProduct.f p2) i j)

private
  DP = DirectProduct

  wrap-dp : (I -> D) -> DP D I
  wrap-dp f = direct-product-cons f

  unwrap-dp : DP D I -> I -> D
  unwrap-dp (direct-product-cons f) = f

  dp-map0 : D -> DP D I
  dp-map0 d = wrap-dp (\_ -> d)

  dp-map1 : (D -> D) -> (DP D I) -> (DP D I)
  dp-map1 f dp1 = wrap-dp (\i -> f (unwrap-dp dp1 i))

  dp-map2 : (D -> D -> D) -> (DP D I) -> (DP D I) -> (DP D I)
  dp-map2 f dp1 dp2 = wrap-dp (\i -> f (unwrap-dp dp1 i) (unwrap-dp dp2 i))


module _ {ℓD ℓI : Level} {D : Type ℓD} (M : Monoid D) (I : Type ℓI) where
  private
    module M = Monoid M

    dpε : (DP D I)
    dpε = dp-map0 M.ε

    dp∙ : (DP D I) -> (DP D I) -> (DP D I)
    dp∙ = dp-map2 M._∙_

    dp∙-assoc : {x y z : DP D I} -> dp∙ (dp∙ x y) z == dp∙ x (dp∙ y z)
    dp∙-assoc {x} {y} {z} = cong wrap-dp (funExt (\_ -> M.∙-assoc))

    dp∙-left-ε : {x : DP D I} -> (dp∙ dpε x) == x
    dp∙-left-ε = cong wrap-dp (funExt (\_ -> M.∙-left-ε))
    dp∙-right-ε : {x : DP D I} -> (dp∙ x dpε) == x
    dp∙-right-ε = cong wrap-dp (funExt (\_ -> M.∙-right-ε))

  Monoid-DirectProduct : Monoid (DP D I)
  Monoid-DirectProduct = record
    { ε = dpε
    ; _∙_ = dp∙
    ; ∙-assoc = dp∙-assoc
    ; ∙-left-ε = dp∙-left-ε
    ; ∙-right-ε = dp∙-right-ε
    }


module _ {ℓD ℓI : Level} {D : Type ℓD} (M : CommMonoid D) (I : Type ℓI) where
  private
    module M = CommMonoid M
    MDP = (Monoid-DirectProduct M.monoid I)
    module MDP = Monoid MDP

    dp∙-commute : {x y : DP D I} -> x MDP.∙ y == y MDP.∙ x
    dp∙-commute {x} {y} = cong wrap-dp (funExt (\_ -> M.∙-commute))

  CommMonoid-DirectProduct : CommMonoid (DP D I)
  CommMonoid-DirectProduct = record
    { monoid = MDP
    ; ∙-commute = dp∙-commute
    }


module _ {ℓD ℓI : Level} {D : Type ℓD} (G : GroupStr D) (I : Type ℓI) where
  private
    module G = GroupStr G
    CMDP = (CommMonoid-DirectProduct G.comm-monoid I)
    module CMDP = CommMonoid CMDP

    inverse : (DP D I) -> (DP D I)
    inverse x = wrap-dp (\i -> G.inverse (unwrap-dp x i))
    dp∙-left-inverse : {x : DP D I} -> ((inverse x) CMDP.∙ x) == CMDP.ε
    dp∙-left-inverse = cong wrap-dp (funExt (\_ -> G.∙-left-inverse))

  GroupStr-DirectProduct : GroupStr (DP D I)
  GroupStr-DirectProduct = record
    { comm-monoid = CMDP
    ; isSet-Domain = isSet-DirectProduct G.isSet-Domain
    ; inverse = inverse
    ; ∙-left-inverse = dp∙-left-inverse
    }


-- module _ {ℓK ℓI : Level} {K : Type ℓK} {S : Semiring K} (R : Ring S) (I : Type ℓI) where
--   private
--     module R = Ring R
--     instance
--       IS = S
--       IR = R
--
--     GroupStr-DP = (GroupStr-DirectProduct R.+-Group I)
--     _dp+_ = GroupStr._∙_ GroupStr-DP
--
--     _dp*_ : K -> (DP K I) -> (DP K I)
--     _dp*_ d = dp-map1 (d *_)
--
--     dp*-distrib-dp+ : {k : K} -> {v1 v2 : DP K I} -> k dp* (v1 dp+ v2) == (k dp* v1) dp+ (k dp* v2)
--     dp*-distrib-dp+ = cong wrap-dp (funExt (\_ -> *-distrib-+-left))
--     dp*-distrib-+ : {k1 k2 : K} -> {v : DP K I} -> (k1 + k2) dp* v == (k1 dp* v) dp+ (k2 dp* v)
--     dp*-distrib-+ = cong wrap-dp (funExt (\_ -> *-distrib-+-right))
--     dp*-assoc : {k1 k2 : K} -> {v : DP K I} -> (k1 * k2) dp* v == k1 dp* (k2 dp* v)
--     dp*-assoc = cong wrap-dp (funExt (\_ -> *-assoc))
--     dp*-left-one : {v : DP K I} -> 1# dp* v == v
--     dp*-left-one = cong wrap-dp (funExt (\_ -> *-left-one))
--
--   ModuleStr-DirectProduct : ModuleStr R (DP K I) ℓI
--   ModuleStr-DirectProduct = record
--     { GroupStr-V = GroupStr-DP
--     ; _v*_ = _dp*_
--     ; v*-distrib-v+ = dp*-distrib-dp+
--     ; v*-distrib-+ = dp*-distrib-+
--     ; v*-assoc = dp*-assoc
--     ; v*-left-one = dp*-left-one
--     }
