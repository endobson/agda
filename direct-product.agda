{-# OPTIONS --cubical --safe --exact-split #-}

module direct-product where

open import additive-group
open import additive-group.apartness
open import apartness
open import base
open import commutative-monoid
open import equality hiding (J)
open import fin
open import funext
open import functions
open import group
open import heyting-field
open import hlevel
open import monoid
open import relation
open import ring
open import semiring
open import sum
open import truncation
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
isSet-DirectProduct h = isSet-Retract DirectProduct.f direct-product-cons (\_ -> refl) (isSetΠ (\_ -> h))


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

  dp-ext : {dp1 dp2 : DP D I} -> ((i : I) -> (unwrap-dp dp1 i) == (unwrap-dp dp2 i)) -> dp1 == dp2
  dp-ext = cong wrap-dp ∘ funExt

direct-product-index : DP D I -> I -> D
direct-product-index = unwrap-dp

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
    ; isSet-Domain = isSet-DirectProduct M.isSet-Domain
    }

  Monoidʰ-direct-product-index :
    (i : I) -> Monoidʰᵉ Monoid-DirectProduct M (\dp -> direct-product-index dp i)
  Monoidʰ-direct-product-index i = record
    { preserves-ε = refl
    ; preserves-∙ = \x y -> refl
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

  CommMonoidʰ-direct-product-index :
    (i : I) -> CommMonoidʰᵉ CommMonoid-DirectProduct M (\dp -> direct-product-index dp i)
  CommMonoidʰ-direct-product-index i = record
    { monoidʰ = Monoidʰ-direct-product-index M.monoid I i
    }


module _ {ℓD ℓI : Level} {D : Type ℓD} (G : AbGroupStr D) (I : Type ℓI) where
  private
    module G = AbGroupStr G
    CMDP = (CommMonoid-DirectProduct G.comm-monoid I)
    module CMDP = CommMonoid CMDP

    inverse : (DP D I) -> (DP D I)
    inverse x = wrap-dp (\i -> G.inverse (unwrap-dp x i))
    dp∙-left-inverse : {x : DP D I} -> ((inverse x) CMDP.∙ x) == CMDP.ε
    dp∙-left-inverse = cong wrap-dp (funExt (\_ -> G.∙-left-inverse))
    dp∙-right-inverse : {x : DP D I} -> (x CMDP.∙ (inverse x)) == CMDP.ε
    dp∙-right-inverse = cong wrap-dp (funExt (\_ -> G.∙-right-inverse))

  AbGroupStr-DirectProduct : AbGroupStr (DP D I)
  AbGroupStr-DirectProduct = record
    { comm-monoid = CMDP
    ; inverse = inverse
    ; ∙-left-inverse = dp∙-left-inverse
    ; ∙-right-inverse = dp∙-right-inverse
    }

module _ {ℓD ℓI ℓ# : Level} {D : Type ℓD} {D# : Rel D ℓ#}
         (TD : isTightApartness D#) (I : Type ℓI) where
  private
    instance
      ITD = TD

    _dp#'_ : Rel (DP D I) _
    _dp#'_ dp1 dp2 = Σ[ i ∈ I ] ((unwrap-dp dp1 i) # (unwrap-dp dp2 i))

    _dp#_ : Rel (DP D I) _
    _dp#_ dp1 dp2 = ∥ dp1 dp#' dp2 ∥

    abstract
      tight-dp# : Tight _dp#_
      tight-dp# {a} {b} ¬a#b = cong wrap-dp (funExt (\i -> tight-# (¬ai#bi i)))
        where
        ¬ai#bi : (i : I) -> ¬ ((unwrap-dp a i) # (unwrap-dp b i))
        ¬ai#bi i ai#bi = ¬a#b ∣ i , ai#bi ∣

      irrefl-dp# : Irreflexive _dp#_
      irrefl-dp# a#a = unsquash isPropBot (∥-map (\ (i , a#a) -> irrefl-# a#a) a#a)

      sym-dp# : Symmetric _dp#_
      sym-dp# = ∥-map (\ (i , a#b) -> i , (sym-# a#b))

      comparison-dp# : Comparison _dp#_
      comparison-dp# a b c = ∥-bind handle
        where
        handle : (a dp#' c) -> ∥ (a dp# b) ⊎ (b dp# c) ∥
        handle (i , ai#ci) =
          ∥-map
            (⊎-map (\a#b -> ∣ i , a#b ∣) (\b#c -> ∣ i , b#c ∣))
            (comparison-# (unwrap-dp a i) (unwrap-dp b i) (unwrap-dp c i) ai#ci)

  isTightApartness-DirectProduct : isTightApartness _dp#_
  isTightApartness-DirectProduct = record
    { tight-# = tight-dp#
    ; irrefl-# = irrefl-dp#
    ; sym-# = sym-dp#
    ; comparison-# = comparison-dp#
    ; isProp-# = squash
    }

module _ {ℓK ℓI : Level} {K : Type ℓK} (ACM : AdditiveCommMonoid K) (I : Type ℓI) where
  AdditiveCommMonoid-DirectProduct : AdditiveCommMonoid (DP K I)
  AdditiveCommMonoid-DirectProduct = record
    { comm-monoid = (CommMonoid-DirectProduct (AdditiveCommMonoid.comm-monoid ACM) I)
    }

module _ {ℓK ℓI : Level} {K : Type ℓK} {ACM : AdditiveCommMonoid K}
         (AG : AdditiveGroup ACM) (I : Type ℓI) where
  private
    instance
      ACM-DP = AdditiveCommMonoid-DirectProduct ACM I
      IAG = AG

    dp-_ : DP K I -> DP K I
    dp-_ = dp-map1 -_

    dp+-inverse : (v : DP K I) -> (v + (dp- v)) == 0#
    dp+-inverse _ = dp-ext (\_ -> +-inverse)

  AdditiveGroup-DirectProduct : AdditiveGroup ACM-DP
  AdditiveGroup-DirectProduct = record
    { -_ = dp-_
    ; +-inverse = \{v} -> dp+-inverse v
    }


module _ {ℓK ℓI ℓ# : Level} {K : Type ℓK} {K# : Rel K ℓ#}
         {ACM : AdditiveCommMonoid K} {TA : isTightApartness K#}
         (AACM : ApartAdditiveCommMonoid ACM TA) (I : Type ℓI) where
  private
    instance
      IACM = ACM
      IAACM = AACM
      ITA = TA
      ACM-DP = AdditiveCommMonoid-DirectProduct ACM I
      TA-DP = isTightApartness-DirectProduct TA I

    dp+₁-preserves-# : {v1 v2 v3 : DP K I} -> v2 # v3 -> (v1 + v2) # (v1 + v3)
    dp+₁-preserves-# = ∥-map \ (i , a) -> (i , +₁-preserves-# a)

    dp+₁-reflects-# : {v1 v2 v3 : DP K I} -> (v1 + v2) # (v1 + v3) -> v2 # v3
    dp+₁-reflects-# = ∥-map \ (i , a) -> (i , +₁-reflects-# a)

  ApartAdditiveCommMonoid-DirectProduct : ApartAdditiveCommMonoid ACM-DP TA-DP
  ApartAdditiveCommMonoid-DirectProduct = record
    { StronglyInjective-+₁ = \_ -> dp+₁-preserves-#
    ; StronglyExtensional-+₁ = \_ -> dp+₁-reflects-#
    }


module _ {ℓK ℓI : Level} {K : Type ℓK}
         {ACM : AdditiveCommMonoid K} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         (R : Ring S AG) (I : Type ℓI) where
  private
    module R = Ring R
    instance
      IACM = ACM
      IS = S
      IR = R

    AbGroupStr-DP = (AbGroupStr-DirectProduct R.+-AbGroup I)
    _dp+_ = AbGroupStr._∙_ AbGroupStr-DP

    _dp*_ : K -> (DP K I) -> (DP K I)
    _dp*_ d = dp-map1 (d *_)

    dp*-distrib-dp+ : {k : K} -> {v1 v2 : DP K I} -> k dp* (v1 dp+ v2) == (k dp* v1) dp+ (k dp* v2)
    dp*-distrib-dp+ = cong wrap-dp (funExt (\_ -> *-distrib-+-left))
    dp*-distrib-+ : {k1 k2 : K} -> {v : DP K I} -> (k1 + k2) dp* v == (k1 dp* v) dp+ (k2 dp* v)
    dp*-distrib-+ = cong wrap-dp (funExt (\_ -> *-distrib-+-right))
    dp*-assoc : {k1 k2 : K} -> {v : DP K I} -> (k1 * k2) dp* v == k1 dp* (k2 dp* v)
    dp*-assoc = cong wrap-dp (funExt (\_ -> *-assoc))
    dp*-left-one : {v : DP K I} -> 1# dp* v == v
    dp*-left-one = cong wrap-dp (funExt (\_ -> *-left-one))

  ModuleStr-DirectProduct : ModuleStr R (AdditiveGroup-DirectProduct AG I)
  ModuleStr-DirectProduct = record
    { _v*_ = _dp*_
    ; v*-distrib-+-left = dp*-distrib-dp+
    ; v*-distrib-+-right = dp*-distrib-+
    ; v*-assoc = dp*-assoc
    ; v*-left-one = dp*-left-one
    }


module _ {ℓK ℓI : Level} {K : Type ℓK} {K# : Rel K ℓK}
         {ACM : AdditiveCommMonoid K} {S : Semiring ACM} {AG : AdditiveGroup ACM}
         {R : Ring S AG} {A : isTightApartness K#} (F : Field R A) (I : Type ℓI) where
  private
    instance
      IACM = ACM
      IS = S
      IA = A
      IVA = isTightApartness-DirectProduct A I
      IMS = ModuleStr-DirectProduct R I

    dp*-apart-args : {k1 k2 : K} {v1 v2 : (DP K I)} ->
                     (k1 v* v1) # (k2 v* v2) ->
                     ∥ (k1 # k2) ⊎ (v1 # v2) ∥
    dp*-apart-args {k1} {k2} {v1} {v2} = ∥-bind handle
      where
      handle : (Σ[ i ∈ I ] ((k1 * (unwrap-dp v1 i)) # (k2 * (unwrap-dp v2 i)))) ->
               ∥ (k1 # k2) ⊎ (v1 # v2) ∥
      handle (i , k1v1#k2v2) =
        ∥-map (⊎-map (\x -> x) (\x -> ∣ i , x ∣)) (Field.*-apart-args F k1v1#k2v2)

  ApartModuleStr-DirectProduct : ApartModuleStr IMS A IVA
  ApartModuleStr-DirectProduct = record
    {  v*-apart-args = dp*-apart-args
    }
