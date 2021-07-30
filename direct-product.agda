{-# OPTIONS --cubical --safe --exact-split #-}

module direct-product where

open import apartness
open import base
open import commutative-monoid
open import equality hiding (J)
open import finset
open import finset.search
open import funext
open import functions
open import group
open import heyting-field
open import hlevel
open import monoid
open import relation
open import ring
open import semiring
open import sigma
open import subset
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

module _ {ℓD ℓI : Level} {D : Type ℓD} (TD : TightApartnessStr D) (I : Type ℓI) where
  private
    instance
      ITD = TD

    _dp#'_ : Rel (DP D I) _
    _dp#'_ dp1 dp2 = Σ[ i ∈ I ] ((unwrap-dp dp1 i) # (unwrap-dp dp2 i))

    _dp#_ : Rel (DP D I) _
    _dp#_ dp1 dp2 = ∥ dp1 dp#' dp2 ∥

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


  TightApartnessStr-DirectProduct : TightApartnessStr (DP D I)
  TightApartnessStr-DirectProduct = record
    { _#_ = _dp#_
    ; TightApartness-# = (tight-dp# , (irrefl-dp# , sym-dp# , comparison-dp#))
    ; isProp-# = \_ _ -> squash
    }


module _ {ℓK ℓI : Level} {K : Type ℓK} {S : Semiring K}
         (R : Ring S) (TK : TightApartnessStr K) (I : Type ℓI) where
  private
    module R = Ring R
    instance
      IS = S
      IR = R

    GroupStr-DP = (GroupStr-DirectProduct R.+-Group I)
    _dp+_ = GroupStr._∙_ GroupStr-DP

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

  ModuleStr-DirectProduct : ModuleStr R (DP K I)
  ModuleStr-DirectProduct = record
    { GroupStr-V = GroupStr-DP
    ; TightApartnessStr-V = (TightApartnessStr-DirectProduct TK I)
    ; _v*_ = _dp*_
    ; v*-distrib-v+ = dp*-distrib-dp+
    ; v*-distrib-+ = dp*-distrib-+
    ; v*-assoc = dp*-assoc
    ; v*-left-one = dp*-left-one
    }

module _ {ℓK ℓI : Level} {K : Type ℓK} {S : Semiring K}
         {R : Ring S} (F : Field R) (I : Type ℓI) where
  private
    instance
      IS = S
      IR = R
      IFA = (Field.TightApartnessStr-f# F)
      IVA = TightApartnessStr-DirectProduct IFA I

    MS = ModuleStr-DirectProduct R IFA I
    module MS = ModuleStr MS
    module R = Ring R
    module F = Field F

    dp*-apart-zero : {k : K} {v : (DP K I)} -> (k MS.v* v) # MS.0v -> (k # 0#) × (v MS.v# MS.0v)
    dp*-apart-zero {k} {v} = (unsquash (isProp× isProp-# squash)) ∘ (∥-map handle)
      where
      handle : Σ[ i ∈ I ] (k * (unwrap-dp v i)) # 0# -> (k # 0#) × (v # MS.0v)
      handle (i , kv#0) = fst prod , ∣ i , snd prod ∣
        where
        prod = F.*-apart-zero kv#0

    dp*-apart-args : {k1 k2 : K} {v1 v2 : (DP K I)} ->
                     (k1 MS.v* v1) MS.v# (k2 MS.v* v2) ->
                     ∥ (k1 # k2) ⊎ (v1 MS.v# v2) ∥
    dp*-apart-args {k1} {k2} {v1} {v2} = ∥-bind handle
      where
      handle : (Σ[ i ∈ I ] ((k1 * (unwrap-dp v1 i)) # (k2 * (unwrap-dp v2 i)))) ->
               ∥ (k1 # k2) ⊎ (v1 MS.v# v2) ∥
      handle (i , k1v1#k2v2) = ∥-map (⊎-map (\x -> x) (\x -> ∣ i , x ∣)) prod
        where
        prod = F.*-apart-args k1v1#k2v2

  VectorSpaceStr-DirectProduct : VectorSpaceStr F (DP K I)
  VectorSpaceStr-DirectProduct = record
    { module-str = MS
    ; v*-apart-zero = dp*-apart-zero
    ; v*-apart-args = dp*-apart-args
    }

module _ {ℓK ℓI : Level} {K : Type ℓK} {S : Semiring K}
         {R : Ring S} (F : Field R) (I : FinSet ℓI) where
  private
    instance
      IS = S
      IR = R

    I' = ⟨ I ⟩
    isFinSet-I = snd I
    isSet-I = isFinSet->isSet isFinSet-I
    discrete-I = isFinSet->Discrete isFinSet-I

    VS = (VectorSpaceStr-DirectProduct F I')

    J : FinSubset I' ℓI
    J = I , (\x -> x) , (\p -> p)

    indicator' : {i1 i2 : I'} -> Dec (i1 == i2) -> K
    indicator' (yes _) = 1#
    indicator' (no _) = 0#

    indicator : I' -> I' -> K
    indicator i1 i2 = indicator' (discrete-I i1 i2)

    standard-basis' : I' -> (DP K I')
    standard-basis' i1 = wrap-dp (indicator i1)

    module _ (S : FinSubset I' ℓI) (f : ⟨ ⟨ S ⟩ ⟩ -> K) where
      private
        S' = ⟨ ⟨ S ⟩ ⟩
        inc : S' -> I'
        inc = fst (snd S)
        inj-inc : Injective inc
        inj-inc = snd (snd S)

      ΣS' : Pred I' ℓI
      ΣS' i = (Σ[ s ∈ S' ] (inc s == i))

      isProp-ΣS' : isPropValuedPred ΣS'
      isProp-ΣS' _ (s1 , p1) (s2 , p2) =
        ΣProp-path (isSet-I _ _) (inj-inc (p1 >=> (sym p2)))


      find-s : Decidable ΣS'
      find-s i = handle find-or
        where
        find-or : Inhabited (\s -> inc s == i) ⊎ Universal (\s -> inc s != i)
        find-or = finite-search' ⟨ S ⟩ (\s -> handle (discrete-I (inc s) i))
          where
          handle : {s : S'} -> Dec (inc s == i) -> (inc s == i) ⊎ (inc s != i)
          handle (yes p) = inj-l p
          handle (no p) = inj-r p

        handle : (Inhabited (\s -> inc s == i) ⊎ Universal (\s -> inc s != i)) -> Dec (ΣS' i)
        handle (inj-r f) = no (\(s , p) -> f s p)
        handle (inj-l p) = yes (unsquash (isProp-ΣS' i) p)


      extend' : {i : I'} -> Dec (ΣS' i) -> K
      extend' (yes (s , _)) = f s
      extend' (no _) = 0#

      extend : I' -> K
      extend i = extend' (find-s i)

      extend-support : (s : S') -> extend (inc s) == f s
      extend-support s = handle (find-s (inc s)) refl
        where
        handle : (d : Dec (Σ[ s2 ∈ S' ] (inc s2 == inc s))) -> d == find-s (inc s) ->
                 extend (inc s) == f s
        handle (yes (s2 , p)) path =
          cong extend' (sym path) >=> cong f (inj-inc p)
        handle (no ¬s2) path = bot-elim (¬s2 (s , refl))

--      standard-basis'-sum'-i-elem : (i : I') -> ΣS' i ->
--        unwrap-dp (scaled-vector-sum VS standard-basis' S f) i == extend i
--      standard-basis'-sum'-i-elem i (s , path) = ?
--
--      standard-basis'-sum'-i-noelem : (i : I') -> ¬ (ΣS' i) ->
--        unwrap-dp (scaled-vector-sum VS standard-basis' S f) i == extend i
--      standard-basis'-sum'-i-noelem i ¬s = ?


--      standard-basis'-sum'-i :
--        ∀ (i : I') ->
--        unwrap-dp (scaled-vector-sum VS standard-basis' S f) i == extend i
--      standard-basis'-sum'-i i = ?
--
--
--      standard-basis'-sum' :
--        scaled-vector-sum VS standard-basis' S f == wrap-dp extend
--      standard-basis'-sum' k = wrap-dp (\i -> standard-basis'-sum'-i i k)
--
--    extend-J : (f : I' -> K) -> extend J f == f
--    extend-J f k i = extend-support J f i k
--
--
--    standard-basis'-sum : (f : I' -> K) -> scaled-vector-sum VS standard-basis' J f == wrap-dp f
--    standard-basis'-sum f = standard-basis'-sum' J f >=> cong wrap-dp (extend-J f)
--
--
--    isSpanning-standard-basis' : isSpanning VS standard-basis' ℓI
--    isSpanning-standard-basis' v = ∣ J , unwrap-dp v , standard-basis'-sum _ ∣
--
--    LinearlyIndependent-standard-basis' : LinearlyIndependent VS standard-basis' ℓI
--    LinearlyIndependent-standard-basis' S a path s =
--      sym (extend-support S a s) >=>
--      cong (\x -> unwrap-dp x (fst (snd S) s)) (sym (standard-basis'-sum' S a) >=> path)
--
--    isBasis-standard-basis' : isBasis VS standard-basis' ℓI
--    isBasis-standard-basis' = isSpanning-standard-basis' , LinearlyIndependent-standard-basis'
--
--  standard-basis : Basis VS ℓI
--  standard-basis = I' , standard-basis' , isBasis-standard-basis'
