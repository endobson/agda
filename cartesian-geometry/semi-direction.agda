{-# OPTIONS --cubical --safe --exact-split #-}

module cartesian-geometry.semi-direction where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import cartesian-geometry.vector
open import cartesian-geometry.rotation
open import equality
open import equivalence
open import functions
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import order
open import order.minmax.instances.real
open import ordered-ring
open import ordered-ring.absolute-value
open import ordered-semiring.instances.real
open import real
open import real.arithmetic.absolute-value
open import real.heyting-field
open import real.order
open import relation
open import ring.implementations.real
open import semiring
open import set-quotient
open import sigma
open import subset
open import vector-space


data SameSemiDirection : Rel Direction ℓ-one where
  same-semi-direction-same : {d1 d2 : Direction} -> ⟨ d1 ⟩ == ⟨ d2 ⟩ -> SameSemiDirection d1 d2
  same-semi-direction-flipped : {d1 d2 : Direction} -> ⟨ d1 ⟩ == (v- ⟨ d2 ⟩) -> SameSemiDirection d1 d2

-- The type itself
SemiDirection : Type ℓ-one
SemiDirection = Direction / SameSemiDirection

module SemiDirectionElim = SetQuotientElim Direction SameSemiDirection

isSet-SemiDirection : isSet SemiDirection
isSet-SemiDirection = squash/

-- Constants
xaxis-semi-dir : SemiDirection
xaxis-semi-dir = [ xaxis-dir ]

yaxis-semi-dir : SemiDirection
yaxis-semi-dir = [ yaxis-dir ]

-- Constructors
vector->semi-direction : (v : Vector) -> v v# 0v -> SemiDirection
vector->semi-direction v v#0 = [ vector->direction v v#0 ]


sym-SameSemiDirection : {d1 d2 : Direction} -> SameSemiDirection d1 d2 -> SameSemiDirection d2 d1
sym-SameSemiDirection (same-semi-direction-same p) = same-semi-direction-same (sym p)
sym-SameSemiDirection (same-semi-direction-flipped p) =
  same-semi-direction-flipped (sym v--double-inverse >=> cong v-_ (sym p))


private
  vector->semi-direction-v*' :
    (v : Vector) -> (v#0 : v v# 0v) -> (k : ℝ) -> (kv#0 : (k v* v) v# 0v) ->
    vector->semi-direction (k v* v) kv#0 == vector->semi-direction v v#0
  vector->semi-direction-v*' v v#0 k kv#0 = a.ans
    where
    module a where
      AP = _#_
      abstract
        k#0 : AP k 0#
        k#0 = fst (v*-apart-zero kv#0)
        handle : (k # 0#) -> vector->semi-direction (k v* v) kv#0 == vector->semi-direction v v#0
        handle (inj-r 0<k) = eq/ _ _ (same-semi-direction-same (normalize-vector-v*-Pos v v#0 k 0<k kv#0))
        handle (inj-l k<0) = eq/ _ _ (same-semi-direction-flipped p)
          where
          module _ where
            -k = - k
            0<-k = minus-flips-<0 k<0

          v-p1 : (v- (k v* v)) == ((- k) v* v)
          v-p1 = sym v*-minus-extract-left

          -kv#0 : ((- k) v* v) v# 0v
          -kv#0 = v*-#0 (inj-r 0<-k) v#0

          v-kv#0 : (v- (k v* v)) v# 0v
          v-kv#0 = subst (_v# 0v) (sym v-p1) -kv#0

          p1 : normalize-vector ((- k) v* v) -kv#0 == (normalize-vector v v#0)
          p1 = normalize-vector-v*-Pos v v#0 -k 0<-k -kv#0
          p2 : normalize-vector (v- (k v* v)) v-kv#0 == v- (normalize-vector (k v* v) kv#0)
          p2 = normalize-vector-v- (k v* v) kv#0 v-kv#0
          p3 : normalize-vector (v- (k v* v)) v-kv#0 == normalize-vector ((- k) v* v) -kv#0
          p3 = cong2-dep normalize-vector v-p1 (isProp->PathPᵉ (\i -> isProp-v# (v-p1 i) _) v-kv#0 -kv#0)

          p : normalize-vector (k v* v) kv#0 == v- (normalize-vector v v#0)
          p = sym v--double-inverse >=> cong v-_ (sym p2 >=> p3 >=> p1)

        ans : vector->semi-direction (k v* v) kv#0 == vector->semi-direction v v#0
        ans = handle k#0

vector->semi-direction-v* :
  (v1 : Vector) (v1#0 : v1 v# 0v) (v2 : Vector) (v2#0 : v2 # 0v) (k : ℝ) ->
  (k v* v1 == v2) ->
  vector->semi-direction v1 v1#0 == vector->semi-direction v2 v2#0
vector->semi-direction-v* v1 v1#0 v2 v2#0 k path =
  sym (vector->semi-direction-v*' v1 v1#0 k kv1#0) >=> path2
  where
  kv1#0 : (k v* v1) # 0v
  kv1#0 = (subst (_v# 0v) (sym path) v2#0)
  path3 : PathP (\i -> path i # 0v) kv1#0 v2#0
  path3 = isProp->PathP (\i -> isProp-#)
  path2 : vector->semi-direction (k v* v1) kv1#0 == vector->semi-direction v2 v2#0
  path2 i = vector->semi-direction (path i) (path3 i)




private
  same-semi-direction-span : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
                             (direction-span d1) == (direction-span d2)
  same-semi-direction-span d1 d2 same-semi =
    same-Subtype (handle same-semi) (handle (sym-SameSemiDirection same-semi))
    where
    handle : {d1 d2 : Direction} {v : Vector} -> SameSemiDirection d1 d2 ->
             (direction-span' d1 v) -> (direction-span' d2 v)
    handle (same-semi-direction-same p) (k , kd=v) = (k , cong (k v*_) (sym p) >=> kd=v)
    handle (same-semi-direction-flipped p) (k , kd=v) =
      ((- k) , v*-minus-extract-left >=> sym v*-minus-extract-right >=>
               cong (k v*_) (sym p) >=> kd=v)


  in-span->same-semi-direction :
    (d1 d2 : Direction) -> ⟨ direction-span d1 ⟨ d2 ⟩ ⟩ ->
    SameSemiDirection d1 d2
  in-span->same-semi-direction d1@(v1 , d1p) d2@(v2 , d2p) (k , p) = handle k-cases
    where
    ak=1 : abs k == 1#
    ak=1 =
      sym *-right-one >=>
      *-right (sym d1p) >=>
      sym (vector-length-* k v1) >=>
      cong vector-length p >=>
      d2p

    k-cases : (k == 1#) ⊎ (k == (- 1#))
    k-cases = abs-cases k 1# (IntegralDomain.1#0 IntegralDomain-ℝ)  ak=1

    handle : (k == 1#) ⊎ (k == (- 1#)) -> SameSemiDirection d1 d2
    handle (inj-l k=1) =
      same-semi-direction-same (sym v*-left-one >=> v*-left (sym k=1) >=> p)
    handle (inj-r k=-1) = same-semi-direction-flipped
      (sym v--double-inverse >=>
       cong v-_ (sym v*-left-one >=>
                 sym v*-minus-inverse >=>
                 v*-left (sym k=-1) >=>
                 p))



semi-direction-span : SemiDirection -> Subtype Vector ℓ-one
semi-direction-span = SemiDirectionElim.rec isSet-Subtype direction-span same-semi-direction-span



abstract
  isLinearSubtype-semi-direction-span : (s : SemiDirection) -> isLinearSubtype (semi-direction-span s)
  isLinearSubtype-semi-direction-span =
    SemiDirectionElim.elimProp (\_ -> isProp-isLinearSubtype) isLinearSubtype-direction-span
