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
open import funext
open import functions
open import hlevel
open import integral-domain
open import integral-domain.instances.real
open import order
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.real
open import real
open import real.arithmetic.absolute-value
open import real.heyting-field
open import relation
open import ring
open import ring.implementations.real
open import semiring
open import set-quotient
open import sigma
open import subset
open import sum
open import truncation
open import vector-space
open import vector-space.finite


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


private

  sym-SameSemiDirection : {d1 d2 : Direction} -> SameSemiDirection d1 d2 -> SameSemiDirection d2 d1
  sym-SameSemiDirection (same-semi-direction-same p) = same-semi-direction-same (sym p)
  sym-SameSemiDirection (same-semi-direction-flipped p) =
    same-semi-direction-flipped (sym v--double-inverse >=> cong v-_ (sym p))


  vector->semi-direction-v* :
    (v : Vector) -> (v#0 : v v# 0v) -> (k : ℝ) -> (kv#0 : (k v* v) v# 0v) ->
    vector->semi-direction (k v* v) kv#0 == vector->semi-direction v v#0
  vector->semi-direction-v* v v#0 k kv#0 = handle (eqInv (<>-equiv-# k 0ℝ) k#0)
    where
    k#0 = fst (v*-apart-zero kv#0)
    handle : (k ℝ# 0ℝ) -> vector->semi-direction (k v* v) kv#0 == vector->semi-direction v v#0
    handle (inj-r 0<k) = eq/ _ _ (same-semi-direction-same (normalize-vector-v*-Pos v v#0 k 0<k kv#0))
    handle (inj-l k<0) = eq/ _ _ (same-semi-direction-flipped p)
      where
      -k = - k
      0<-k = minus-flips-<0 k<0

      v-p1 : (v- (k v* v)) == ((- k) v* v)
      v-p1 = sym v*-minus-extract-left

      -kv#0 : ((- k) v* v) v# 0v
      -kv#0 = v*-#0 (eqFun (<>-equiv-# -k 0ℝ) (inj-r 0<-k)) v#0

      v-kv#0 : (v- (k v* v)) v# 0v
      v-kv#0 = subst (_v# 0v) (sym v-p1) -kv#0

      p1 : normalize-vector ((- k) v* v) -kv#0 == (normalize-vector v v#0)
      p1 = normalize-vector-v*-Pos v v#0 -k 0<-k -kv#0
      p2 : normalize-vector (v- (k v* v)) v-kv#0 == v- (normalize-vector (k v* v) kv#0)
      p2 = normalize-vector-v- (k v* v) kv#0 v-kv#0
      p3 : normalize-vector (v- (k v* v)) v-kv#0 == normalize-vector ((- k) v* v) -kv#0
      p3 = cong2-dep normalize-vector v-p1 (isProp->PathP (\i -> isProp-v# (v-p1 i) _) v-kv#0 -kv#0)

      p : normalize-vector (k v* v) kv#0 == v- (normalize-vector v v#0)
      p = sym v--double-inverse >=> cong v-_ (sym p2 >=> p3 >=> p1)



  same-semi-direction-distance : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
    semi-direction-distance d1 == semi-direction-distance d2
  same-semi-direction-distance d1 d2 (same-semi-direction-same p) =
    cong semi-direction-distance (direction-ext {d1} {d2} p)
  same-semi-direction-distance d1 d2 (same-semi-direction-flipped p) = funExt f
    where
    f : (v : Vector) -> semi-direction-distance d1 v == semi-direction-distance d2 v
    f v = cong absℝ (dec1=-dec2 y-axis) >=> absℝ-- _
      where
      d1=-d2 : d1 == (d- d2)
      d1=-d2 = direction-ext p

      dec1 : Axis -> ℝ
      dec1 = (basis-decomposition (isBasis-rotated-basis (rotation d1)) v)

      dec2 : Axis -> ℝ
      dec2 = (basis-decomposition (isBasis-rotated-basis (rotation d2)) v)

      check : dec1 x-axis == vector-index (rotate (r- (rotation d1)) v) x-axis
      check = refl

      dec1=-dec2 : (a : Axis) -> dec1 a == - (dec2 a)
      dec1=-dec2 a =
        cong (\v -> vector-index v a)
          ((cong (\r -> rotate r v)
             (cong (r-_ ∘ rotation) d1=-d2 >=>
              cong rotation (conjugate-direction-d- d2))) >=>
           rotate-add-half-rotation (r- (rotation d2)) v)

semi-direction-distance' : SemiDirection -> Vector -> ℝ
semi-direction-distance' =
  SemiDirectionElim.rec (isSetΠ \_ -> isSet-ℝ) semi-direction-distance same-semi-direction-distance

semi-direction-distance'-v- : {v1 v2 : Vector} (sd : SemiDirection) -> v1 == (v- v2) ->
  semi-direction-distance' sd v1 == semi-direction-distance' sd v2
semi-direction-distance'-v- {v1} {v2} =
  SemiDirectionElim.elimProp
    (\_ -> (isPropΠ (\_ -> isSet-ℝ _ _)))
    (\d -> semi-direction-distance-v- d {v1} {v2})


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
    ak=1 : absℝ k == 1#
    ak=1 =
      sym *-right-one >=>
      *-right (sym d1p) >=>
      sym (vector-length-* k v1) >=>
      cong vector-length p >=>
      d2p

    k-cases : (k == 1#) ⊎ (k == (- 1#))
    k-cases = absℝ-cases k 1# (IntegralDomain.1#0 IntegralDomain-ℝ)  ak=1

    handle : (k == 1#) ⊎ (k == (- 1#)) -> SameSemiDirection d1 d2
    handle (inj-l k=1) =
      same-semi-direction-same (sym v*-left-one >=> v*-left (sym k=1) >=> p)
    handle (inj-r k=-1) = same-semi-direction-flipped
      (sym v--double-inverse >=>
       cong v-_ (sym v*-left-one >=>
                 sym v*-minus-inverse >=>
                 v*-left (sym k=-1) >=>
                 p))


  same-semi-direction-span-comp : (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
                                   (direction-span-comp d1) == (direction-span-comp d2)
  same-semi-direction-span-comp d1 d2 same-semi =
    same-Subtype (\{v} -> handle same-semi {v})
                 (\{v} -> handle (sym-SameSemiDirection same-semi) {v})
    where
    handle : {d1 d2 : Direction} -> SameSemiDirection d1 d2 -> {v : Vector} ->
             (direction-span'-comp d1 v) -> (direction-span'-comp d2 v)
    handle {d1} {d2} same {v} dis#0 =
      subst (\ sd -> semi-direction-distance' sd v # 0#) (eq/ d1 d2 same) dis#0


semi-direction-span : SemiDirection -> Subtype Vector ℓ-one
semi-direction-span = SemiDirectionElim.rec isSet-Subtype direction-span same-semi-direction-span

semi-direction-span-comp : SemiDirection -> Subtype Vector ℓ-one
semi-direction-span-comp sd v = semi-direction-distance' sd v # 0# , isProp-#

isLinearSubtype-semi-direction-span : (s : SemiDirection) -> isLinearSubtype (semi-direction-span s)
isLinearSubtype-semi-direction-span =
  SemiDirectionElim.elimProp (\_ -> isProp-isLinearSubtype) isLinearSubtype-direction-span


-- Apartness
private
  sd#-direction : SemiDirection -> Direction -> hProp ℓ-one
  sd#-direction sd (dv , _) = semi-direction-span-comp sd dv

  sd#-direction-same-direction : (sd : SemiDirection) ->
    (d1 d2 : Direction) -> SameSemiDirection d1 d2 ->
    sd#-direction sd d1 == sd#-direction sd d2
  sd#-direction-same-direction sd d1 d2 (same-semi-direction-same p) = ΣProp-path isProp-isProp path
    where
    path : ⟨ semi-direction-span-comp sd ⟨ d1 ⟩ ⟩ ==
           ⟨ semi-direction-span-comp sd ⟨ d2 ⟩ ⟩
    path = cong (\dv -> ⟨ semi-direction-span-comp sd dv ⟩) p

  sd#-direction-same-direction sd d1 d2 (same-semi-direction-flipped p) = ΣProp-path isProp-isProp path
    where
    path : ⟨ semi-direction-span-comp sd ⟨ d1 ⟩ ⟩ ==
           ⟨ semi-direction-span-comp sd ⟨ d2 ⟩ ⟩
    path = cong (_# 0#) (semi-direction-distance'-v- sd p)

  sd#-full : SemiDirection -> SemiDirection -> hProp ℓ-one
  sd#-full sd1 =
    SemiDirectionElim.rec isSet-hProp (sd#-direction sd1) (sd#-direction-same-direction sd1)

_sd#_ : Rel SemiDirection ℓ-one
_sd#_ sd1 sd2 = fst (sd#-full sd1 sd2)

isProp-sd# : (sd1 sd2 : SemiDirection) -> isProp (sd1 sd# sd2)
isProp-sd# sd1 sd2 = snd (sd#-full sd1 sd2)

sym-sd# : Symmetric _sd#_
sym-sd# {sd1} {sd2} =
  SemiDirectionElim.elimProp2
    (\sd1 sd2 -> isPropΠ (\(_ : sd1 sd# sd2) -> isProp-sd# sd2 sd1))
    f sd1 sd2
  where
  f : (d1 d2 : Direction) -> [ d1 ] sd# [ d2 ] -> [ d2 ] sd# [ d1 ]
  f d1 d2 = subst (_# 0#) (sym-semi-direction-distance d1 d2)


tight-sd# : Tight _sd#_
tight-sd# {sd1} {sd2} =
  SemiDirectionElim.elimProp2
    (\sd1 sd2 -> isPropΠ (\(_ : ¬ (sd1 sd# sd2)) -> isSet-SemiDirection sd1 sd2))
    f sd1 sd2
  where
  f : (d1 d2 : Direction) -> ¬ ([ d1 ] sd# [ d2 ]) -> [ d1 ] == [ d2 ]
  f d1 d2 ¬d1#d2 = eq/ d1 d2 (in-span->same-semi-direction d1 d2 in-span)
    where
    in-span : ⟨ direction-span d1 ⟨ d2 ⟩ ⟩
    in-span = direction-span'-comp-tight d1 ⟨ d2 ⟩ ¬d1#d2


irrefl-sd# : Irreflexive _sd#_
irrefl-sd# {sd} = SemiDirectionElim.elimProp (\sd -> isProp¬ (sd sd# sd)) f sd
  where
  f : (d : Direction) -> ¬ ([ d ] sd# [ d ])
  f d@(dv , _) = irrefl-path-# dis=0
    where
    dis=0 : semi-direction-distance d dv == 0#
    dis=0 = direction-span->semi-direction-distance0 d dv (1# , v*-left-one)


--comparison-sd# : Comparison _sd#_
--comparison-sd# =
--  SemiDirectionElim.elimProp3 (\sd1 sd2 sd3 -> isPropΠ (\_ -> squash)) f
--  where
--  f : (d1 d2 d3 : Direction) -> ([ d1 ] sd# [ d3 ]) ->  ∥ ([ d1 ] sd# [ d2 ]) ⊎ ([ d2 ] sd# [ d3 ]) ∥
--  f d1 d2 d3 d1#d3 = ?
--    where
--    check : semi-direction-distance d1 ⟨ d3 ⟩ # 0#
--    check = d1#d3
--
--    check2 : semi-direction-distance d1 ⟨ d3 ⟩ # semi-direction-distance d1 ⟨ d2 ⟩
--    check2 = ?
