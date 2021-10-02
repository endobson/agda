{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space where

open import additive-group
open import apartness
open import base
open import cubical using (_≃_)
open import commutative-monoid
open import equality hiding (J)
open import equivalence
open import fin
open import finset
open import finset.partition
open import finset.detachable
open import finsum
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finite-commutative-monoid.partition
open import functions
open import group
open import heyting-field
open import hlevel
open import monoid
open import ring
open import relation
open import semiring
open import subset
open import truncation

private
  variable
    ℓ : Level

module _ {ℓK ℓV : Level} {K : Type ℓK} {ACM : AdditiveCommMonoid K}
         {S : Semiring ACM} {AG : AdditiveGroup ACM} (R : Ring S AG) (V : Type ℓV) where
  private
    instance
      IACM = ACM
      IAG = AG
      IS = S
      IR = R

  record ModuleStr : Type (ℓ-max ℓK (ℓ-suc ℓV)) where
    field
      GroupStr-V : GroupStr V
      TightApartnessStr-V : TightApartnessStr V

    _v#_ = TightApartnessStr._#_ TightApartnessStr-V

    isProp-v# = TightApartnessStr.isProp-# TightApartnessStr-V

    _v+_ = GroupStr._∙_ GroupStr-V
    0v = GroupStr.ε GroupStr-V
    v-_ = GroupStr.inverse GroupStr-V

    isSet-V = GroupStr.isSet-Domain GroupStr-V
    CommMonoid-V+ = GroupStr.comm-monoid GroupStr-V


    field
      _v*_ : K -> V -> V
      v*-distrib-v+ : {k : K} -> {v1 v2 : V} -> k v* (v1 v+ v2) == (k v* v1) v+ (k v* v2)
      v*-distrib-+ : {k1 k2 : K} -> {v : V} -> (k1 + k2) v* v == (k1 v* v) v+ (k2 v* v)
      v*-assoc : {k1 k2 : K} -> {v : V} -> (k1 * k2) v* v == k1 v* (k2 v* v)
      v*-left-one : {v : V} -> 1# v* v == v


module _  {ℓK ℓV : Level} {K : Type ℓK}
          {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
          {S : Semiring ACM} {R : Ring S AG} {V : Type ℓV}
          {{M : ModuleStr R V}} where
  open ModuleStr M public using
    ( _v+_
    ; 0v
    ; v-_
    ; _v*_
    ; v*-distrib-v+
    ; v*-distrib-+
    ; v*-assoc
    ; v*-left-one
    ; _v#_
    ; isProp-v#
    )

  private
    instance
      IACM = ACM
      IAG = AG
      IS = S
      IR = R




  open GroupStr (ModuleStr.GroupStr-V M)

  abstract
    v+-right-zero : {v : V} -> v v+ 0v == v
    v+-right-zero = ∙-right-ε

    v+-left-zero : {v : V} -> 0v v+ v == v
    v+-left-zero = ∙-left-ε

    v+-inverse : {v : V} -> v v+ (v- v) == 0v
    v+-inverse = ∙-right-inverse

    v+-left : {v1 v2 v3 : V} -> v1 == v2 -> v1 v+ v3 == v2 v+ v3
    v+-left {v3 = v3} p = cong (_v+ v3) p

    v+-right : {v1 v2 v3 : V} -> v2 == v3 -> v1 v+ v2 == v1 v+ v3
    v+-right {v1} p = cong (v1 v+_) p

    v+-commute : {v1 v2 : V} -> v1 v+ v2 == v2 v+ v1
    v+-commute = ∙-commute

    v+-assoc : {v1 v2 v3 : V} -> (v1 v+ v2) v+ v3 == v1 v+ (v2 v+ v3)
    v+-assoc = ∙-assoc

    v--distrib-v+ : {v1 v2 : V} -> (v- (v1 v+ v2)) == (v- v1) v+ (v- v2)
    v--distrib-v+ = CommMonoidʰ.preserves-∙ inverse-CMʰ _ _

    v*-left-zero : {v : V} -> 0# v* v == 0v
    v*-left-zero {v} =
      sym ∙-right-ε >=>
      ∙-right (sym ∙-right-inverse) >=>
      sym ∙-assoc >=>
      ∙-left (∙-right (sym v*-left-one) >=>
              sym v*-distrib-+ >=>
              cong (_v* v) +-left-zero >=>
              v*-left-one) >=>
      ∙-right-inverse


    v*-right-zero : {k : K} -> k v* 0v == 0v
    v*-right-zero {k} =
      sym ∙-right-ε >=>
      ∙-right (sym v*-left-zero >=>
               cong (_v* 0v) (sym +-inverse) >=>
               v*-distrib-+) >=>
      sym ∙-assoc >=>
      ∙-left (sym v*-distrib-v+ >=>
              cong (k v*_) (∙-right-ε)) >=>
      sym v*-distrib-+ >=>
      cong (_v* 0v) +-inverse >=>
      v*-left-zero

    v*-left : {k1 k2 : K} {v : V} -> k1 == k2 -> k1 v* v == k2 v* v
    v*-left {k1} {k2} {v} p = cong (_v* v) p

    v*-right : {k : K} {v1 v2 : V} -> v1 == v2 -> k v* v1 == k v* v2
    v*-right {k} p = cong (k v*_) p


    v*-minus-inverse : {k : K} {v : V} -> (- k) v* v == k v* (v- v)
    v*-minus-inverse {k} {v} =
      sym ∙-right-ε >=>
      ∙-right (sym v*-left-zero >=>
               cong (_v* (v- v)) (sym +-inverse >=> +-commute) >=>
               v*-distrib-+ { - k} {k}) >=>
      sym ∙-assoc >=>
      ∙-left (sym v*-distrib-v+ >=>
              cong ((- k) v*_) ∙-right-inverse >=>
              v*-right-zero) >=>
      v+-left-zero

    v*-left-minus-one : {v : V} -> (- 1#) v* v == (v- v)
    v*-left-minus-one = v*-minus-inverse >=> v*-left-one

    v*-minus-extract-left : {k : K} {v : V} -> (- k) v* v == v- (k v* v)
    v*-minus-extract-left =
      v*-left (sym *-left-one >=> minus-extract-right >=> sym minus-extract-left) >=>
      v*-assoc >=>
      v*-left-minus-one

    v*-minus-extract-right : {k : K} {v : V} -> k v* (v- v) == v- (k v* v)
    v*-minus-extract-right =
      v*-right (sym v*-left-minus-one) >=>
      sym v*-assoc >=>
      v*-left *-commute >=>
      v*-assoc >=>
      v*-left-minus-one

    v--double-inverse : {v : V} -> (v- (v- v)) == v
    v--double-inverse =
      sym v*-left-minus-one >=>
      v*-minus-extract-right >=>
      sym v*-minus-extract-left >=>
      v*-left minus-double-inverse >=>
      v*-left-one


    v*-minus-extract-both : {k : K} {v : V} -> (- k) v* (v- v) == (k v* v)
    v*-minus-extract-both =
      v*-minus-extract-left >=>
      cong v-_ v*-minus-extract-right >=>
      v--double-inverse

  vdiff : V -> V -> V
  vdiff v1 v2 = v2 v+ (v- v1)

  private
    G-V+ = (ModuleStr.GroupStr-V M)
    CM-V+ = GroupStr.comm-monoid G-V+

  v-ʰ : CommMonoidʰᵉ CM-V+ CM-V+ v-_
  v-ʰ = GroupStr.inverse-CMʰ G-V+



module _ {ℓK ℓV : Level} {K : Type ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : TightApartnessStr K}
         (F : Field R A) (V : Type ℓV)  where
  private
    instance
      IACM = ACM
      IS = S
      IF = F
      IA = A

  record VectorSpaceStr : Type (ℓ-max ℓK (ℓ-suc ℓV)) where
    constructor vector-space-str
    field
      module-str : ModuleStr R V

    private
      module MS = ModuleStr module-str

    field
      v*-apart-zero : {k : K} {v : V} -> (k MS.v* v) MS.v# MS.0v -> (k # 0#) × (v MS.v# MS.0v)
      v*-apart-args : {k1 k2 : K} {v1 v2 : V} ->
                      (k1 MS.v* v1) MS.v# (k2 MS.v* v2) ->
                      ∥ (k1 # k2) ⊎ (v1 MS.v# v2) ∥

module _ {ℓK ℓV : Level} {K : Type ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : TightApartnessStr K} {F : Field R A} {V : Type ℓV}
         {{VS : VectorSpaceStr F V}} where
  open VectorSpaceStr VS public using
    ( v*-apart-zero
    ; v*-apart-args
    )

  private
    module VS = VectorSpaceStr VS
    module M = ModuleStr VS.module-str
    module R = Ring R
    module F = Field F

    instance
      IM = VS.module-str
      IACM = ACM
      IS = S
      IA = A
      IF = F
      IVA = ModuleStr.TightApartnessStr-V IM

  abstract
    v*-#0 : {k : K} -> {v : V} -> k # 0# -> v v# 0v -> (k v* v) v# 0v
    v*-#0 {k} {v} k#0 v#0 = snd (v*-apart-zero k'kv#0)
      where
      k-unit : R.isUnit k
      k-unit = F.#0->isUnit k#0
      k' = R.isUnit.inv k-unit
      kk'=1 = R.isUnit.path k-unit
      k'kv#0 = subst (_v# 0v) (sym v*-left-one >=> v*-left (sym kk'=1 >=> *-commute) >=> v*-assoc) v#0


module _ {ℓK ℓV : Level} {K : Type ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : TightApartnessStr K} {F : Field R A} {V : Type ℓV}
         {{VS : VectorSpaceStr F V}} where

  private
    instance
      IM = VectorSpaceStr.module-str VS

  private
    CommMonoid-V+ : CommMonoid V
    CommMonoid-V+ = GroupStr.comm-monoid (ModuleStr.GroupStr-V (VectorSpaceStr.module-str VS))

  vector-sum : {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} -> (I -> V) -> V
  vector-sum = finiteMerge CommMonoid-V+

  record isLinearSubtype  {ℓS : Level} (S : (Subtype V ℓS)) : Type (ℓ-max* 3 ℓS ℓV ℓK) where
    field
      closed-under-0v : ⟨ S 0v ⟩
      closed-under-v+ : {v1 v2 : V} -> ⟨ S v1 ⟩ -> ⟨ S v2 ⟩ -> ⟨ S (v1 v+ v2) ⟩
      closed-under-v* : {v : V} (k : K) -> ⟨ S v ⟩ -> ⟨ S (k v* v) ⟩

  isProp-isLinearSubtype : {ℓS : Level} {S : (Subtype V ℓS)} -> isProp (isLinearSubtype S)
  isProp-isLinearSubtype {S = S} ls1 ls2 i = record
    { closed-under-0v =
        snd (S 0v)
          (isLinearSubtype.closed-under-0v ls1)
          (isLinearSubtype.closed-under-0v ls2) i
    ; closed-under-v+ =
      isPropΠ2 (\sv1 sv2 -> snd (S _))
        (isLinearSubtype.closed-under-v+ ls1)
        (isLinearSubtype.closed-under-v+ ls2) i
    ; closed-under-v* =
      isPropΠ2 (\k sv -> snd (S (k v* _)))
        (isLinearSubtype.closed-under-v* ls1)
        (isLinearSubtype.closed-under-v* ls2) i
    }



module _ {ℓK ℓV1 ℓV2 : Level} {K : Type ℓK}
         {ACM : AdditiveCommMonoid K} {AG : AdditiveGroup ACM}
         {S : Semiring ACM} {R : Ring S AG}
         {A : TightApartnessStr K} {F : Field R A} {V1 : Type ℓV1} {V2 : Type ℓV2}
         {{VS1 : VectorSpaceStr F V1}} {{VS2 : VectorSpaceStr F V2}} where
  private
    instance
      IM1 = VectorSpaceStr.module-str VS1
      IM2 = VectorSpaceStr.module-str VS2
      IACM = ACM
      IS = S

  record isLinearTransformation (f : V1 -> V2) : Type (ℓ-max* 3 ℓK ℓV1 ℓV2) where
    constructor is-linear-transformation
    field
      preserves-+ : (v1 v2 : V1) -> f (v1 v+ v2) == f v1 v+ f v2
      preserves-* : (k : K) (v : V1) -> f (k v* v) == k v* f v

  lt-preserves-+ : {f : V1 -> V2} -> isLinearTransformation f -> (v1 v2 : V1) ->
                   f (v1 v+ v2) == f v1 v+ f v2
  lt-preserves-+ = isLinearTransformation.preserves-+

  lt-preserves-* : {f : V1 -> V2} -> isLinearTransformation f -> (k : K) -> (v : V1) ->
                   f (k v* v) == k v* f v
  lt-preserves-* = isLinearTransformation.preserves-*

  lt-preserves-0v : {f : V1 -> V2} -> isLinearTransformation f -> f 0v == 0v
  lt-preserves-0v {f} lt = cong f (sym v*-left-zero) >=> lt-preserves-* lt 0# 0v >=> v*-left-zero

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    abstract
      lt-preserves-vector-sum : {f : V1 -> V2} {vs : I -> V1} -> isLinearTransformation f ->
                                f (vector-sum vs) == vector-sum (f ∘ vs)
      lt-preserves-vector-sum {f} lt = sym (finiteMerge-homo-inject CM-V2+ CM-V1+ h)
        where
        instance
          CM-V1+ : CommMonoid V1
          CM-V1+ = GroupStr.comm-monoid (ModuleStr.GroupStr-V (VectorSpaceStr.module-str VS1))
          CM-V2+ : CommMonoid V2
          CM-V2+ = GroupStr.comm-monoid (ModuleStr.GroupStr-V (VectorSpaceStr.module-str VS2))
        h : CommMonoidʰ f
        h = record
          { preserves-∙ = lt-preserves-+ lt
          ; preserves-ε = lt-preserves-0v lt
          }
