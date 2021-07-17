{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space where

open import base
open import commutative-monoid
open import finset
open import finite-commutative-monoid
open import group
open import heyting-field
open import hlevel
open import monoid
open import semiring
open import ring

private
  variable
    ℓ : Level

module _ {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} (R : Ring S) (V : Type ℓV) where
  private
    instance
      IS = S
      IR = R

  record ModuleStr : Type (ℓ-max ℓK ℓV) where
    field
      GroupStr-V : GroupStr V

    _v+_ = GroupStr._∙_ GroupStr-V
    0v = GroupStr.ε GroupStr-V

    field
      _v*_ : K -> V -> V
      v*-distrib-v+ : {k : K} -> {v1 v2 : V} -> k v* (v1 v+ v2) == (k v* v1) v+ (k v* v2)
      v*-distrib-+ : {k1 k2 : K} -> {v : V} -> (k1 + k2) v* v == (k1 v* v) v+ (k2 v* v)
      v*-assoc : {k1 k2 : K} -> {v : V} -> (k1 * k2) v* v == k1 v* (k2 v* v)
      v*-left-one : {v : V} -> 1# v* v == v


module _  {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} {V : Type ℓV}
          {{M : ModuleStr R V}} where
  open ModuleStr M public using
    ( _v+_
    ; 0v
    ; _v*_
    ; v*-distrib-v+
    ; v*-distrib-+
    ; v*-assoc
    ; v*-left-one
    )


module _ {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} (F : Field R) (V : Type ℓV) where
  record VectorSpaceStr : Type (ℓ-max ℓK ℓV) where
    constructor vector-space-str
    field
      module-str : ModuleStr R V

instance
  VectorSpaceStr-ModuleStr :
    {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} {F : Field R} {V : Type ℓV}
    {{ M : ModuleStr R V }} -> VectorSpaceStr F V
  VectorSpaceStr-ModuleStr {{M}} = vector-space-str M


module _ {ℓK ℓV : Level} {K : Type ℓK} {S : Semiring K} {R : Ring S} {F : Field R} {V : Type ℓV}
         (VS : VectorSpaceStr F V) where
  private
    module VS = VectorSpaceStr VS
    module M = ModuleStr VS.module-str

    instance
      IM = VS.module-str

  private
    variable
      I : Type ℓ

  private
    CommMonoid-V+ : CommMonoid V
    CommMonoid-V+ = GroupStr.comm-monoid M.GroupStr-V

   -- vector-sum : isFinSet I -> isSet V -> (I -> V) -> V
   -- vector-sum fs setV vs = finiteMerge CommMonoid-V+ setV (_ , fs) vs

   --module _ {ℓI : Level} {I : Type ℓI} (fam : I -> V) where
   --  LinearlyDependent : Type _
   --  LinearlyDependent = isFinSetΣ I × Σ[ coef ∈ (I -> K) ]
