{-# OPTIONS --cubical --safe --exact-split #-}

module vector-space where

open import additive-group
open import apartness
open import base
open import commutative-monoid
open import equality hiding (J)
open import finite-commutative-monoid
open import finite-commutative-monoid.instances
open import finset
open import finsum
open import functions
open import group
open import heyting-field
open import hlevel
open import relation
open import ring
open import semiring
open import subset
open import sum
open import truncation

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV}
         {ACM-K : AdditiveCommMonoid K} {AG-K : AdditiveGroup ACM-K}
         {S-K : Semiring ACM-K}
         {ACM-V : AdditiveCommMonoid V}
         (R-K : Ring S-K AG-K) (AG-V : AdditiveGroup ACM-V) where
  private
    instance
      IACM-K = ACM-K
      IAG-K = AG-K
      IS-K = S-K
      IR-K = R-K
      IACM-V = ACM-V
      IAG-V = AG-V

  record ModuleStr : Type (ℓ-max ℓK (ℓ-suc ℓV)) where
    field
      _v*_ : K -> V -> V
      v*-distrib-+-left : {k : K} -> {v1 v2 : V} -> k v* (v1 + v2) == (k v* v1) + (k v* v2)
      v*-distrib-+-right : {k1 k2 : K} -> {v : V} -> (k1 + k2) v* v == (k1 v* v) + (k2 v* v)
      v*-assoc : {k1 k2 : K} -> {v : V} -> (k1 * k2) v* v == k1 v* (k2 v* v)
      v*-left-one : {v : V} -> 1# v* v == v


module _  {ℓK ℓV : Level} {K : Type ℓK}
          {{ACM-K : AdditiveCommMonoid K}} {{AG-K : AdditiveGroup ACM-K}}
          {{S-K : Semiring ACM-K}} {{R-K : Ring S-K AG-K}}
          {V : Type ℓV} {{ACM-V : AdditiveCommMonoid V}} {{AG-V : AdditiveGroup ACM-V}}
          {{M : ModuleStr R-K AG-V}} where

  open ModuleStr M public using
    ( _v*_
    ; v*-distrib-+-left
    ; v*-distrib-+-right
    ; v*-assoc
    ; v*-left-one
    )

  opaque
    v*-left-zero : {v : V} -> 0# v* v == 0#
    v*-left-zero {v} =
      sym +-right-zero >=>
      +-right (sym +-inverse) >=>
      sym +-assoc >=>
      +-left (+-right (sym v*-left-one) >=>
              sym v*-distrib-+-right >=>
              cong (_v* v) +-left-zero >=>
              v*-left-one) >=>
      +-inverse


    v*-right-zero : {k : K} -> k v* 0# == 0#
    v*-right-zero {k} =
      sym +-right-zero >=>
      +-right (sym v*-left-zero >=>
               cong (_v* 0#) (sym +-inverse) >=>
               v*-distrib-+-right) >=>
      sym +-assoc >=>
      +-left (sym v*-distrib-+-left >=>
              cong (k v*_) (+-right-zero)) >=>
      sym v*-distrib-+-right >=>
      cong (_v* 0#) +-inverse >=>
      v*-left-zero


    v*-left : {k1 k2 : K} {v : V} -> k1 == k2 -> k1 v* v == k2 v* v
    v*-left {k1} {k2} {v} p = cong (_v* v) p

    v*-right : {k : K} {v1 v2 : V} -> v1 == v2 -> k v* v1 == k v* v2
    v*-right {k} p = cong (k v*_) p


    v*-minus-inverse : {k : K} {v : V} -> (- k) v* v == k v* (- v)
    v*-minus-inverse {k} {v} =
      sym +-right-zero >=>
      +-right (sym v*-left-zero >=>
               cong (_v* (- v)) (sym +-inverse >=> +-commute) >=>
               v*-distrib-+-right) >=>
      sym +-assoc >=>
      +-left (sym v*-distrib-+-left >=>
              cong ((- k) v*_) +-inverse >=>
              v*-right-zero) >=>
      +-left-zero


    v*-left-minus-one : {v : V} -> (- 1#) v* v == (- v)
    v*-left-minus-one = v*-minus-inverse >=> v*-left-one

    v*-minus-extract-left : {k : K} {v : V} -> (- k) v* v == - (k v* v)
    v*-minus-extract-left =
      v*-left (sym *-left-one >=> minus-extract-right >=> sym minus-extract-left) >=>
      v*-assoc >=>
      v*-left-minus-one

    v*-minus-extract-right : {k : K} {v : V} -> k v* (- v) == - (k v* v)
    v*-minus-extract-right =
      v*-right (sym v*-left-minus-one) >=>
      sym v*-assoc >=>
      v*-left *-commute >=>
      v*-assoc >=>
      v*-left-minus-one

    v*-minus-extract-both : {k : K} {v : V} -> (- k) v* (- v) == (k v* v)
    v*-minus-extract-both =
      v*-minus-extract-left >=>
      cong -_ v*-minus-extract-right >=>
      minus-double-inverse


module _ {ℓK ℓV : Level}
         {K : Type ℓK} {K# : Rel K ℓK}
         {V : Type ℓV} {V# : Rel V ℓV}
         {ACM-K : AdditiveCommMonoid K}
         {AG-K : AdditiveGroup ACM-K}
         {S-K : Semiring ACM-K}
         {R-K : Ring S-K AG-K}
         {ACM-V : AdditiveCommMonoid V}
         {AG-V : AdditiveGroup ACM-V}
         (MS : ModuleStr R-K AG-V)
         (A-K : isTightApartness K#)
         (A-V : isTightApartness V#)
         where
  private
    instance
      IMS = MS
      IACM-K = ACM-K
      IAG-K = AG-K
      IS-K = S-K
      IR-K = R-K
      IACM-V = ACM-V
      IAG-V = AG-V
      IA-K = A-K
      IA-V = A-V


  record ApartModuleStr : Type (ℓ-max ℓK (ℓ-suc ℓV)) where
    field
      v*-apart-args : {k₁ k₂ : K} {v₁ v₂ : V} ->
        (k₁ v* v₁) # (k₂ v* v₂) -> ∥ (k₁ # k₂) ⊎ (v₁ # v₂) ∥


module _ {ℓK ℓV : Level}
         {K : Type ℓK} {K# : Rel K ℓK}
         {V : Type ℓV} {V# : Rel V ℓV}
         {{ACM-K : AdditiveCommMonoid K}}
         {{AG-K : AdditiveGroup ACM-K}}
         {{S-K : Semiring ACM-K}}
         {{R-K : Ring S-K AG-K}}
         {{ACM-V : AdditiveCommMonoid V}}
         {{AG-V : AdditiveGroup ACM-V}}
         {{MS : ModuleStr R-K AG-V}}
         {{A-K : isTightApartness K#}}
         {{A-V : isTightApartness V#}}
         {{AMS : ApartModuleStr MS A-K A-V}}
  where
  open ApartModuleStr AMS public using
    ( v*-apart-args
    )

  opaque
    v*-apart-zero : {k : K} {v : V} ->
      (k v* v) # 0# -> (k # 0#) × (v # 0#)
    v*-apart-zero {k} {v} kv#0 = k#0 , v#0
      where
      k#0 : k # 0#
      k#0 = unsquash isProp-# (∥-map (\s -> proj-¬r s irrefl-#) (v*-apart-args kv#0v))
        where
        kv#0v : (k v* v) # (0# v* v)
        kv#0v = subst ((k v* v) #_) (sym v*-left-zero) kv#0

      v#0 : v # 0#
      v#0 = unsquash isProp-# (∥-map (\s -> proj-¬l s irrefl-#) (v*-apart-args kv#k0))
        where
        kv#k0 : (k v* v) # (k v* 0#)
        kv#k0 = subst ((k v* v) #_) (sym v*-right-zero) kv#0

module _ {ℓK ℓV : Level}
         {K : Type ℓK} {K# : Rel K ℓK}
         {V : Type ℓV} {V# : Rel V ℓV}
         {{ACM-K : AdditiveCommMonoid K}} {{AG-K : AdditiveGroup ACM-K}}
         {{S-K : Semiring ACM-K}} {{R-K : Ring S-K AG-K}}
         {{ACM-V : AdditiveCommMonoid V}} {{AG-V : AdditiveGroup ACM-V}}
         {{MS : ModuleStr R-K AG-V}}
         {{A-K : isTightApartness K#}}
         {{A-V : isTightApartness V#}}
         {{AMS : ApartModuleStr MS A-K A-V}}
         {{F : Field R-K A-K}}
         where
  private
    module R = Ring R-K
    module F = Field F

  opaque
    v*-#0 : {k : K} -> {v : V} -> k # 0# -> v # 0# -> (k v* v) # 0#
    v*-#0 {k} {v} k#0 v#0 = snd (v*-apart-zero k'kv#0)
      where
      module _ where
        k-unit : R.isUnit k
        k-unit = F.#0->isUnit k#0
        kk'=1 = R.isUnit.path k-unit
        k'kv#0 = subst (_# 0#) (sym v*-left-one >=> v*-left (sym kk'=1 >=> *-commute) >=> v*-assoc) v#0

module _ {ℓK ℓV : Level} {K : Type ℓK} {V : Type ℓV}
         {{ACM-K : AdditiveCommMonoid K}}
         {{AG-K : AdditiveGroup ACM-K}}
         {{S-K : Semiring ACM-K}}
         {{R-K : Ring S-K AG-K}}
         {{ACM-V : AdditiveCommMonoid V}}
         {{AG-V : AdditiveGroup ACM-V}}
         {{MS : ModuleStr R-K AG-V}}
         where

  record isLinearSubtype  {ℓS : Level} (S : (Subtype V ℓS)) : Type (ℓ-max* 3 ℓS ℓV ℓK) where
    field
      closed-under-0v : ⟨ S 0# ⟩
      closed-under-v+ : {v₁ v₂ : V} -> ⟨ S v₁ ⟩ -> ⟨ S v₂ ⟩ -> ⟨ S (v₁ + v₂) ⟩
      closed-under-v* : {v : V} (k : K) -> ⟨ S v ⟩ -> ⟨ S (k v* v) ⟩

    opaque
      closed-under-v- : {v : V} -> ⟨ S v ⟩ -> ⟨ S (- v) ⟩
      closed-under-v- {v} sv = subst (\mv -> ⟨ S mv ⟩) v*-left-minus-one (closed-under-v* (- 1#) sv)


  isProp-isLinearSubtype : {ℓS : Level} {S : (Subtype V ℓS)} -> isProp (isLinearSubtype S)
  isProp-isLinearSubtype {S = S} ls1 ls2 i = record
    { closed-under-0v =
        snd (S 0#)
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



module _ {ℓK ℓV₁ ℓV₂ : Level}
         {K : Type ℓK} {V₁ : Type ℓV₁} {V₂ : Type ℓV₂}
         {{ACM-K : AdditiveCommMonoid K}}
         {{AG-K : AdditiveGroup ACM-K}}
         {{S-K : Semiring ACM-K}}
         {{R-K : Ring S-K AG-K}}
         {{ACM-V₁ : AdditiveCommMonoid V₁}} {{AG-V₁ : AdditiveGroup ACM-V₁}}
         {{ACM-V₂ : AdditiveCommMonoid V₂}} {{AG-V₂ : AdditiveGroup ACM-V₂}}
         {{MS₁ : ModuleStr R-K AG-V₁}}
         {{MS₂ : ModuleStr R-K AG-V₂}}
  where

  record isLinearTransformation (f : V₁ -> V₂) : Type (ℓ-max* 3 ℓK ℓV₁ ℓV₂) where
    constructor is-linear-transformation
    field
      preserves-+ : (v₁ v₂ : V₁) -> f (v₁ + v₂) == f v₁ + f v₂
      preserves-* : (k : K) (v : V₁) -> f (k v* v) == k v* f v


  opaque
    lt-preserves-+ : {f : V₁ -> V₂} -> isLinearTransformation f -> (v₁ v₂ : V₁) ->
                     f (v₁ + v₂) == f v₁ + f v₂
    lt-preserves-+ = isLinearTransformation.preserves-+

    lt-preserves-* : {f : V₁ -> V₂} -> isLinearTransformation f -> (k : K) -> (v : V₁) ->
                     f (k v* v) == k v* f v
    lt-preserves-* = isLinearTransformation.preserves-*

    lt-preserves-0v : {f : V₁ -> V₂} -> isLinearTransformation f -> f 0# == 0#
    lt-preserves-0v {f} lt = cong f (sym v*-left-zero) >=> lt-preserves-* lt 0# 0# >=> v*-left-zero

  module _ {ℓI : Level} {I : Type ℓI} {{FI : FinSetStr I}} where
    opaque
      lt-preserves-finiteSum : {f : V₁ -> V₂} {vs : I -> V₁} ->
        isLinearTransformation f -> f (finiteSum vs) == finiteSum (f ∘ vs)
      lt-preserves-finiteSum {f} lt = sym (finiteMerge-homo-inject h)
        where
        h : CommMonoidʰᵉ (CommMonoid-+ V₁) (CommMonoid-+ V₂) f
        h = record
          { monoidʰ = record
            { preserves-∙ = lt-preserves-+ lt
            ; preserves-ε = lt-preserves-0v lt
            }
          }
