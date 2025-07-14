{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.exact-sequence where

open import base
open import group
open import nat
open import truncation
open import functions
open import equivalence.base

record Short3Sequence (ℓA ℓB ℓC : Level) : Type (ℓ-suc (ℓ-max* 3 ℓA ℓB ℓC)) where
  field
    GA : Group ℓA
    GB : Group ℓB
    GC : Group ℓC

  A : Type ℓA
  A = fst GA
  B : Type ℓB
  B = fst GB
  C : Type ℓC
  C = fst GC

  field
    fʰ : Groupʰ GA GB
    gʰ : Groupʰ GB GC

record Short4Sequence (ℓA ℓB ℓC ℓD : Level) : Type (ℓ-suc (ℓ-max* 4 ℓA ℓB ℓC ℓD)) where
  field
    GA : Group ℓA
    GB : Group ℓB
    GC : Group ℓC
    GD : Group ℓD

  module GA = Group GA
  module GB = Group GB
  module GC = Group GC
  module GD = Group GD

  A : Type ℓA
  A = fst GA
  B : Type ℓB
  B = fst GB
  C : Type ℓC
  C = fst GC
  D : Type ℓD
  D = fst GD

  GSA : GroupStr A
  GSA = snd GA
  GSB : GroupStr B
  GSB = snd GB
  GSC : GroupStr C
  GSC = snd GC
  GSD : GroupStr D
  GSD = snd GD

  field
    fʰ : Groupʰ GA GB
    gʰ : Groupʰ GB GC
    hʰ : Groupʰ GC GD

  module fʰ = Groupʰ fʰ
  module gʰ = Groupʰ gʰ
  module hʰ = Groupʰ hʰ


  f : A -> B
  f = ⟨ fʰ ⟩
  g : B -> C
  g = ⟨ gʰ ⟩
  h : C -> D
  h = ⟨ hʰ ⟩



record ℕ⁻-Sequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    G : ℕ -> Group ℓ

  D : ℕ -> Type ℓ
  D n = ⟨ G n ⟩

  field
    fʰ : (n : ℕ) -> Groupʰ (G (suc n)) (G n)

  short3 : ℕ -> Short3Sequence ℓ ℓ ℓ
  short3 i = record
    { GA = G (suc (suc i))
    ; GB = G (suc i)
    ; GC = G i
    ; fʰ = fʰ (suc i)
    ; gʰ = fʰ i
    }

  short4 : ℕ -> Short4Sequence ℓ ℓ ℓ ℓ
  short4 i = record
    { GA = G (suc (suc (suc i)))
    ; GB = G (suc (suc i))
    ; GC = G (suc i)
    ; GD = G i
    ; fʰ = fʰ (suc (suc i))
    ; gʰ = fʰ (suc i)
    ; hʰ = fʰ i
    }


module _ {ℓA ℓB ℓC : Level} {GA : Group ℓA} {GB : Group ℓB} {GC : Group ℓC}
  where
  isExact-Pair : (f : Groupʰ GA GB) (g : Groupʰ GB GC) -> Type (ℓ-max* 3 ℓA ℓB ℓC)
  isExact-Pair (f , _) (g , _) =
    ∀ b -> ∥ fiber f b ∥ <-> (g b == Group.ε GC)

module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  private
    module S = Short3Sequence S
  record isExact-Short3Sequence : Type (ℓ-max* 3 ℓA ℓB ℓC) where
    field
      isExact : isExact-Pair S.fʰ S.gʰ

module _ {ℓA ℓB ℓC ℓD : Level} (S : Short4Sequence ℓA ℓB ℓC ℓD) where
  private
    module S = Short4Sequence S
  record isExact-Short4Sequence : Type (ℓ-max* 4 ℓA ℓB ℓC ℓD) where
    field
      isExact₁ : isExact-Pair S.fʰ S.gʰ
      isExact₂ : isExact-Pair S.gʰ S.hʰ

module _ {ℓ : Level} (S : ℕ⁻-Sequence ℓ) where
  private
    module S = ℕ⁻-Sequence S

  record isExact-ℕ⁻-Sequence : Type ℓ where
    field
      isExact : (n : ℕ) -> isExact-Pair (S.fʰ (suc n)) (S.fʰ n)

    isExact-short3 : (n : ℕ) -> isExact-Short3Sequence (S.short3 n)
    isExact-short3 n = record { isExact = isExact n }

    isExact-short4 : (n : ℕ) -> isExact-Short4Sequence (S.short4 n)
    isExact-short4 n = record { isExact₁ = isExact (suc n) ; isExact₂ = isExact n}
