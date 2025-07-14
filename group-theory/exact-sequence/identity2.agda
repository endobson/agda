{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.exact-sequence.identity2 where


open import base
open import group
open import hlevel.base
open import equality-path
open import functions
open import group.instance-syntax
open import truncation
open import isomorphism
open import equivalence.injective-surjective
open import equivalence.base
open import group-theory.instances.trivial
open import group-theory.exact-sequence



module _ {ℓA ℓB ℓC ℓD : Level}
         ((S , E) : Σ (Short4Sequence ℓA ℓB ℓC ℓD) isExact-Short4Sequence)
  where

  private
    module S = Short4Sequence S
    module E = isExact-Short4Sequence E

    instance
      IGSB = S.GSB
      IGSC = S.GSC

  module _
    (isZeroGroup-A : isZeroGroup S.GA)
    (isZeroGroup-D : isZeroGroup S.GD)
    where
    private
      isInjective-g : isInjective S.g
      isInjective-g {b₁} {b₂} gb₁=gb₂ =
        ∥-elim (\_ -> S.GB.isSet-Domain _ _) handle fib
        where
        g[b₁-b₂]=ε : S.g (b₁ ∙ (b₂ ⁻¹)) == ε
        g[b₁-b₂]=ε =
          S.gʰ.preserves-∙ b₁ (b₂ ⁻¹) >=>
          cong2 _∙_ gb₁=gb₂ (S.gʰ.preserves-inverse b₂) >=>
          ∙-right-inverse

        fib : ∥ fiber S.f (b₁ ∙ (b₂ ⁻¹)) ∥
        fib = proj₂ (E.isExact₁ (b₁ ∙ (b₂ ⁻¹))) g[b₁-b₂]=ε

        handle : fiber S.f (b₁ ∙ (b₂ ⁻¹)) -> b₁ == b₂
        handle (c , p) = sym p₂
          where
          p₂ : b₂ == b₁
          p₂ =
            sym ∙-left-ε >=>
            cong (_∙ b₂) (sym S.fʰ.preserves-ε >=>
                          cong S.f (isContr->isProp isZeroGroup-A _ _) >=>
                          p) >=>
            ∙-assoc >=>
            cong (b₁ ∙_) ∙-left-inverse >=>
            ∙-right-ε


      isSurjective-g : isSurjective S.g
      isSurjective-g c = proj₂ (E.isExact₂ c) (isContr->isProp isZeroGroup-D _ _)

      isEquiv-g : isEquiv S.g
      isEquiv-g =
        isEmbedding-isSurjective->isEquiv
          (isSet-isInjective->isEmbedding S.GC.isSet-Domain isInjective-g)
          isSurjective-g

      ig : S.C -> S.B
      ig = isEqInv isEquiv-g

      isGroupʰ-ig : isGroupʰ S.GC S.GB ig
      isGroupʰ-ig = record
        { preserves-∙ = p∙
        ; preserves-ε = pε
        ; preserves-inverse = pi
        }
        where

        p∙ : ∀ x y -> ig (x ∙ y) == ig x ∙ ig y
        p∙ x y =
          cong ig (sym (cong2 _∙_ (isEqSec isEquiv-g x) (isEqSec isEquiv-g y)) >=>
                   sym (S.gʰ.preserves-∙ (ig x) (ig y))) >=>
          isEqRet isEquiv-g (ig x ∙ ig y)


        pε : ig ε == ε
        pε = cong ig (sym S.gʰ.preserves-ε) >=> isEqRet isEquiv-g ε

        pi : ∀ x -> ig (x ⁻¹) == (ig x) ⁻¹
        pi x =
          cong ig (sym (cong _⁻¹ (isEqSec isEquiv-g x)) >=>
                   sym (S.gʰ.preserves-inverse (ig x))) >=>
          isEqRet isEquiv-g ((ig x) ⁻¹)

      isGroupIso-g : isGroupIso S.gʰ
      isGroupIso-g = record
        { inv = ig , isGroupʰ-ig
        ; rightInv = \x -> isEqSec isEquiv-g x
        ; leftInv = \x -> isEqRet isEquiv-g x
        }

    0AB0-exact-sequence->isGroupIso : isGroupIso S.gʰ
    0AB0-exact-sequence->isGroupIso = isGroupIso-g

    0AB0-exact-sequence->GroupIso : GroupIso S.GB S.GC
    0AB0-exact-sequence->GroupIso = S.gʰ , 0AB0-exact-sequence->isGroupIso
