{-# OPTIONS --cubical --safe --exact-split #-}

module group-theory.exact-sequence.identity where


open import base
open import group
open import equality-path
open import functions
open import truncation
open import isomorphism
open import equivalence.injective-surjective
open import equivalence.base
open import group-theory.instances.trivial
open import group-theory.exact-sequence



module _ {ℓ₁ ℓ₂ : Level}
         {G₁ : Group ℓ₁}
         {G₂ : Group ℓ₂}
         (f : Groupʰ ZeroGroup G₁)
         (g : Groupʰ G₁ G₂)
         (h : Groupʰ G₂ ZeroGroup)
         (e₁ : isExact-Pair f g)
         (e₂ : isExact-Pair g h)
  where
  private
    module G₁ = Group G₁
    module G₂ = Group G₂
    module f = Groupʰ f
    module g = Groupʰ g

    f' : Top -> G₁.D
    f' = ⟨ f ⟩
    g' : G₁.D -> G₂.D
    g' = ⟨ g ⟩
    h' : G₂.D -> Top
    h' = ⟨ h ⟩

    isInjective-g' : isInjective g'
    isInjective-g' {a₁} {a₂} ga₁=ga₂ =
      ∥-elim (\_ -> G₁.isSet-Domain _ _) handle fib
      where
      g[a₁-a₂]=ε : g' (a₁ G₁.∙ (G₁.inverse a₂)) == G₂.ε
      g[a₁-a₂]=ε =
        g.preserves-∙ a₁ (G₁.inverse a₂) >=>
        cong2 G₂._∙_ ga₁=ga₂ (g.preserves-inverse a₂) >=>
        G₂.∙-right-inverse

      fib : ∥ fiber f' (a₁ G₁.∙ (G₁.inverse a₂)) ∥
      fib = proj₂ (e₁ (a₁ G₁.∙ (G₁.inverse a₂))) g[a₁-a₂]=ε


      handle : fiber f' (a₁ G₁.∙ (G₁.inverse a₂)) ->
               a₁ == a₂
      handle (tt , p) = sym p₂
        where
        p₂ : a₂ == a₁
        p₂ =
          sym G₁.∙-left-ε >=>
          cong (G₁._∙ a₂) (sym f.preserves-ε >=> p) >=>
          G₁.∙-assoc >=>
          cong (a₁ G₁.∙_) G₁.∙-left-inverse >=>
          G₁.∙-right-ε

    isSurjective-g' : isSurjective g'
    isSurjective-g' b = proj₂ (e₂ b) refl

    isEquiv-g' : isEquiv g'
    isEquiv-g' =
      isEmbedding-isSurjective->isEquiv
        (isSet-isInjective->isEmbedding G₂.isSet-Domain isInjective-g')
        isSurjective-g'

    ig' : G₂.D -> G₁.D
    ig' = isEqInv isEquiv-g'

    isGroupʰ-ig' : isGroupʰ G₂ G₁ ig'
    isGroupʰ-ig' = record
      { preserves-∙ = p∙
      ; preserves-ε = pε
      ; preserves-inverse = pi
      }
      where

      p∙ : ∀ x y -> ig' (x G₂.∙ y) == ig' x G₁.∙ ig' y
      p∙ x y =
        cong ig' (sym (cong2 G₂._∙_ (isEqSec isEquiv-g' x) (isEqSec isEquiv-g' y)) >=>
                  sym (g.preserves-∙ (ig' x) (ig' y))) >=>
        isEqRet isEquiv-g' (ig' x G₁.∙ ig' y)


      pε : ig' G₂.ε == G₁.ε
      pε = cong ig' (sym g.preserves-ε) >=> isEqRet isEquiv-g' G₁.ε

      pi : ∀ x -> ig' (G₂.inverse x) == G₁.inverse (ig' x)
      pi x =
        cong ig' (sym (cong G₂.inverse (isEqSec isEquiv-g' x)) >=>
                  sym (g.preserves-inverse (ig' x))) >=>
        isEqRet isEquiv-g' (G₁.inverse (ig' x))


    isGroupIso-g : isGroupIso g
    isGroupIso-g = record
      { inv = ig' , isGroupʰ-ig'
      ; rightInv = \x -> isEqSec isEquiv-g' x
      ; leftInv = \x -> isEqRet isEquiv-g' x
      }

  0AB0-exact-pairs->isGroupIso : isGroupIso g
  0AB0-exact-pairs->isGroupIso = isGroupIso-g

  0AB0-exact-pairs->GroupIso : GroupIso G₁ G₂
  0AB0-exact-pairs->GroupIso = g , isGroupIso-g
