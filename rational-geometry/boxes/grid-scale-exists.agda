{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.grid-scale-exists where

open import abs
open import additive-group
open import additive-group.instances.int
open import base
open import equality-path
open import finite-commutative-semigroup
open import finite-commutative-semigroup.property
open import finset.inhabited
open import fraction.canonical
open import functions
open import gcd.propositional
open import hlevel.base
open import hlevel.sigma
open import int.base
open import int.order
open import int.sign
open import nat
open import order
open import order.instances.int
open import ordered-additive-group
open import ordered-semiring
open import ordered-semiring.natural-reciprocal
open import ordered-semiring.instances.rational
open import rational
open import rational-geometry.boxes.base
open import rational-geometry.boxes.box
open import rational-geometry.boxes.grid-aligned
open import rational-geometry.boxes.grid-aligned.arithmetic
open import rational.canonical-fraction
open import rational.order
open import relation
open import ring
open import ring.implementations.int
open import ring.implementations.rational
open import semigroup
open import semiring
open import semiring.natural-reciprocal
open import set-quotient
open import sigma.base
open import truncation

private
  ℚ->Σscale : (q : ℚ) -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u q)
  ℚ->Σscale q = case (trichotomous-< 0# q) of
    (\{ (tri< 0<q _ _) -> (q , 0<q) , (1# , *-left-one)
      ; (tri= _ 0=q _) -> (1# , 0<1) , (0# , *-right-one >=> 0=q)
      ; (tri> _ _ q<0) -> (- q , minus-flips-<0 q<0) ,
                          (- 1# , *-left (ℤ->ℚ-preserves-minus _) >=>
                          minus-extract-both >=> *-left-one)
      })

  remove-numerator : ℚ -> ℚ
  remove-numerator q = 1/ℕ (dℕ₁ , Pos-dℕ₁)
    where
    f = ℚ->ℚ' q
    dℕ₁ = abs' (ℚ'.denominator f)
    Pos-dℕ₁ = Pos'-abs' (ℚ'.NonZero-denominator f)

  is1/ℕ : ℚ -> Type₀
  is1/ℕ q = Σ[ n ∈ Nat⁺ ] (q == 1/ℕ n)

  *-preserves-is1/ℕ : {a b : ℚ} -> is1/ℕ a -> is1/ℕ b -> is1/ℕ (a * b)
  *-preserves-is1/ℕ {a} {b} (na , pa) (nb , pb) =
    (na *⁺ nb , *-cong pa pb >=> sym (1/ℕ-distrib-* na nb))

  is1/ℕ-remove-numerator : {q : ℚ} -> is1/ℕ (remove-numerator q)
  is1/ℕ-remove-numerator {q} = _ , refl

  ℚ->ℚ'-1/ℕ : ∀ (n : Nat⁺) -> ℚ->ℚ' (1/ℕ n) == 1/ℕ' n
  ℚ->ℚ'-1/ℕ n = ∃!-unique (ℚ->∃!ℚ' (1/ℕ n)) _ (refl , canon)
    where
    canon : isCanonicalℚ' (1/ℕ' n)
    canon = record
      { 0<d = Pos'->Pos (snd n)
      ; lowest-terms = gcd'->gcd 0≤nonneg (gcd'-sym gcd'-one)
      }


  remove-numerator-1/ℕ : {n : Nat⁺} -> remove-numerator (1/ℕ n) == (1/ℕ n)
  remove-numerator-1/ℕ {n⁺} = path
    where
    f = ℚ->ℚ' (1/ℕ n⁺)
    d : ℕ
    d = abs' (ℚ'.denominator f)
    d⁺ : Nat⁺
    d⁺ = d , Pos'-abs' (ℚ'.NonZero-denominator f)
    path : 1/ℕ d⁺ == 1/ℕ n⁺
    path = cong 1/ℕ (ΣProp-path isPropPos' (cong (abs' ∘ ℚ'.denominator) (ℚ->ℚ'-1/ℕ n⁺)))

  remove-numerator-is1/ℕ : {q : ℚ} -> is1/ℕ q -> remove-numerator q == q
  remove-numerator-is1/ℕ (n , p) =
    cong remove-numerator p >=> remove-numerator-1/ℕ >=> sym p


private
  opaque
    ℚ⁺²->Σscale : (q₁ q₂ : ℚ⁺) -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u ⟨ q₁ ⟩ × isGridAligned u ⟨ q₂ ⟩)
    ℚ⁺²->Σscale (q₁ , 0<q₁) (q₂ , 0<q₂) = (u , 0<u) , (s₁ , p₁) , (s₂ , p₂)
      where
      f₁ f₂ : ℚ'
      f₁ = ℚ->ℚ' q₁
      f₂ = ℚ->ℚ' q₂
      d₁ d₂ : ℤ
      d₁ = ℚ'.denominator f₁
      d₂ = ℚ'.denominator f₂

      dℕ₁ dℕ₂ : ℕ
      dℕ₁ = abs' (ℚ'.denominator f₁)
      dℕ₂ = abs' (ℚ'.denominator f₂)
      Pos-dℕ₁ : Pos' dℕ₁
      Pos-dℕ₁ = Pos'-abs' (ℚ'.NonZero-denominator f₁)
      Pos-dℕ₂ : Pos' dℕ₂
      Pos-dℕ₂ = Pos'-abs' (ℚ'.NonZero-denominator f₂)

      d₁-path : d₁ == int dℕ₁
      d₁-path = nonneg-abs' (weaken-< (isCanonicalℚ'.0<d (isCanonical-ℚ->ℚ' _)))
      d₂-path : d₂ == int dℕ₂
      d₂-path = nonneg-abs' (weaken-< (isCanonicalℚ'.0<d (isCanonical-ℚ->ℚ' _)))

      u : ℚ
      u = (remove-numerator q₁) * (remove-numerator q₂)
      0<u : 0# < u
      0<u = *-preserves-0< (0<1/ℕ _) (0<1/ℕ _)

      s₁ : ℤ
      s₁ = ℚ'.numerator f₁ * ℚ'.denominator f₂
      p₁ : ℤ->ℚ s₁ * u == q₁
      p₁ =
        *-left (ℤ->ℚ-preserves-* _ _) >=>
        *-swap >=>
        *-right (*-left (cong ℤ->ℚ d₂-path) >=> *-commute >=> 1/ℕ-ℕ-path _) >=>
        *-right-one >=>
        p₁' >=>
        ℚ->ℚ'->ℚ q₁
        where
        opaque
          unfolding _r*_ ℚ'->ℚ
          p₁' : ℤ->ℚ (ℚ'.numerator f₁) * 1/ℕ (dℕ₁ , Pos-dℕ₁) == ℚ'->ℚ f₁
          p₁' = eq/ _ _ (cong2 _*_ *-right-one (sym *-left-one >=> *-right d₁-path))
      s₂ : ℤ
      s₂ = ℚ'.numerator f₂ * ℚ'.denominator f₁
      p₂ : ℤ->ℚ s₂ * u == q₂
      p₂ =
        *-right *-commute >=>
        *-left (ℤ->ℚ-preserves-* _ _) >=>
        *-swap >=>
        *-right (*-left (cong ℤ->ℚ d₁-path) >=> *-commute >=> 1/ℕ-ℕ-path _) >=>
        *-right-one >=>
        p₂' >=>
        ℚ->ℚ'->ℚ q₂
        where
        opaque
          unfolding _r*_ ℚ'->ℚ
          p₂' : ℤ->ℚ (ℚ'.numerator f₂) * 1/ℕ (dℕ₂ , Pos-dℕ₂) == ℚ'->ℚ f₂
          p₂' = eq/ _ _ (cong2 _*_ *-right-one (sym *-left-one >=> *-right d₂-path))

  ℚ⁺²->scale : ℚ⁺ -> ℚ⁺ -> ℚ⁺
  ℚ⁺²->scale a b = fst (ℚ⁺²->Σscale a b)

  opaque
    unfolding ℚ⁺²->Σscale

    ℚ⁺²->scale-assoc : (a b c : ℚ⁺) -> ℚ⁺²->scale (ℚ⁺²->scale a b) c == ℚ⁺²->scale a (ℚ⁺²->scale b c)
    ℚ⁺²->scale-assoc (a , 0<a) (b , 0<b) (c , 0<c) = ΣProp-path isProp-< path
      where
      rn : ℚ -> ℚ
      rn = remove-numerator
      rn-distrib : ∀ x y -> rn (rn x * rn y) == rn x * rn y
      rn-distrib x y =
        remove-numerator-is1/ℕ (*-preserves-is1/ℕ is1/ℕ-remove-numerator is1/ℕ-remove-numerator)
      path : rn (rn a * rn b) * rn c == rn a * (rn (rn b * rn c))
      path = *-left (rn-distrib a b) >=> *-assoc >=> *-right (sym (rn-distrib b c))

    ℚ⁺²->scale-commute : (a b : ℚ⁺) -> ℚ⁺²->scale a b == ℚ⁺²->scale b a
    ℚ⁺²->scale-commute a b = ΣProp-path isProp-< *-commute

  CSS-ℚ⁺²->scale : CommutativeSemigroupStr ℚ⁺
  CSS-ℚ⁺²->scale = record
    { _∙_ = ℚ⁺²->scale
    ; ∙-assoc = \{a} {b} {c} -> ℚ⁺²->scale-assoc a b c
    ; ∙-commute = \{a} {b} -> ℚ⁺²->scale-commute a b
    ; isSet-Domain = isSetΣ isSetℚ (\_ -> isProp->isSet isProp-<)
    }


  opaque
    ℚ<>0²->Σscale : (q₁ q₂ : Σ[ q ∈ ℚ ] (q <> 0#)) -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u ⟨ q₁ ⟩ × isGridAligned u ⟨ q₂ ⟩)
    ℚ<>0²->Σscale (q₁ , inj-l q₁<0) (q₂ , inj-l q₂<0) =
      case (ℚ⁺²->Σscale (- q₁ , minus-flips-<0 q₁<0) (- q₂ , minus-flips-<0 q₂<0)) of
        (\{ (u , a₁ , a₂) -> u , isGridAligned-minus⁻ u _ a₁ , isGridAligned-minus⁻ u _ a₂ })
    ℚ<>0²->Σscale (q₁ , inj-l q₁<0) (q₂ , inj-r 0<q₂) =
      case (ℚ⁺²->Σscale (- q₁ , minus-flips-<0 q₁<0) (q₂ , 0<q₂)) of
        (\{ (u , a₁ , a₂) -> u , isGridAligned-minus⁻ u _ a₁ , a₂ })
    ℚ<>0²->Σscale (q₁ , inj-r 0<q₁) (q₂ , inj-l q₂<0) =
      case (ℚ⁺²->Σscale (q₁ , 0<q₁) (- q₂ , minus-flips-<0 q₂<0)) of
        (\{ (u , a₁ , a₂) -> u , a₁ , isGridAligned-minus⁻ u _ a₂ })
    ℚ<>0²->Σscale (q₁ , inj-r 0<q₁) (q₂ , inj-r 0<q₂) =
      case (ℚ⁺²->Σscale (q₁ , 0<q₁) (q₂ , 0<q₂)) of
        (\{ (u , a₁ , a₂) -> u , a₁ , a₂ })

opaque
  ℚ²->Σscale : (q₁ q₂ : ℚ) -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u q₁ × isGridAligned u q₂)
  ℚ²->Σscale q₁ q₂ = case (trichotomous-< 0# q₁ , trichotomous-< 0# q₂) of
    (\{ (tri< 0<q₁ _ _ , tri< 0<q₂ _ _) -> ℚ<>0²->Σscale (q₁ , inj-r 0<q₁) (q₂ , inj-r 0<q₂)
      ; (tri< 0<q₁ _ _ , tri> _ _ q₂<0) -> ℚ<>0²->Σscale (q₁ , inj-r 0<q₁) (q₂ , inj-l q₂<0)
      ; (tri> _ _ q₁<0 , tri< 0<q₂ _ _) -> ℚ<>0²->Σscale (q₁ , inj-l q₁<0) (q₂ , inj-r 0<q₂)
      ; (tri> _ _ q₁<0 , tri> _ _ q₂<0) -> ℚ<>0²->Σscale (q₁ , inj-l q₁<0) (q₂ , inj-l q₂<0)
      ; (tri< 0<q₁ _ _ , tri= _ 0=q₂ _) -> case (ℚ->Σscale q₁) of
        \{ (u , a₁) -> u , a₁ , (0# , *-left-zero >=> 0=q₂) }
      ; (tri> _ _ 0<q₁ , tri= _ 0=q₂ _) -> case (ℚ->Σscale q₁) of
        \{ (u , a₁) -> u , a₁ , (0# , *-left-zero >=> 0=q₂) }
      ; (tri= _ 0=q₁ _ , _            ) -> case (ℚ->Σscale q₂) of
        \{ (u , a₂) -> u , (0# , *-left-zero >=> 0=q₁) , a₂ }
      })

private
  opaque
    Box->Σscale : (b : Box) -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u b)
    Box->Σscale b = u ,
      refine-isGridAligned _ u₁ u (proj₁ (snd Σu₁)) (proj₁ (snd Σu)) ,
      refine-isGridAligned _ u₁ u (proj₂ (snd Σu₁)) (proj₁ (snd Σu)) ,
      refine-isGridAligned _ u₂ u (proj₁ (snd Σu₂)) (proj₂ (snd Σu)) ,
      refine-isGridAligned _ u₂ u (proj₂ (snd Σu₂)) (proj₂ (snd Σu))
      where
      module b = Box b
      Σu₁ : Σ[ u ∈ ℚ⁺ ] (isGridAligned u b.left × isGridAligned u b.right)
      Σu₁ = ℚ²->Σscale b.left b.right
      Σu₂ : Σ[ u ∈ ℚ⁺ ] (isGridAligned u b.bottom × isGridAligned u b.top)
      Σu₂ = ℚ²->Σscale b.bottom b.top
      u₁ : ℚ⁺
      u₁ = ⟨ Σu₁ ⟩
      u₂ : ℚ⁺
      u₂ = ⟨ Σu₂ ⟩

      Σu : Σ[ u ∈ ℚ⁺ ] (isGridAligned u ⟨ u₁ ⟩ × isGridAligned u ⟨ u₂ ⟩)
      Σu = ℚ²->Σscale ⟨ u₁ ⟩ ⟨ u₂ ⟩
      u : ℚ⁺
      u = ⟨ Σu ⟩

  opaque
    Boxes⁰->Σscale : {ℓ : Level} (b : Boxes ℓ) -> ¬ (Boxes.I b) -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u b)
    Boxes⁰->Σscale b ¬i = (1# , 0<1) , \i -> bot-elim (¬i i)
    Boxes⁺->Σscale : {ℓ : Level} (b : Boxes ℓ) -> ∥ Boxes.I b ∥ -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u b)
    Boxes⁺->Σscale {ℓ} b i = u , a
      where
      I⁺ : Fin⁺Set ℓ
      I⁺ = (Boxes.I b , snd (Boxes.Index b) , i)
      instance
        FI : Fin⁺SetStr (Boxes.I b)
        FI = record { isFin = snd (Boxes.Index b) ; inhabited = i }

      f : Boxes.I b -> ℚ⁺
      f i = fst (Box->Σscale (Boxes.box b i))

      u : ℚ⁺
      u = finite⁺Mergeᵉ CSS-ℚ⁺²->scale I⁺ f

      a : isGridAligned u b
      a i =
        finite⁺Merge-somewhere CSS-ℚ⁺²->scale (\v -> isProp-isGridAligned v (Boxes.box b i)) f
          ∣ i , snd (Box->Σscale (Boxes.box b i)) ∣
          r
        where
        r : (s₁ s₂ : ℚ⁺) ->
            isGridAligned s₁ (Boxes.box b i) ->
            isGridAligned (ℚ⁺²->scale s₁ s₂) (Boxes.box b i)
        r s₁ s₂ (al , ar , ab , at) =
          refine-isGridAligned _ s₁ s al as ,
          refine-isGridAligned _ s₁ s ar as ,
          refine-isGridAligned _ s₁ s ab as ,
          refine-isGridAligned _ s₁ s at as
          where
          Σs : Σ[ u ∈ ℚ⁺ ] (isGridAligned u ⟨ s₁ ⟩ × isGridAligned u ⟨ s₂ ⟩)
          Σs = ℚ⁺²->Σscale s₁ s₂
          s : ℚ⁺
          s = fst Σs
          as : isGridAligned s ⟨ s₁ ⟩
          as = proj₁ (snd Σs)


opaque
  Boxes->Σscale : {ℓ : Level} (b : Boxes ℓ) -> Σ[ u ∈ ℚ⁺ ] (isGridAligned u b)
  Boxes->Σscale b = case (decide-isFin⁺Set (snd (Boxes.Index b))) of
    (\{ (inj-l (_ , i)) -> Boxes⁺->Σscale b i
      ; (inj-r ¬i) -> Boxes⁰->Σscale b ¬i
      })
