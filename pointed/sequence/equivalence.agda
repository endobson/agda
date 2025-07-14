{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.sequence.equivalence where

open import base
open import cubical
open import nat
open import equality-path
open import equality.square
open import functions
open import functions.embedding
open import hlevel.base
open import equivalence
open import isomorphism
open import type-algebra
open import pointed.base
open import pointed.loop-space
open import pointed.loop-space.embedding
open import pointed.sequence
open import pointed.function
open import pointed.pullback
open import univalence
open import equivalence.base

private
  module _ {ℓA : Level} {A : I -> Type ℓA} {a₀ : A i0} {a₁ a₁' : A i1}
    (p : PathP A a₀ a₁) (q : a₁ == a₁') where

    transP-lemma₁ : transP-sym (symP p) (transP-left p q) == q
    transP-lemma₁ =
      (\k -> transP-sym (\i -> (p (~ i ∨ k)))
               (transP-left (\i -> (p (i ∨ k))) q)) >=>
      cong (transP-sym refl) (compPath-refl-left q) >=>
      (\k -> transP-sides refl (\i -> q (i ∧ k)) (\i -> q (i ∨ k))) >=>
      transP-sides-filler refl q refl

  module _ {ℓA : Level} {A : I -> Type ℓA} {a₀ : A i0} {a₁ a₁' : A i1}
    (p : PathP A a₀ a₁) (q : PathP A a₀ a₁') where

    transP-lemma₂ : (transP-left p (transP-sym (symP p) q)) == q
    transP-lemma₂ = check₄
      where
      invert : PathP (\j -> p (~ j) == q (~ j)) (transP-sym (symP p) q) (reflᵉ a₀)
      invert = transP-sides-filler (symP p) refl q

      check₂ : PathP (\j -> PathP (\i -> A (i ∧ ~ j)) a₀ (q (~ j)))
                     (transP-mid refl p (transP-sym (symP p) q))
                     (transP-mid refl refl refl)
      check₂ j = (transP-mid refl (\i -> p (i ∧ ~ j)) (invert j))

      check₃ : PathP (\j -> PathP (\i -> A (i ∧ j)) a₀ (q j))
                     (transP-mid refl refl refl)
                     (transP-mid refl q refl)
      check₃ j = (transP-mid refl (\i -> q (i ∧ j)) refl)

      check₄ : (transP-mid refl p (transP-sym (symP p) q)) ==
               q
      check₄ = transP-sym check₂ check₃ >=> sym (transP-mid-filler refl q refl)




module _ {ℓA ℓB ℓC : Level}
  {A∙ : Type∙ ℓA}
  {B∙ : Type∙ ℓB}
  {C∙ : Type∙ ℓC}
  (A≃B : A∙ ≃∙ B∙)
  where
  ->∙/≃ : (f∙ : A∙ ->∙ C∙) (g∙ : B∙ ->∙ C∙) -> Type _
  ->∙/≃ f∙ g∙ = ->∙Tri (->∙-cons (fst (fst A≃B)) (snd A≃B)) f∙ g∙



module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  open Short3Sequence S

  record isFiberSequence-Short3-eq : Type (ℓ-max* 3 ℓA ℓB ℓC) where
    field
      eq : A∙ ≃∙ (fiber∙ g∙)
      f-tri : ->∙/≃ eq f∙ (->∙-cons fst refl)


module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  private
    module S = Short3Sequence S

  main->eq : isFiberSequence-Short3 S -> isFiberSequence-Short3-eq S
  main->eq F = record
    { eq = (F.total , F.isEquiv-total) , p
    ; f-tri = [ f-path ]
    }
    where
    module F = isFiberSequence-Short3 F

    p : (S.f S.★A , F.isNull S.★A) == (S.★B , S.gp)
    p i = S.fp i , F.isNull-Square i

    f-path : S.f∙ == (->∙-cons S.f (S.fp >=> refl))
    f-path k = ->∙-cons S.f (compPath-refl-right S.fp (~ k))


  eq->main : isFiberSequence-Short3-eq S -> isFiberSequence-Short3 S
  eq->main F = record
    { isNull = isNull
    ; isNull-Square = isNull-Square
    ; isEquiv-total = subst isEquiv total-path isEquiv-total
    }
    where
    module F = isFiberSequence-Short3-eq F

    total : S.A -> fiber S.g S.★C
    total = fst (fst F.eq)

    isEquiv-total : isEquiv total
    isEquiv-total = snd (fst F.eq)

    p : total S.★A == (S.★B , S.gp)
    p = snd F.eq

    f-path : S.f∙ == (->∙-cons total p) >∙> (->∙-cons fst refl)
    f-path = ->∙Tri.path F.f-tri

    f-total-path : S.f == fst ∘ total
    f-total-path k a = app∙ (f-path k) a

    fp-total-path : PathP (\i -> f-total-path i S.★A == S.★B) S.fp (cong fst p >=> refl)
    fp-total-path k = ->∙-path (f-path k)

    fp-total-path' : PathP (\i -> f-total-path i S.★A == S.★B) S.fp (cong fst p)
    fp-total-path' = transP-left fp-total-path (compPath-refl-right (cong fst p))

    step₁ : PathP (\i -> S.g (fst (p i)) == S.★C) (snd (total S.★A)) S.gp
    step₁ k = snd (p k)

    step₂ : (cong S.g (\i -> (app∙ (f-path i) S.★A)) ∙∙ refl ∙∙
             (\i -> S.g (fst (p i)))) == cong S.g S.fp
    step₂ = sym (cong-∙∙ S.g _ _ _) >=> cong (cong S.g) inner
      where
      inner : (\i -> (app∙ (f-path i) S.★A)) ∙∙ refl ∙∙ cong fst p == S.fp
      inner =
        (\k -> (\i -> (app∙ (f-path i) S.★A)) ∙∙ (\i -> fst (p (i ∧ k))) ∙∙ (\i -> fst (p (i ∨ k)))) >=>
        (transP-sym (symP (doubleCompPath-filler _ _ _))
                    (symP fp-total-path'))

    isNull : ∀ a -> app∙ S.g∙ (app∙ S.f∙ a) == S.★C
    isNull a = cong S.g (\i -> (f-total-path i a)) ∙∙ snd (total a) ∙∙ refl

    total' : S.A -> fiber S.g S.★C
    total' a = S.f a , isNull a

    isNull-filler : ∀ a ->
      Square
        (\i -> (snd (total a) i)) (isNull a)
        (\i -> S.g (app∙ (f-path (~ i)) a))
        refl
    isNull-filler a =
      doubleCompPath-filler (\i -> app∙ S.g∙ (app∙ (f-path i) a)) (snd (total a)) refl

    isNull-Square :
      Square
        (isNull S.★A) S.gp
        (cong S.g S.fp)
        refl
    isNull-Square =
      ▪ᵀ (transP-mid (sym step₂) (▪ᵀ (symP (isNull-filler S.★A) ▪h refl ▪h step₁)) ∙∙-refl)


    total-path : total == total'
    total-path k a = f-total-path (~ k) a , (isNull-filler a k)



module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  private
    module S = Short3Sequence S

  Ωf-Short3Sequence : Short3Sequence ℓA ℓB ℓC
  Ωf-Short3Sequence = record
    { A∙ = Ω S.A∙
    ; B∙ = Ω S.B∙
    ; C∙ = Ω S.C∙
    ; f∙ = Ωf S.f∙
    ; g∙ = Ωf S.g∙
    }

private
  module _ {ℓA ℓB ℓC : Level} {S : Short3Sequence ℓA ℓB ℓC}
           (F : isFiberSequence-Short3-eq S)
    where
    private
      module S = Short3Sequence S
      module F = isFiberSequence-Short3-eq F

    Ωf-Short3FiberSequence' : isFiberSequence-Short3-eq (Ωf-Short3Sequence S)
    Ωf-Short3FiberSequence' = F'
      where
      S' : (Short3Sequence ℓA ℓB ℓC)
      S' = Ωf-Short3Sequence S
      module S' = Short3Sequence S'

      e₀ : S.A∙ ->∙ (fiber∙ S.g∙)
      e₀ = ->∙-cons (fst (fst F.eq)) (snd F.eq)

      e₁ : S'.A∙ ->∙ (Ω (fiber∙ S.g∙))
      e₁ = Ωf e₀

      eq₁ : S'.A∙ ≃∙ (Ω (fiber∙ S.g∙))
      eq₁ = (app∙ e₁ , isEmbedding->isEquiv-Ωf e₀ (isEquiv->isEmbedding (snd (fst F.eq)))) ,
            (->∙-path e₁)

      eq₂ : Ω (fiber∙ S.g∙) ≃∙ fiber∙ (Ωf S.g∙)
      eq₂ = (fiber∙-Ωf-eq∙₄ S.g∙)

      e₂ : Ω (fiber∙ S.g∙) ->∙ fiber∙ (Ωf S.g∙)
      e₂ = ->∙-cons (fst (fst eq₂)) (snd eq₂)


      t₀ : ->∙Tri e₀ S.f∙ (->∙-cons fst refl)
      t₀ = F.f-tri

      t₁ : ->∙Tri e₁ S'.f∙ (Ωf (->∙-cons fst refl))
      t₁ = Ω->∙Tri t₀

      t₂ : ->∙Tri e₂ (Ωf (->∙-cons fst refl)) (->∙-cons fst refl)
      t₂ = fiber∙-Ωf-eq∙₄-∙Tri S.g∙

      eq : S'.A∙ ≃∙ (fiber∙ S'.g∙)
      eq = eq₁ >≃∙> eq₂


      F' : isFiberSequence-Short3-eq S'
      F' = record
        { eq = eq
        ; f-tri = ∘->∙Tri t₁ t₂
        }


module _ {ℓA ℓB ℓC : Level} {S : Short3Sequence ℓA ℓB ℓC}
         (F : isFiberSequence-Short3 S)
  where
  private
    S' : (Short3Sequence ℓA ℓB ℓC)
    S' = Ωf-Short3Sequence S

  Ωf-Short3FiberSequence : isFiberSequence-Short3 (Ωf-Short3Sequence S)
  Ωf-Short3FiberSequence = eq->main S' (Ωf-Short3FiberSequence' (main->eq S F))






module _ {ℓ : Level} (X∙@(X , ★X) : Type∙ ℓ) (fib : X -> Type∙ ℓ) where
  private
    P : X -> Type ℓ
    P = fst ∘ fib
    ★P : P ★X
    ★P = snd (fib ★X)

    A∙ B∙ C∙ : Type∙ ℓ
    A∙ = Ω (TotalSpace∙ X∙ fib)
    B∙ = Ω X∙
    C∙ = fib ★X

    A B C : Type ℓ
    A = ⟨ A∙ ⟩
    B = ⟨ B∙ ⟩
    C = ⟨ C∙ ⟩

    f∙ : A∙ ->∙ B∙
    f∙ = Ωf (->∙-cons fst refl)
    g∙ : B∙ ->∙ C∙
    g∙ = ->∙-cons (\p -> transport (\i -> (P (p i))) ★P) (transportRefl ★P)


    S : Short3Sequence ℓ ℓ ℓ
    S = record { A∙ = A∙ ; B∙ = B∙ ; C∙ = C∙ ; f∙ = f∙ ; g∙ = g∙ }

    F : isFiberSequence-Short3-eq S
    F = record
      { eq = eq
      ; f-tri = f-tri
      }
      where

      e' : A -> (fiber (app∙ g∙) ★P)
      e' xp-path = (cong fst xp-path , ans)
        where
        ★P-pathp : PathP (\i -> P (fst (xp-path i))) ★P ★P
        ★P-pathp = cong snd xp-path
        t-fill : PathP (\i -> P (fst (xp-path (~ i))))
          (transport (\i -> P (fst (xp-path i))) ★P) ★P
        t-fill = symP (transport-filler (\i -> P (fst (xp-path i))) ★P)

        ans : app∙ g∙ (cong fst xp-path) == ★P
        ans = transP-sym t-fill ★P-pathp

      ★e' : e' refl == (refl , (transportRefl ★P))
      ★e' k = refl , (transP-sides->∙∙ (transportRefl ★P) refl refl >=>
                      compPath-refl-right _) k

      e : Ω (Σ X P , (★X , ★P)) ->∙
          ((Σ[ xp ∈ (★X == ★X) ] (transport (\i -> P (xp i)) ★P == ★P)) ,
           (refl , (transportRefl ★P)))
      e = ->∙-cons e' ★e'

      isEquiv-e' : isEquiv e'
      isEquiv-e' = isoToIsEquiv (iso e' back fb bf)
        where
        back : (fiber (app∙ g∙) ★P) -> A
        back (x-path , p-path) = \i -> (x-path i , p-pathp i)
          where
          p-pathp : PathP (\i -> P (x-path i)) ★P ★P
          p-pathp = transP-left (transport-filler (\i -> P (x-path i)) ★P) p-path

        fb : ∀ x -> e' (back x) == x
        fb (x-path , p-path) = \k -> x-path , p-path² k
          where
          t-fill = (transport-filler (\i -> P (x-path i)) ★P)

          p-path² : transP-sym (symP t-fill) (transP-left t-fill p-path) == p-path
          p-path² =
            (\k -> transP-sym (symP (\i -> t-fill (i ∨ k))) (transP-left (\i -> t-fill (i ∨ k)) p-path)) >=>
            transP-sides->∙∙ refl refl (transP-left refl p-path) >=>
            compPath-refl-left (transP-left refl p-path) >=>
            compPath-refl-left p-path

        bf : ∀ x -> (back (e' x)) == x
        bf xp-path = \k j -> x-path j , (transP-lemma₂ t-fill p-path) k j
          where
          x-path = cong fst xp-path
          p-path = cong snd xp-path
          t-fill = (transport-filler (\i -> P (x-path i)) ★P)


      eq : A∙ ≃∙ (fiber∙ g∙)
      eq = (e' , isEquiv-e') , ★e'

      f-tri : ->∙Tri e f∙ (->∙-cons fst refl)
      f-tri = [ (\k -> ->∙-cons (f-path k) (fp-path k)) ]
        where
        f-path : app∙ f∙ == fst ∘ e'
        f-path k xp = doubleCompPath-filler refl (cong fst xp) refl (~ k)

        fp-path : Square (∙∙-refl) (reflᵉ (reflᵉ ★X) >=> reflᵉ (reflᵉ ★X))
                         (∙∙-refl) (reflᵉ (reflᵉ ★X))
        fp-path  = transP-left (\i j -> ∙∙-refl (i ∨ j))
                               (sym (compPath-refl-right _))
