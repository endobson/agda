{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.loop-space where

open import base
open import equality-path
open import equality.null-homotopic
open import equality.square
open import equivalence
open import nat
open import funext
open import hlevel
open import functions
open import isomorphism
open import cubical
open import nat.iteration
open import pointed.base
open import pointed.function

Ω : {ℓ : Level} -> Type∙ ℓ -> Type∙ ℓ
Ω (A , ★A) = (★A == ★A) , refl

Ωⁿ : {ℓ : Level} -> Nat -> Type∙ ℓ -> Type∙ ℓ
Ωⁿ n = iter n Ω

Ω² : {ℓ : Level} -> Type∙ ℓ -> Type∙ ℓ
Ω² = Ωⁿ 2

Ωf : {ℓA ℓB : Level} {A∙ : Type∙ ℓA} {B∙ : Type∙ ℓB} ->
     (A∙ ->∙ B∙) -> (Ω A∙ ->∙ Ω B∙)
Ωf {A∙ = (A , ★A)} {B∙ = (B , ★B)} (->∙-cons f fp) = (->∙-cons f' fp')
  where
  f' : (★A == ★A) -> (★B == ★B)
  f' ap = sym fp ∙∙ (cong f ap) ∙∙ fp

  fp' : f' refl == refl
  fp' = compPath-sym (sym fp)

Ω-Ωⁿ-path : {ℓ : Level} {A∙ : Type∙ ℓ} (n : Nat) ->
            Ω (Ωⁿ n A∙) == (Ωⁿ n (Ω A∙))
Ω-Ωⁿ-path zero    = refl
Ω-Ωⁿ-path (suc n) = cong Ω (Ω-Ωⁿ-path n)



module _ {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB} where
  Ωf-const : Path (Ω A∙ ->∙ Ω B∙) (Ωf const->∙) const->∙
  Ωf-const = \k -> ->∙-cons (\p -> ∙∙-refl k) (\i -> ∙∙-refl (k ∨ i))


module _ {ℓA ℓB : Level}
         {A∙@(A , ★A) : Type∙ ℓA}
         {B∙@(B , ★B) : Type∙ ℓB}
         (f∙@(->∙-cons f fp) : A∙ ->∙ B∙)
         where
  Ωf-∙∙ : ∀ (x y z : ⟨ Ω A∙ ⟩) ->
    app∙ (Ωf f∙) (x ∙∙ y ∙∙ z) ==
    app∙ (Ωf f∙) x ∙∙ app∙ (Ωf f∙) y ∙∙ app∙ (Ωf f∙) z
  Ωf-∙∙ x y z = step₁ ∙∙ step₂ ∙∙ ∙∙-refl-sides _
    where
    step₁ :
      app∙ (Ωf f∙) (x ∙∙ y ∙∙ z) ==
      (sym fp ∙∙
       ((refl ∙∙ cong f x ∙∙ refl) ∙∙
        (refl ∙∙ cong f y ∙∙ refl) ∙∙
        (refl ∙∙ cong f z ∙∙ refl)) ∙∙
       fp)
    step₁ =
      cong (sym fp ∙∙_∙∙ fp)
        (cong-∙∙ f x y z >=>
         (\i -> (∙∙-refl-sides (cong f x) (~ i)) ∙∙
                (∙∙-refl-sides (cong f y) (~ i)) ∙∙
                (∙∙-refl-sides (cong f z) (~ i))))

    step₂ :
      (sym fp ∙∙
       ((refl ∙∙ cong f x ∙∙ refl) ∙∙
        (refl ∙∙ cong f y ∙∙ refl) ∙∙
        (refl ∙∙ cong f z ∙∙ refl)) ∙∙
       fp) ==
      (refl ∙∙
       ((sym fp ∙∙ cong f x ∙∙ fp) ∙∙
        (sym fp ∙∙ cong f y ∙∙ fp) ∙∙
        (sym fp ∙∙ cong f z ∙∙ fp)) ∙∙
       refl)
    step₂ k =
      ((\i -> fp (~ i ∨ k)) ∙∙
       (((\i -> fp (~ i ∧ k)) ∙∙ cong f x ∙∙ (\i -> fp (i ∧ k))) ∙∙
        ((\i -> fp (~ i ∧ k)) ∙∙ cong f y ∙∙ (\i -> fp (i ∧ k))) ∙∙
        ((\i -> fp (~ i ∧ k)) ∙∙ cong f z ∙∙ (\i -> fp (i ∧ k)))) ∙∙
       (\i -> fp (i ∨ k)))

  Ωf->=> : ∀ (x y : ⟨ Ω A∙ ⟩) ->
    app∙ (Ωf f∙) (x >=> y) ==
    app∙ (Ωf f∙) x >=> app∙ (Ωf f∙) y
  Ωf->=> x y =
    Ωf-∙∙ x refl y >=>
    cong ((app∙ (Ωf f∙) x) ∙∙_∙∙ (app∙ (Ωf f∙) y))
         (->∙-path (Ωf f∙))




module _ {ℓA ℓB : Level} {A∙@(A , ★A) : Type∙ ℓA} {B∙@(B , ★B) : Type∙ ℓB} where
  fiber∙-Ωf-eq∙ : (f : A∙ ->∙ B∙) -> fiber∙ (Ωf f) ≃∙ Ω (fiber∙ f)
  fiber∙-Ωf-eq∙ f∙@(->∙-cons f fp) = isoToEquiv (iso for back fb bf) , for∙
    where

    module _ (ap : ★A == ★A) where
      square-path₁ :
        (app∙ (Ωf f∙) ap == refl) ==
        (Square (refl ∙∙ (cong f ap) ∙∙ refl) refl fp fp)
      square-path₁ k =
        Square (\j -> ((\i -> fp (~ i ∧ ~ k)) ∙∙ cong f ap ∙∙ (\i -> fp (i ∧ ~ k))) j)
               refl
               (\i -> fp (i ∨ ~ k))
               (\i -> fp (i ∨ ~ k))


      square-path₂ :
        (Square (refl ∙∙ (cong f ap) ∙∙ refl) refl fp fp) ==
        (Square (cong f ap) refl fp fp)
      square-path₂ k = Square (∙∙-refl-sides (cong f ap) k) refl fp fp

    for : ⟨ fiber∙ (Ωf f∙) ⟩ -> ⟨ Ω (fiber∙ f∙) ⟩
    for (ap , s) = \i -> ap i , (\j -> r j i)
      where
      r : Square (cong f ap) refl fp fp
      r = transport (square-path₁ ap >=> square-path₂ ap) s

    back : ⟨ Ω (fiber∙ f∙) ⟩ -> ⟨ fiber∙ (Ωf f∙) ⟩
    back fib-p = p , r
      where
      p : ⟨ Ω A∙ ⟩
      p = (\i -> (fst (fib-p i)))
      s' : Square (\i -> (app∙ f∙ (p i))) refl fp fp
      s' i j = (snd (fib-p j)) i

      r : (app∙ (Ωf f∙) p == refl)
      r = transport (sym (square-path₁ p >=> square-path₂ p)) s'

    bf : ∀ x -> back (for x) == x
    bf (ap , s) = \k -> ap , transport-sym sp s k
      where
      sp = (square-path₁ ap >=> square-path₂ ap)

    fb : ∀ x -> for (back x) == x
    fb fib-p = \k j -> p j , (\i -> (transport-sym (sym sp) s' k) i j)
      where
      p : ⟨ Ω A∙ ⟩
      p = (\i -> (fst (fib-p i)))
      s' : Square (\i -> (app∙ f∙ (p i))) refl fp fp
      s' i j = (snd (fib-p j)) i
      sp = (square-path₁ p >=> square-path₂ p)

    for∙ : for (snd (fiber∙ (Ωf f∙))) == reflᵉ (★A , fp)
    for∙ = \k i -> ★A , isNull¹-tp k i
      where

      tp : fp == fp
      tp = ▪ᵀ (transport (square-path₁ refl >=> square-path₂ refl) (compPath-sym (sym fp)))


      tp₁ : fp == fp
      tp₁ = ▪ᵀ (transport (square-path₂ refl) (transport (square-path₁ refl) (compPath-sym (sym fp))))

      tp₁' : (Square (refl ∙∙ reflᵉ (f ★A) ∙∙ refl) (reflᵉ ★B) fp fp)
      tp₁' = (transport (square-path₁ refl) (compPath-sym (sym fp)))

      tp₂' : (Square (refl ∙∙ reflᵉ (f ★A) ∙∙ refl) (reflᵉ ★B) fp fp)
      tp₂' i j =
        hcomp (\k -> \{ (j = i0) -> fp i
                      ; (j = i1) -> fp i
                      ; (i = i1) -> ★B
                      })
          (fp i)

      tp₂ : fp == fp
      tp₂ = ▪ᵀ (transport (square-path₂ refl) tp₂')

      tp₃ : fp == fp
      tp₃ = ▪ᵀ (\i j -> fp i)

      step-tp₃' : Path (PathP (\i -> fp i == fp i) refl refl)
                    (transport (square-path₂ refl) tp₂')
                    (\i j -> fp i)
      step-tp₃' =
        \l -> transp
               (\k -> Square (∙∙-refl-sides refl (k ∨ l)) refl fp fp)
               l
               (inner-fill l)
        where
        inner-fill :
          PathP (\k -> Square (∙∙-refl-sides refl k) refl fp fp)
                (\i j -> (tp₂' i j)) (\i j -> (fp i))
        inner-fill k i j =
          hfill (\k -> \{ (j = i0) -> fp i
                        ; (j = i1) -> fp i
                        ; (i = i1) -> ★B
                        })
                (inS (fp i)) (~ k)

      step-tp₂' : tp₁' == tp₂'
      step-tp₂' l =
        transp
         (\k ->
            Square (\j -> ((\i -> fp (~ i ∧ (~ k ∧ ~ l))) ∙∙ reflᵉ (f ★A) ∙∙ (\i -> fp (i ∧ (~ k ∧ ~ l)))) j)
                   refl
                   (\i -> fp (i ∨ (~ k ∧ ~ l)))
                   (\i -> fp (i ∨ (~ k ∧ ~ l)))
                   )
         l
         (\i j -> (hcomp (\k -> \{ (j = i0) -> fp (i ∨ (k ∧ ~ l))
                                 ; (j = i1) -> fp (i ∨ (k ∧ ~ l))
                                 ; (i = i1) -> ★B
                                 })
           (fp i)))


      isNull¹-tp : isNull¹ tp
      isNull¹-tp = subst isNull¹ (sym (step-tp₁ ∙∙ step-tp₂ ∙∙ step-tp₃)) (isNull¹-refl fp)
        where
        step-tp₁ : tp == tp₁
        step-tp₁ k = ▪ᵀ (transport-twice  (square-path₂ refl) (square-path₁ refl) (compPath-sym (sym fp)) (~ k))

        step-tp₂ : tp₁ == tp₂
        step-tp₂ k = ▪ᵀ (transport (square-path₂ refl) (step-tp₂' k))

        step-tp₃ : tp₂ == tp₃
        step-tp₃ k = ▪ᵀ (step-tp₃' k)

private
  module Ωf->∙>
    {ℓA ℓB ℓC : Level}
    {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
    (f : A -> B) (g : B -> C)
    (★A : A)
    where
    A∙ : Type∙ ℓA
    A∙ = A , ★A

    module path₁ (★B : B) (fp : f ★A == ★B) where
      B∙ : Type∙ ℓB
      B∙ = B , ★B
      f∙ = ->∙-cons f fp

      module path₂ (★C : C) (gp : g ★B == ★C) where
        C∙ : Type∙ ℓC
        C∙ = C , ★C
        g∙ = ->∙-cons g gp

        stage₀ : ⟨ Ω A∙ ⟩ -> ⟨ Ω C∙ ⟩
        stage₀ = \p -> sym (cong g fp >=> gp) ∙∙ cong (g ∘ f) p ∙∙ (cong g fp >=> gp)

        stage₁ : ⟨ Ω A∙ ⟩ -> ⟨ Ω C∙ ⟩
        stage₁ = \p -> refl ∙∙ (sym (cong g fp >=> gp) ∙∙ cong (g ∘ f) p ∙∙ (cong g fp >=> gp)) ∙∙ refl

        stage₂ : ⟨ Ω A∙ ⟩ -> ⟨ Ω C∙ ⟩
        stage₂ = \p -> sym gp ∙∙ (sym (cong g fp >=> refl) ∙∙ cong (g ∘ f) p ∙∙ (cong g fp >=> refl)) ∙∙ gp

        stage₃ : ⟨ Ω A∙ ⟩ -> ⟨ Ω C∙ ⟩
        stage₃ = \p -> sym gp ∙∙ (sym (cong g fp) ∙∙ cong (g ∘ f) p ∙∙ (cong g fp)) ∙∙ gp

        stage₄ : ⟨ Ω A∙ ⟩ -> ⟨ Ω C∙ ⟩
        stage₄ = \p -> sym gp ∙∙ (cong g ((sym fp) ∙∙ cong f p ∙∙ fp)) ∙∙ gp

        isNull¹-stage₀ : {p : ⟨ Ω A∙ ⟩} -> isNull¹ p -> isNull¹ (stage₀ p)
        isNull¹-stage₀ n = isNull¹-∙∙-sym (sym (cong g fp >=> gp)) (isNull¹-cong (g ∘ f) n)
        isNull¹-stage₁ : {p : ⟨ Ω A∙ ⟩} -> isNull¹ p -> isNull¹ (stage₁ p)
        isNull¹-stage₁ n = isNull¹-∙∙-sym refl (isNull¹-∙∙-sym (sym (cong g fp >=> gp)) (isNull¹-cong (g ∘ f) n))
        isNull¹-stage₂ : {p : ⟨ Ω A∙ ⟩} -> isNull¹ p -> isNull¹ (stage₂ p)
        isNull¹-stage₂ n = isNull¹-∙∙-sym (sym gp) (isNull¹-∙∙-sym (sym (cong g fp >=> refl)) (isNull¹-cong (g ∘ f) n))
        isNull¹-stage₃ : {p : ⟨ Ω A∙ ⟩} -> isNull¹ p -> isNull¹ (stage₃ p)
        isNull¹-stage₃ n = isNull¹-∙∙-sym (sym gp) (isNull¹-∙∙-sym (sym (cong g fp)) (isNull¹-cong (g ∘ f) n))
        isNull¹-stage₄ : {p : ⟨ Ω A∙ ⟩} -> isNull¹ p -> isNull¹ (stage₄ p)
        isNull¹-stage₄ n = isNull¹-∙∙-sym (sym gp) (isNull¹-cong g (isNull¹-∙∙-sym (sym fp) (isNull¹-cong f n)))


        left : app∙ (Ωf (f∙ >∙> g∙)) == stage₀
        left = refl


        step₁ : stage₀ == stage₁
        step₁ = funExt (\p -> doubleCompPath-filler refl _ refl)
        step₂ : stage₁ == stage₂
        step₂ = funExt (\p k ->
          (\j -> gp (~ j ∨ ~ k)) ∙∙
          (sym (cong g fp >=> (\j -> gp (j ∧ ~ k))) ∙∙
           cong (g ∘ f) p ∙∙
           (cong g fp >=> (\j -> gp (j ∧ ~ k)))) ∙∙
          (\j -> gp (j ∨ ~ k)))
        step₃ : stage₂ == stage₃
        step₃ = funExt (\p k ->
          sym gp ∙∙
          (sym (compPath-refl-right (cong g fp) k) ∙∙
           cong (g ∘ f) p ∙∙
           (compPath-refl-right (cong g fp) k)) ∙∙
          gp)
        step₄ : stage₃ == stage₄
        step₄ = funExt (\p k ->
          sym gp ∙∙
          (cong-∙∙ g (sym fp) (cong f p) fp (~ k)) ∙∙
          gp)

        right : app∙ (Ωf f∙ >∙> Ωf g∙) == stage₄
        right = refl

        h : app∙ (Ωf (f∙ >∙> g∙)) == app∙ (Ωf f∙ >∙> Ωf g∙)
        h = step₁ >=> (step₂ >=> (step₃ >=> step₄))

        isNull¹-step₁ : {p : ⟨ Ω A∙ ⟩} -> (n : isNull¹ p) ->
                        PathP (\i -> isNull¹ (step₁ i p)) (isNull¹-stage₀ n) (isNull¹-stage₁ n)
        isNull¹-step₁ n k = isNull¹-∙∙-refl (isNull¹-stage₀ n) (~ k)
        isNull¹-step₂ : {p : ⟨ Ω A∙ ⟩} -> (n : isNull¹ p) ->
                        PathP (\i -> isNull¹ (step₂ i p)) (isNull¹-stage₁ n) (isNull¹-stage₂ n)
        isNull¹-step₂ n k =
          isNull¹-∙∙-sym (\j -> gp (~ j ∨ ~ k))
            (isNull¹-∙∙-sym (sym ((cong g fp) >=> (\j -> gp (j ∧ ~ k))))
                            (isNull¹-cong (g ∘ f) n))
        isNull¹-step₃ : {p : ⟨ Ω A∙ ⟩} -> (n : isNull¹ p) ->
                        PathP (\i -> isNull¹ (step₃ i p)) (isNull¹-stage₂ n) (isNull¹-stage₃ n)
        isNull¹-step₃ n k =
          isNull¹-∙∙-sym (sym gp)
            (isNull¹-∙∙-sym (sym (compPath-refl-right (cong g fp) k))
                            (isNull¹-cong (g ∘ f) n))
        isNull¹-step₄ : {p : ⟨ Ω A∙ ⟩} -> (n : isNull¹ p) ->
                        PathP (\i -> isNull¹ (step₄ i p)) (isNull¹-stage₃ n) (isNull¹-stage₄ n)
        isNull¹-step₄ n k = isNull¹-∙∙-sym (sym gp) (isNull¹-cong-∙∙-sym g (sym fp) (isNull¹-cong f n) (~ k))

        isNull¹-steps : {p : ⟨ Ω A∙ ⟩} -> (n : isNull¹ p) ->
                         PathP (\i ->
                          ((\j -> isNull¹ (step₁ j p)) >=>
                           ((\j -> isNull¹ (step₂ j p)) >=>
                            ((\j -> isNull¹ (step₃ j p)) >=>
                             (\j -> isNull¹ (step₄ j p))))) i)
                          (isNull¹-stage₀ n) (isNull¹-stage₄ n)
        isNull¹-steps n =
          transP (isNull¹-step₁ n)
            (transP (isNull¹-step₂ n)
              (transP (isNull¹-step₃ n) (isNull¹-step₄ n)))

        isNull¹-steps=h : {p : ⟨ Ω A∙ ⟩} ->
          (\j -> isNull¹ (h j p))
          ==
          ((\j -> isNull¹ (step₁ j p)) >=>
           ((\j -> isNull¹ (step₂ j p)) >=>
            ((\j -> isNull¹ (step₃ j p)) >=>
             (\j -> isNull¹ (step₄ j p)))))
        isNull¹-steps=h {p} =
          cong-trans (\f -> isNull¹ (f p)) step₁ (step₂ >=> (step₃ >=> step₄)) >=>
          (cong ((\j -> isNull¹ (step₁ j p)) >=>_)
            (cong-trans (\f -> isNull¹ (f p)) step₂ (step₃ >=> step₄) >=>
             (cong ((\j -> isNull¹ (step₂ j p)) >=>_)
               (cong-trans (\f -> isNull¹ (f p)) step₃ step₄))))

        isNull¹-h : {p : ⟨ Ω A∙ ⟩} -> (n : isNull¹ p) ->
                    PathP (\i -> isNull¹ (h i p))
                     (isNull¹-stage₀ n) (isNull¹-stage₄ n)
        isNull¹-h {p} n =
          transport
            (\k -> PathP (\i -> isNull¹-steps=h {p} (~ k) i)
                            (isNull¹-stage₀ n) (isNull¹-stage₄ n))
            (isNull¹-steps n)

        ΣisNull¹-path :
          (p : ⟨ Ω A∙ ⟩) -> (n : isNull¹ p) ->
          Path (Σ ( ⟨ Ω C∙ ⟩ ) isNull¹)
            (stage₀ p , isNull¹-stage₀ n)
            (stage₄ p , isNull¹-stage₄ n)
        ΣisNull¹-path p n i = h i p , isNull¹-h n i

        -- ΣisNull¹-path' :
        --   (p : ⟨ Ω A∙ ⟩) -> (n : isNull¹ p) ->
        --   Path (Σ ( ⟨ Ω C∙ ⟩ ) isNull¹)
        --     (stage₀ p , isNull¹-stage₀ n)
        --     (stage₄ p , isNull¹-stage₄ n)
        -- ΣisNull¹-path' p n = isContr->isProp (isContr-ΣisNull¹ ★C) _ _

        check-C : C∙ == (C , g ★B)
        check-C k = C , gp (~ k)

        P : Type ℓC
        P =
          PathP (\i -> h i (reflᵉ ★A) == (reflᵉ ★C))
                (compPath-sym (sym (cong g fp >=> gp)))
                (cong (\p -> sym gp ∙∙ cong g p ∙∙ gp)
                      (compPath-sym (sym fp)) >=>
                      (compPath-sym (sym gp)))

        ansP : P
        ansP =
          transP-left
            (transP-right
              (sym (compPath-refl-left (compPath-sym (sym (cong g fp >=> gp)))))
              (isNull¹-h (isNull¹-refl ★A)))
            (cong (\p -> cong (\p -> sym gp ∙∙ cong g p ∙∙ gp) p >=> compPath-sym (sym gp))
                  (compPath-refl-left _))

      P₁ : Type ℓC
      P₁ = ∀ (★C : C) (gp : g ★B == ★C) -> path₂.P ★C gp

    P₂ : Type (ℓ-max ℓB ℓC)
    P₂ = ∀ (★B : B) (fp : f ★A == ★B) -> path₁.P₁ ★B fp


module _ {ℓA ℓB ℓC : Level}
         {A∙@(A , ★A) : Type∙ ℓA}
         {B∙@(B , ★B) : Type∙ ℓB}
         {C∙@(C , ★C) : Type∙ ℓC}
         (f∙@(->∙-cons f fp) : A∙ ->∙ B∙)
         (g∙@(->∙-cons g gp) : B∙ ->∙ C∙)
         where

  Ωf->∙> : (Ωf (f∙ >∙> g∙)) == (Ωf f∙ >∙> Ωf g∙)
  Ωf->∙> = \k -> ->∙-cons (h k) (h' k)
    where
    open Ωf->∙>.path₁.path₂ f g ★A ★B fp ★C gp

    h' : PathP (\i -> h i (reflᵉ ★A) == (reflᵉ ★C))
               (compPath-sym (sym (cong g fp >=> gp)))
               (cong (\p -> sym gp ∙∙ cong g p ∙∙ gp)
                     (compPath-sym (sym fp)) >=>
                     (compPath-sym (sym gp)))
    h' = Ωf->∙>.path₁.path₂.ansP f g ★A ★B fp ★C gp


module _ {ℓA ℓB ℓC : Level}
         {A∙ : Type∙ ℓA}
         {B∙ : Type∙ ℓB}
         {C∙ : Type∙ ℓC}
         {e∙ : A∙ ->∙ B∙}
         {f∙ : A∙ ->∙ C∙}
         {g∙ : B∙ ->∙ C∙}
  where
  Ω->∙Tri : ->∙Tri e∙ f∙ g∙ -> ->∙Tri (Ωf e∙) (Ωf f∙) (Ωf g∙)
  Ω->∙Tri [ p ] = [ cong Ωf p >=> Ωf->∙> e∙ g∙ ]
