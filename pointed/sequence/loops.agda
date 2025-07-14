{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.sequence.loops where

open import base
open import cubical
open import nat
open import equality-path
open import functions
open import functions.embedding
open import hlevel.base
open import equivalence
open import equality.square
open import isomorphism
open import type-algebra
open import pointed.base
open import pointed.loop-space.embedding
open import univalence
open import equivalence.base
open import pointed.function
open import pointed.sequence
open import pointed.sequence.equivalence
open import pointed.loop-space
open import equality.null-homotopic


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


-- module _ {ℓA1 ℓA2 : Level} {A1 : Type ℓA1} {A2 : Type ℓA2} (f : A1 -> A2) where
--   private
--     module _ {w x y z : A1} (p₁ : w == x) (p₂ : x == y) (p₃ : y == z) where
--       step₁ : Square (cong f (p₁ ∙∙ p₂ ∙∙ p₃)) (cong f p₂) (cong f p₁) (cong f (sym p₃))
--       step₁ i j = f (doubleCompPath-filler p₁ p₂ p₃ (~ i) j)
--
--       step₂ : Square (cong f p₂) (cong f p₁ ∙∙ cong f p₂ ∙∙ cong f p₃) (cong f (sym p₁)) (cong f p₃)
--       step₂ i j = doubleCompPath-filler (cong f p₁) (cong f p₂) (cong f p₃) i j
--
--   cong-∙∙ : {w x y z : A1} (p₁ : w == x) (p₂ : x == y) (p₃ : y == z) ->
--        cong f (p₁ ∙∙ p₂ ∙∙ p₃) == cong f p₁ ∙∙ cong f p₂ ∙∙ cong f p₃
--   cong-∙∙ p₁ p₂ p₃ = transP-sym (step₁ p₁ p₂ p₃) (step₂ p₁ p₂ p₃)







-- module _ {ℓ : Level} {A : Type ℓ} {a₀ b₀ a₁ b₁ : A}
--   {p₀ : a₀ == b₀}
--   {p₁ : a₁ == b₁}
--   {a : a₀ == a₁} {b : b₀ == b₁}
--   (s : Square a b p₀ p₁)
--   where
--   private
--
--
--   ▪h-symSides-filler : s ▪v (\i j -> p₁ i) ▪v (\i j -> s i (~ j)) == ?
--   ▪h-symSides-filler = ?


module _ {ℓ : Level} {A : Type ℓ} {x y : A} (p : x == y) (q : x == x) where
  -- ∙∙-sym-sides : Path (y == y) (sym p ∙∙ q ∙∙ p) refl
  -- ∙∙-sym-sides = ?

module _ {ℓ : Level} {A : Type ℓ} {a b c d : A}
  {p1 : a == b} {p2 : c == d} {p3 : a == c} {p4 : b == d}
  where

  Square->compPaths : Square p1 p2 p3 p4 -> (p1 >=> p4) == (p3 >=> p2)
  Square->compPaths s i j =
    hcomp (\k -> \{ (j = i0) -> p3 (i ∧ ~ k) -- doubleCompPath-filler p1 (reflᵉ b) p4 k j
                  ; (j = i1) -> p4 (i ∨ k) -- doubleCompPath-filler p3 (reflᵉ c) p2 k j
                  ; (i = i0) -> compPath-filler p1 p4 k j
                  ; (i = i1) -> compPath-filler' p3 p2 (~ k) j
                  })
      (s i j)


module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
  private
    module S = Short3Sequence S

  isFiberSequence-Short3->isFiberSequence-Short3' :
    isFiberSequence-Short3 S -> isFiberSequence-Short3' S
  isFiberSequence-Short3->isFiberSequence-Short3' F =
    record
      { isNull = \k -> ->∙-cons (\a -> F.isNull a k) (\j -> square k j)
      ; isEquiv-total = F.isEquiv-total
      }
    where
    module F = isFiberSequence-Short3 F

    path : (->∙-path (S.f∙ >∙> S.g∙)) == (F.isNull S.★A)
    path = sym (Square->compPaths F.isNull-Square) >=> compPath-refl-right (F.isNull S.★A)

    square' : Square refl (sym (F.isNull S.★A))
                     refl (sym (->∙-path (S.f∙ >∙> S.g∙)))
    square' = rotate-square-ABCR->RBCA (\i j -> path i (~ j))

    square : Square (->∙-path (S.f∙ >∙> S.g∙)) refl (F.isNull S.★A) refl
    square i j = square' (~ j) (~ i)


  isFiberSequence-Short3'->isFiberSequence-Short3 :
    isFiberSequence-Short3' S -> isFiberSequence-Short3 S
  isFiberSequence-Short3'->isFiberSequence-Short3 F =
    record
      { isNull = \a i -> app∙ (F.isNull i) a
      ; isNull-Square = square'
      ; isEquiv-total = F.isEquiv-total
      }
    where
    module F = isFiberSequence-Short3' F

    square : Square (->∙-path (S.f∙ >∙> S.g∙)) refl (\i -> app∙ (F.isNull i) S.★A) refl
    square i j = ->∙-path (F.isNull i) j

    path : (\i -> app∙ (F.isNull i) S.★A) == (->∙-path (S.f∙ >∙> S.g∙))
    path i j = rotate-square-ABCR->RBCA square j i
    path' : (\i -> app∙ (F.isNull i) S.★A) >=> refl == (->∙-path (S.f∙ >∙> S.g∙))
    path' = compPath-refl-right _ >=> path

    square' : _
    square' = compPaths->Square _ _ _ _ path'









-- module _ {ℓA ℓB ℓC : Level} (S : Short3Sequence ℓA ℓB ℓC) where
--   private
--     module S = Short3Sequence S
--
--   Ωf-Short3Sequence : Short3Sequence ℓA ℓB ℓC
--   Ωf-Short3Sequence = record
--     { A∙ = Ω S.A∙
--     ; B∙ = Ω S.B∙
--     ; C∙ = Ω S.C∙
--     ; f∙ = Ωf S.f∙
--     ; g∙ = Ωf S.g∙
--     }


module _ {ℓA ℓB ℓC : Level} ((S , F) : Σ (Short3Sequence ℓA ℓB ℓC) isFiberSequence-Short3') (magic : Magic) where
  private
    module S = Short3Sequence S
    module F = isFiberSequence-Short3' F
    module G = isFiberSequence-Short3 (isFiberSequence-Short3'->isFiberSequence-Short3 S F)

  Ωf-Short3FiberSequence' : Σ (Short3Sequence ℓA ℓB ℓC) isFiberSequence-Short3'
  Ωf-Short3FiberSequence' = S' , F'
    where
    S' : (Short3Sequence ℓA ℓB ℓC)
    S' = Ωf-Short3Sequence S
    module S' = Short3Sequence S'


    null-path : Ωf S.f∙ >∙> Ωf S.g∙ == const->∙
    null-path = sym (Ωf->∙> S.f∙ S.g∙) ∙∙ cong Ωf F.isNull ∙∙ Ωf-const

    null-path' : (ap : S'.A) -> isNull¹ (sym S.gp ∙∙ cong S.g (sym S.fp ∙∙ cong S.f ap ∙∙ S.fp) ∙∙ S.gp)
    null-path' ap i = app∙ (null-path i) ap

    total' : S'.A -> fiber (S'.g) S'.★C
    total' ap = S'.f ap , (null-path' ap)

    totalⁱ : S.A -> fiber (S.g) S.★C
    totalⁱ a = S.f a , (\i -> app∙ (F.isNull i) a)

    totalⁱ-path : totalⁱ S.★A == (S.★B , S.gp)
    totalⁱ-path = \j -> S.fp j , pathp j
      where
      transp-Fnull : PathP (\i -> (cong S.g S.fp >=> refl) i == S.★C) (\j -> app∙ (F.isNull j) S.★A) S.gp
      transp-Fnull =
        transport (\k -> PathP (\i -> (cong S.g S.fp >=> (\i -> S.gp (i ∧ ~ k))) i == S.★C)
                               (\j -> app∙ (F.isNull j) S.★A)
                               (\j -> S.gp (j ∨ ~ k)))
          (\i j -> ->∙-path (F.isNull j) i)

      pathp : PathP (\j -> S.g (S.fp j) == S.★C) (\i -> app∙ (F.isNull i) S.★A) S.gp
      pathp = ▪ᵀ (transP-right (sym (compPath-refl-right _)) (▪ᵀ transp-Fnull))


    totalⁱ∙ : S.A∙ ->∙ fiber∙ S.g∙
    totalⁱ∙ = ->∙-cons totalⁱ totalⁱ-path


    Ωtotalⁱ∙ : S'.A∙ ->∙ Ω (fiber∙ S.g∙)
    Ωtotalⁱ∙ = Ωf totalⁱ∙

    Ωfib-eq∙ : fiber∙ (Ωf S.g∙) ≃∙ Ω (fiber∙ S.g∙)
    Ωfib-eq∙ = fiber∙-Ωf-eq∙ S.g∙

    Ωfib-eq∙-fun-check : Σ[ bp ∈ ⟨ Ω S.B∙ ⟩ ] (sym S.gp ∙∙ cong S.g bp ∙∙ S.gp == refl) ->
                         ((S.★B , S.gp) == (S.★B , S.gp))
    Ωfib-eq∙-fun-check = eqFun ⟨ Ωfib-eq∙ ⟩

    total'-path : eqFun (fst Ωfib-eq∙) ∘ total' == (app∙ Ωtotalⁱ∙)
    total'-path = magic
      where
      right : (app∙ Ωtotalⁱ∙) ==
              (\ap -> sym totalⁱ-path ∙∙
                      cong totalⁱ ap ∙∙
                      totalⁱ-path)
      right = refl

      right₁ : Path ((S.★A == S.★A) -> S.★B == S.★B) -- ((S.★B , S.gp) == (S.★B , S.gp)))
               (\ap -> cong fst (app∙ Ωtotalⁱ∙ ap))
               (\ap -> (sym S.fp ∙∙ (cong S.f ap) ∙∙ S.fp))
      right₁ k ap = cong-∙∙ fst (sym totalⁱ-path) (cong totalⁱ ap) totalⁱ-path k



    total'-pathp : PathP (\i -> S'.A -> ua (fst Ωfib-eq∙) i) total' (app∙ Ωtotalⁱ∙)
    total'-pathp = transP-left (\i a -> (ua-filler (fst Ωfib-eq∙) (total' a)) i)
                               total'-path


    fib-totalⁱ : (x : fiber (S.g) S.★C) -> isContr (fiber totalⁱ x)
    fib-totalⁱ = isEquiv.equiv-proof F.isEquiv-total

    isEmb-totalⁱ : isEmbedding totalⁱ
    isEmb-totalⁱ = isEquiv->isEmbedding F.isEquiv-total


    fib-Ωtotalⁱ : (x : ⟨ Ω (fiber∙ S.g∙) ⟩) -> isContr (fiber (app∙ (Ωf totalⁱ∙)) x)
    fib-Ωtotalⁱ x =
      isEquiv.equiv-proof (isEmbedding->isEquiv-Ωf totalⁱ∙ isEmb-totalⁱ) x

    fib-total' : (x : ⟨ fiber∙ (Ωf S.g∙) ⟩) -> isContr (fiber total' x)
    fib-total' =
      transport (\i -> (x : (ua (fst Ωfib-eq∙) (~ i))) ->
                       isContr (fiber (total'-pathp (~ i)) x))
        fib-Ωtotalⁱ


    isEquiv-total' : isEquiv total'
    isEquiv-total' .isEquiv.equiv-proof = fib-total'


    F' : isFiberSequence-Short3' S'
    F' = record
      { isNull = null-path
      ; isEquiv-total = isEquiv-total'
      }




module _ {ℓ : Level} (X∙@(X , ★X) : Type∙ ℓ) (P : X -> Type ℓ) (★P : P ★X) where
  private
    Ty∙ : ℕ -> Type∙ ℓ
    Ty∙ zero = X∙
    Ty∙ (suc zero) = Σ∙ X∙ P ★P
    Ty∙ (suc (suc zero)) = P ★X , ★P
    Ty∙ (suc (suc (suc n))) = Ω (Ty∙ n)

    f∙ : (n : ℕ) -> Ty∙ (suc n) ->∙ Ty∙ n
    f∙ zero = ->∙-cons fst refl
    f∙ (suc zero) = ->∙-cons (\x -> ★X , x) refl
    f∙ (suc (suc zero)) =
      ->∙-cons
        (\p -> (transport (\i -> P (p i)) ★P))
        (transportRefl ★P)
    f∙ (suc (suc (suc n))) = Ωf (f∙ n)

    Seq : ℕ⁻-Sequence ℓ
    Seq = record
      { Ty∙ = Ty∙
      ; f∙ = f∙
      }

    isFiber₀ : isFiberSequence-Short3 (ℕ⁻-Sequence.short3 Seq 0)
    isFiber₀ = snd (fibration->ShortFiberSequence X∙ P ★P)

    isFiber₁ : isFiberSequence-Short3 (ℕ⁻-Sequence.short3 Seq 1)
    isFiber₁ = record
      { isNull = isNull
      ; isNull-Square = isNull-Square
      ; isEquiv-total = isEquiv-total
      }
      where
      isNull : ∀ p -> app∙ (f∙ 1) (app∙ (f∙ 2) p) == (★X , ★P)
      isNull p i = p (~ i) , (transp (\j -> P (p (j ∧ ~ i))) i ★P)

      isNull-Square : Square
        (\j -> ★X , (transp (\k -> P ★X) j ★P))
        (\j -> ★X , ★P)
        (\i -> ★X , (transportRefl ★P i))
        (\i -> ★X , ★P)
      isNull-Square i j = ★X , (transp (\k -> P ★X) (j ∨ i) ★P)

      total' : ⟨ Ty∙ 3 ⟩ -> fiber (app∙ (f∙ 1)) (★X , ★P)
      total' p = transport (\i -> P (p i)) ★P , isNull p


      isEquiv-total : isEquiv total'
      isEquiv-total = snd (isoToEquiv (iso total' inv fb bf))
        where
        inv : fiber (app∙ (f∙ 1)) (★X , ★P) -> ⟨ Ty∙ 3 ⟩
        inv (b , p) = cong fst (sym p)
          where
          type-b : P ★X
          type-b = b
          type-p : (★X , b) == (★X , ★P)
          type-p = p
          type-p₁ : ★X == ★X
          type-p₁ = cong fst p
          type-p₂ : PathP (\i -> P (fst (p i))) b ★P
          type-p₂ = cong snd p

        bf : ∀ x -> inv (total' x) == x
        bf _ = refl

        fb : ∀ y -> total' (inv y) == y
        fb y@(b , p) = fb-y-path
          where
          type-fbx : fiber (app∙ (f∙ 1)) (★X , ★P)
          type-fbx = total' (inv y)
          type-y : Σ[ b ∈ P ★X ] ((★X , b) == (★X , ★P))
          type-y = y

          fb-y₁-path₁ : PathP (\i -> P (fst (p i))) (fst (total' (inv y))) ★P
          fb-y₁-path₁ = symP (transport-filler (\i -> P (fst (p (~ i)))) ★P)

          fb-y₂-path₁ : PathP (\i -> ((fst (p i)) , (fb-y₁-path₁ i)) == (★X , ★P))
                              (isNull (inv y))
                              (reflᵉ (★X , ★P))
          fb-y₂-path₁ = ans
            where
            path₁ : (b : X) (q : b == ★X) ->
                    PathP (\i -> P (q i)) (transport (\i -> P (q (~ i))) ★P) ★P
            path₁ b q = symP (transport-filler (\i -> P (q (~ i))) ★P)

            isNull' : ∀ {b : X} (p : ★X == b) -> Path (Σ X P) (b , transport (\i -> P (p i)) ★P) (★X , ★P)
            isNull' {b} p i = p (~ i) , (transp (\j -> P (p (j ∧ ~ i))) i ★P)

            Q : (b : X) (q : b == ★X) -> Type ℓ
            Q b q = PathP (\i -> (q i , path₁ b q i) == (★X , ★P))
                          (isNull' (sym q))
                          (reflᵉ (★X , ★P))
            Q' : (b : X) (q : ★X == b) -> Type ℓ
            Q' b q = Q b (sym q)

            Q-refl : Q ★X refl
            Q-refl = isNull-Square

            ans : Q ★X (cong fst p)
            ans = J Q' Q-refl (sym (cong fst p))


          fb-y-path₁ : PathP (\i -> Σ[ v ∈ P (fst (p i)) ] (Path (Σ X P) (fst (p i) , v) (★X , ★P)))
                             (total' (inv y))
                             (★P , reflᵉ (★X , ★P))
          fb-y-path₁ i = fb-y₁-path₁ i , fb-y₂-path₁ i

          fb-y-path₂ : PathP (\i -> Σ[ v ∈ P (fst (p (~ i))) ] (Path (Σ X P) (fst (p (~ i)) , v) (★X , ★P)))
                             (★P , reflᵉ (★X , ★P))
                             (b , p)
          fb-y-path₂ i = snd (p (~ i)) , (\j -> fst (p (j ∨ ~ i)) , snd (p (j ∨ ~ i)))

          fb-y-path : Path (Σ[ v ∈ P ★X ] (Path (Σ X P) (★X , v) (★X , ★P)))
                           (total' (inv y))
                           (b , p)
          fb-y-path = transP-sym fb-y-path₁ fb-y-path₂


    isFiber₂-eq : isFiberSequence-Short3-eq (ℕ⁻-Sequence.short3 Seq 2)
    isFiber₂-eq = record
      { eq = eq
      ; f-tri = f-tri
      }
      where
      A∙ B∙ C∙ : Type∙ ℓ
      A∙ = Ω (Σ∙ X∙ P ★P)
      B∙ = Ω X∙
      C∙ = P ★X , ★P

      A B C : Type ℓ
      A = ⟨ A∙ ⟩
      B = ⟨ B∙ ⟩
      C = ⟨ C∙ ⟩

      f∙' : A∙ ->∙ B∙
      f∙' = Ωf (->∙-cons fst refl)
      g∙ : B∙ ->∙ C∙
      g∙ = ->∙-cons (\p -> transport (\i -> (P (p i))) ★P) (transportRefl ★P)

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

      f-tri : ->∙Tri e f∙' (->∙-cons fst refl)
      f-tri = [ (\k -> ->∙-cons (f-path k) (fp-path k)) ]
        where
        f-path : app∙ f∙' == fst ∘ e'
        f-path k xp = doubleCompPath-filler refl (cong fst xp) refl (~ k)

        fp-path : Square (∙∙-refl) (reflᵉ (reflᵉ ★X) >=> reflᵉ (reflᵉ ★X))
                         (∙∙-refl) (reflᵉ (reflᵉ ★X))
        fp-path  = transP-left (\i j -> ∙∙-refl (i ∨ j))
                               (sym (compPath-refl-right _))

    isFiber₂ : isFiberSequence-Short3 (ℕ⁻-Sequence.short3 Seq 2)
    isFiber₂ = eq->main _ isFiber₂-eq

    isFiber₃ : (n : Nat) ->
               isFiberSequence-Short3 (ℕ⁻-Sequence.short3 Seq n) ->
               isFiberSequence-Short3 (ℕ⁻-Sequence.short3 Seq (suc (suc (suc n))))
    isFiber₃ n F = Ωf-Short3FiberSequence F


    isFiber-Short3 : (n : Nat) -> isFiberSequence-Short3 (ℕ⁻-Sequence.short3 Seq n)
    isFiber-Short3 0 = isFiber₀
    isFiber-Short3 1 = isFiber₁
    isFiber-Short3 2 = isFiber₂
    isFiber-Short3 (suc (suc (suc n))) =
      isFiber₃ n (isFiber-Short3 n)


    isFiber : isFiberSequence-ℕ⁻ Seq
    isFiber = record { isFiberSeq-short3 = isFiber-Short3 }


  puppe-sequence : Σ (ℕ⁻-Sequence ℓ) isFiberSequence-ℕ⁻
  puppe-sequence = Seq , isFiber
