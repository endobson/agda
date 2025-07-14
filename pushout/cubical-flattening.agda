{-# OPTIONS --cubical --safe --exact-split #-}

module pushout.cubical-flattening where

open import base
open import cubical renaming (glue to cglue)
open import equality-path
open import equality.square
open import equality.transport2
open import equivalence
open import functions
open import isomorphism
open import pushout
open import funext
open import univalence

{- Reimplemented following the implementation in Cubical.HITs.Pushout.Flattening. -}

module _ {ℓA : Level} {A : Type ℓA} where

  line-iso₀ : Iso A (I -> A)
  line-iso₀ = iso fwd bkw fb (\_ -> refl)
    where
    fwd : A -> I -> A
    fwd a _ = a
    bkw : (I -> A) -> A
    bkw p = p i0

    fb : ∀ p -> fwd (bkw p) == p
    fb p i j = p (i ∧ j)


module _ {ℓA ℓB ℓC ℓP : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         {f : A -> B} {g : A -> C}
         (P : Pushout f g -> Type ℓP)
         where
  private
    ℓ : Level
    ℓ = ℓ-max* 4 ℓA ℓB ℓC ℓP

    F : B -> Type ℓP
    F = P ∘ inj-l
    G : C -> Type ℓP
    G = P ∘ inj-r
    paths : ∀ a -> F (f a) == G (g a)
    paths a i = P (glue a i)

    Q : (a : A) -> Type ℓP
    Q a = (i : I) -> paths a i

    f' : Σ A Q -> Σ B F
    f' (a , p) = (f a , p i0)
    g' : Σ A Q -> Σ C G
    g' (a , p) = (g a , p i1)


    module conv (a : A) (i : I) (p : paths a i) where
      module _ (j : I) where
        base : paths a j
        base =
          transp (\k -> paths a ((i ∨ j) ∧ (~ k ∨ j))) (~ i ∨ j)
           (transp (\k -> paths a ((i ∧ j) ∨ (k ∧ (i ∨ j)))) ((i ∧ j) ∨ (~ i ∧ ~ j))
             (transp (\k -> paths a (i ∧ (~ k ∨ (i ∧ j)))) (~ i ∨ j)
               p))

        side-j0 : PartialP {a = ℓP} (~ j) (\{ (j = i0) ->
          (base == transp (\k -> paths a (~ k ∧ i)) (~ i) p) })
        side-j0 (j = i0) = \m ->
          transp (\k -> paths a ((i ∧ ~ m) ∧ ~ k)) (~ i ∨ m)
           (transp (\k -> paths a (k ∧ (i ∧ ~ m))) (~ i ∨ m)
             (transp (\k -> paths a (i ∧ ~ k)) (~ i)
               p))

        side-j1 : PartialP {a = ℓP} j (\{ (j = i1) ->
          (base == transp (\k -> paths a (k ∨ i)) i p) })
        side-j1 (j = i1) = refl

        side-i0 : PartialP {a = ℓP} (~ i) (\{ (i = i0) ->
          (base == transp (\k -> paths a (k ∧ j)) (~ j) p) })
        side-i0 (i = i0) = refl

        side-i1 : PartialP {a = ℓP} i (\{ (i = i1) ->
          (base == transp (\k -> paths a (~ k ∨ j)) j p )})
        side-i1 (i = i1) = \m ->
          transp (\k -> paths a ((~ k ∧ (j ∨ ~ m)) ∨ j)) (j ∨ m)
           (transp (\k -> paths a (j ∨ (k ∧ ~ m))) (j ∨ m)
             (transp (\k -> paths a (~ k ∨ j)) j
               p))

        ans-fill : (m : I) -> paths a j
        ans-fill =
          hfill (\m -> (\{ (j = i0) -> side-j0 1=1 m
                         ; (i = i0) -> side-i0 1=1 m
                         ; (j = i1) -> side-j1 1=1 m
                         ; (i = i1) -> side-i1 1=1 m
                         }))
            (inS base)

        ans :
          Sub (paths a j) (i ∨ ~ i ∨ j ∨ ~ j)
              (\{ (i = i0) -> transp (\k -> paths a (k ∧ j)) (~ j) p
                ; (i = i1) -> transp (\k -> paths a (~ k ∨ j)) j p
                ; (j = i0) -> transp (\k -> paths a (~ k ∧ i)) (~ i) p
                ; (j = i1) -> transp (\k -> paths a (k ∨ i)) i p
                })
        ans = inS (ans-fill i1)

        base=ans : base == outS ans
        base=ans m = ans-fill m

      base-i=p : base i == p
      base-i=p m =
        transp (\k -> paths a i) (~ i ∨ i ∨ m)
         (transp (\k -> paths a i) (i ∨ ~ i ∨ m)
           (transp (\k -> paths a i) (~ i ∨ i ∨ m)
             p))

    bkw : (Pushout f' g') -> (Σ (Pushout f g) P)
    bkw (inj-l (b , p)) = inj-l b , p
    bkw (inj-r (c , p)) = inj-r c , p
    bkw (glue (a , p) i) = glue a i , p i


    fwd : (Σ (Pushout f g) P) -> Pushout f' g'
    fwd (inj-l b , p) = inj-l (b , p)
    fwd (inj-r c , p) = inj-r (c , p)
    fwd (glue a i , p) =
      glue (a , (\j -> outS (c.ans j))) i
      where
      module c = conv a i p

    bf : ∀ x -> bkw (fwd x) == x
    bf (inj-l b , p) = refl
    bf (inj-r c , p) = refl
    bf (glue a i , p) l = (glue a i , outS sol l)
      where
      module c = conv a i p

      sol' : outS (c.ans i) == p
      sol' = sym (c.base=ans i) >=> c.base-i=p

      sol'-path₀ : PartialP {a = ℓP} (~ i)
                     \{ (i = i0) -> sol' == refl }
      sol'-path₀ (i = i0) = compPath-refl-left refl

      sol'-path₁ : PartialP {a = ℓP} i
                     \{ (i = i1) -> sol' == refl }
      sol'-path₁ (i = i1) = compPath-refl-left refl

      sol : Sub (outS (c.ans i) == p) (i ∨ ~ i)
              \{ (i = i0) -> refl
               ; (i = i1) -> refl
               }
      sol =
        inS (hcomp (\m -> \{ (i = i0) -> sol'-path₀ 1=1 m
                           ; (i = i1) -> sol'-path₁ 1=1 m
                           })
                   sol')

    fb : ∀ x -> fwd (bkw x) == x
    fb (inj-l (b , p)) = refl
    fb (inj-r (c , p)) = refl
    fb (glue (a , p) i) = outS sol'+₂ -- \l -> glue (a , (outS sol2₀ l)) i
      where

      start : (α : I) -> paths a α
      start α = p α
      down∧ : (α : I) (β : I) -> paths a β -> paths a (β ∧ α)
      down∧ α β p = transp (\k -> paths a (β ∧ (~ k ∨ α))) (~ β ∨ α) p
      down∨ : (α : I) (β : I) -> paths a (α ∨ β) -> paths a α
      down∨ α β p = transp (\k -> paths a ((α ∨ β) ∧ (~ k ∨ α))) (~ β ∨ α) p

      up∨ : (α : I) (β : I) -> paths a β -> paths a (β ∨ α)
      up∨ α β p = transp (\k -> paths a (β ∨ (k ∧ α))) (β ∨ ~ α) p
      up∧ : (α : I) (β : I) -> paths a (α ∧ β) -> paths a α
      up∧ α β p = transp (\k -> paths a ((α ∧ β) ∨ (k ∧ α))) (β ∨ ~ α) p

      down∨-up∨ : (α β : I) -> (v : paths a α) -> down∨ α β (up∨ β α v) == v
      down∨-up∨ α β v m =
        transp (\k -> paths a ((α ∨ (β ∧ ~ m)) ∧ (~ k ∨ α))) (~ β ∨ α ∨ m )
          (transp (\k -> paths a (α ∨ (k ∧ (β ∧ ~ m)))) (α ∨ ~ β ∨ m) v)


      check-p : (j : I) -> paths a j
      check-p = p
      out : (i : I) (j : I) -> paths a j
      out i = (\j -> outS (conv.ans a i (p i) j))

      module c = conv a i (p i)

      module bp (j : I) where
        base₀ : paths a j
        base₀ =
          transp (\k -> paths a ((i ∨ j) ∧ (~ k ∨ j))) (~ i ∨ j)
           (transp (\k -> paths a ((i ∧ j) ∨ (k ∧ (i ∨ j)))) ((i ∧ j) ∨ (~ i ∧ ~ j))
             (transp (\k -> paths a (i ∧ (~ k ∨ (i ∧ j)))) (~ i ∨ j)
               (p i)))

        base₁ : paths a j
        base₁ =
          transp (\k -> paths a ((i ∨ j) ∧ (~ k ∨ j))) (~ i ∨ j)
           (transp (\k -> paths a ((i ∧ j) ∨ (k ∧ (i ∨ j)))) ((i ∧ j) ∨ (~ i ∧ ~ j))
             (p (i ∧ j)))

        base₂ : paths a j
        base₂ =
          transp (\k -> paths a ((i ∨ j) ∧ (~ k ∨ j))) (~ i ∨ j)
           (p (i ∨ j))

        base₃ : paths a j
        base₃ = p j


        check-base' : c.base j == base₀
        check-base' = refl

        step₁ : base₀ == base₁
        step₁ m =
          transp (\k -> paths a ((i ∨ j) ∧ (~ k ∨ j))) (~ i ∨ j)
           (transp (\k -> paths a ((i ∧ j) ∨ (k ∧ (i ∨ j)))) ((i ∧ j) ∨ (~ i ∧ ~ j))
             (transp (\k -> paths a ((i ∧ (~ m ∨ j)) ∧ (~ k ∨ (i ∧ j)))) (~ i ∨ j ∨ m)
               (p (i ∧ (~ m ∨ j)))))

        step₂ : base₁ == base₂
        step₂ m =
          transp (\k -> paths a ((i ∨ j) ∧ (~ k ∨ j))) (~ i ∨ j)
           (transp (\k -> paths a (((i ∧ j) ∨ (m ∧ (i ∨ j))) ∨ (k ∧ (i ∨ j)))) ((i ∧ j) ∨ (~ i ∧ ~ j) ∨ m)
             (p ((i ∧ j) ∨ (m ∧ (i ∨ j)))))

        step₃ : base₂ == base₃
        step₃ m =
          transp (\k -> paths a (((i ∨ j) ∧ (~ m ∨ j)) ∧ (~ k ∨ j))) (~ i ∨ j ∨ m)
            (p ((i ∨ j) ∧ (~ m ∨ j)))

      base-path : (j : I) -> c.base j == p j
      base-path j = step₁ ∙∙ step₂ ∙∙ step₃
        where
        open bp j

      sol' : Path ((j : I) -> paths a j) (\j -> outS (c.ans j)) p
      sol' = (\l j -> c.base=ans j (~ l)) >=> (\l j -> base-path j l)





      sol'+ : Path (Pushout f' g') (glue (a , sol' i0) i) (glue (a , sol' i1) i)
      sol'+ l = glue (a , sol' l) i


      sol'-path₀ : PartialP {a = ℓ} (~ i)
        \{ (i = i0) -> sol'+ == refl}
      sol'-path₀ (i = i0) = \m l -> glue (a , ans l m) i0
        where

        check-sol2 : sol' == (\l j -> base-path j l)
        check-sol2 =
          compPath-refl-left (\l j -> base-path j l)


        check-sol2' : Square sol' (\l j -> base-path j l) (reflᵉ (\j -> (outS (c.ans j)))) (reflᵉ p)
        check-sol2' =
          compPath-refl-left (\l j -> base-path j l)


        check-base : c.base == (\j -> transp (λ k → paths a ((k ∧ j))) (~ j) (p i0))
        check-base = refl

        check-sol' : (\j -> outS (c.ans j)) == p
        check-sol' l = sol' l

        base=p : (j : I) -> Path (paths a j) (c.base j) (p j)
        base=p j m =
          transp (λ k → paths a ((m ∧ j) ∨ (k ∧ j))) (~ j ∨ m) (p (m ∧ j))

        base=p' : Path ((j : I) -> paths a j) c.base p
        base=p' m j =
          transp (λ k → paths a ((m ∧ j) ∨ (k ∧ j))) (~ j ∨ m) (p (m ∧ j))


        simplify-base-path : (j : I) -> base-path j == base=p j
        simplify-base-path j =
          sym (doubleCompPath-filler refl (base=p j) refl)

        simplify-base-path' : base-path == base=p
        simplify-base-path' m j =
          sym (doubleCompPath-filler refl (base=p j) refl) m

        simplify-base-path'2 : (\l j -> base-path j l) == base=p'
        simplify-base-path'2 m l j =
          sym (doubleCompPath-filler refl (base=p j) refl) m l

        bp-square : Square (\l j -> base-path j l) base=p' refl refl
        bp-square m l j =
          sym (doubleCompPath-filler refl (base=p j) refl) m l

        square3 : Square sol' base=p' refl refl
        square3 = check-sol2' >=> bp-square

        square4 : Square (sym sol') (sym base=p') refl refl
        square4 i j = square3 i (~ j)

        square6 : Square refl (sym sol') refl (sym base=p')
        square6 = rotate-square-ABCR->CARB square4

        square7 : Square refl base=p' refl sol'
        square7 = rotate-square-ABCR->RBCA square3

        square8 : Square base=p' refl sol' refl
        square8 i j = square6 (~ j) (~ i)


        check-sol3 : ∀ l -> sol' l == (\j -> base=p j l)
        check-sol3 l =
          (\k -> check-sol2 k l) >=>
          (\k j -> simplify-base-path' k j l)

        check-sol4 : ∀ l -> sol' l == p
        check-sol4 l =
          (\k -> check-sol2 k l) >=>
          (\k j -> simplify-base-path' k j l) >=>
          (\k j -> base=p j (l ∨ k))

        ans-sq : Square base=p' (reflᵉ p) sol' (reflᵉ p)
        ans-sq = square8

        ans : PathP (\l -> sol' l == p) base=p' refl
        ans = ans-sq -- check-sol4


      sol'-path₁ : PartialP {a = ℓ} i
        \{ (i = i1) -> sol'+ == refl}
      sol'-path₁ (i = i1) = \m l -> glue (a , ans l m) i1

        where
        ans-side₁ : Path ((j : I) -> paths a j) (sol' i0) p
        ans-side₁ m j = transp (\k -> paths a ((~ m ∨ j) ∧ (~ k ∨ j))) (j ∨ m) (p (i1 ∧ (~ m ∨ j)))

        check-sol : sol' == (\l j -> c.base=ans j (~ l)) >=> (\l j -> base-path j l)
        check-sol = refl



        -- check-ba : ∀ l -> PathP (\j -> c.base j == outS (c.ans j)) (c.base=ans i0) (c.base=ans i1)
        type-ba : PathP (\l -> PathP (\j -> (paths a j)) (c.base=ans i0 (~ l)) (c.base=ans i1 (~ l)))
                          (\j -> outS (c.ans j))
                          (\j -> c.base j)
        type-ba = (\l j -> c.base=ans j (~ l))

        check-ba : ∀ j l -> c.base=ans j l ==
          transp (\k -> paths a ((~ k ∧ (j ∨ ~ l)) ∨ j)) (j ∨ l)
           (transp (\k -> paths a (j ∨ (k ∧ ~ l))) (j ∨ l)
             (transp (\k -> paths a (~ k ∨ j)) j
               (p i1)))
        check-ba _ _ = refl

        check-ba' : ∀ j -> c.base=ans j ==
          (down∨-up∨ j i1 (transp (\k -> paths a (~ k ∨ j)) j (p i1)))
        check-ba' _ = refl


        check-bp : ∀ j l -> base-path j l == (bp.step₁ j ∙∙ bp.step₂ j ∙∙ bp.step₃ j) l
        check-bp j l = refl

        stage₀ : Path ((j : I) -> paths a j) (\j -> outS (c.ans j)) p
        stage₀ = (\l j -> transp (\k -> paths a ((~ k ∧ (j ∨ l)) ∨ j)) (j ∨ (~ l))
                            (transp (\k -> paths a (j ∨ (k ∧ l))) (j ∨ (~ l))
                              (transp (\k -> paths a (~ k ∨ j)) j
                                (p i1)))) >=>
                 (\l j -> (bp.step₁ j ∙∙ bp.step₂ j ∙∙ bp.step₃ j) l)

        section₁ : ∀ l j ->
          c.base=ans j (~ l) ==
          (transp (\k -> paths a (~ k ∨ j)) j (p i1))
        section₁ l j m = c.base=ans j (~ l ∨ m)

        section₂-1 : ∀ j ->
          (bp.step₁ j ∙∙ bp.step₂ j ∙∙ bp.step₃ j) ==
          ((bp.step₁ j >=> bp.step₂ j) ∙∙ refl ∙∙ bp.step₃ j)
        section₂-1 j =
          (\l -> compPath-refl-right (bp.step₁ j) (~ l) ∙∙ bp.step₂ j ∙∙ bp.step₃ j) >=>
          (\l -> (bp.step₁ j ∙∙ refl ∙∙ (\k -> bp.step₂ j (k ∧ l))) ∙∙ (\k -> bp.step₂ j (k ∨ l)) ∙∙ bp.step₃ j)

        module _ (j : I) where
          raw-step₁ : (down∨ j i1 (start i1)) == (start j)
          raw-step₁ l = transp (\k -> paths a ((~ l ∨ j) ∧ (~ k ∨ j))) (j ∨ l) (p (~ l ∨ j))
          raw-step₂ : (up∨ i1 j (start j)) == (start i1)
          raw-step₂ l = transp (\k -> paths a ((j ∨ l) ∨ k)) (j ∨ l) (p (l ∨ j))

          check-step₁ :
            Path (Path (paths a j) (down∨ j i1 (up∨ i1 j (down∨ j i1 (start i1))))
                                   (down∨ j i1 (up∨ i1 j (start j))))
            (bp.step₁ j)
            (\l -> down∨ j i1 (up∨ i1 j (raw-step₁ l)))
          check-step₁ = refl

          convert-step₁ :
            PathP (\m -> Path (paths a j)
                           (c.base=ans j m)
                           (down∨-up∨ j i1 (start j) m))
            (bp.step₁ j)
            (\l -> raw-step₁ l)
          convert-step₁ m = (\l -> down∨-up∨ j i1 (raw-step₁ l) m)

          sq-step₁ : Square (bp.step₁ j) raw-step₁ (c.base=ans j) (down∨-up∨ j i1 (start j))
          sq-step₁ = convert-step₁


          check-step₂ :
            Path (Path (paths a j) (down∨ j i1 (up∨ i1 j (start j)))
                                   (down∨ j i1 (start i1)))
            (bp.step₂ j)
            (\l -> (down∨ j i1 (raw-step₂ l)))
          check-step₂ = refl

          sq-step₂ : Square (bp.step₂ j) (sym raw-step₁)
                            (down∨-up∨ j i1 (start j)) (reflᵉ (down∨ j i1 (start i1)))
          sq-step₂ l m =
            transp (\k -> paths a ((j ∨ ~ l ∨ m) ∧ (~ k ∨ j))) (j ∨ (l ∧ ~ m))
             (transp (\k -> paths a ((j ∨ m) ∨ (k ∧ (~ l ∨ m)))) (j ∨ m ∨ l)
               (start (j ∨ m)))


          section₂-ans-sq' : Square (bp.step₁ j >=> bp.step₂ j) (raw-step₁ >=> sym raw-step₁) (c.base=ans j)
                                    (reflᵉ (outS (c.ans j)))
          section₂-ans-sq' = sq-step₁ ▪v (\_ -> refl) ▪v sq-step₂

          section₂-ans-sq : Square (bp.step₁ j >=> bp.step₂ j) refl (c.base=ans j)
                              (reflᵉ (outS (c.ans j)))
          section₂-ans-sq = transP-left section₂-ans-sq' (compPath-sym raw-step₁)




        section₂-2 : ∀ j -> PathP (\m -> c.base=ans j m == c.base=ans j i1) (bp.step₁ j >=> bp.step₂ j) refl
        section₂-2 j = section₂-ans-sq j

        section₂ : ∀ j -> PathP (\m -> c.base=ans j m == p j)
          (bp.step₁ j ∙∙ bp.step₂ j ∙∙ bp.step₃ j)
          (refl ∙∙ refl ∙∙ bp.step₃ j)
        section₂ j = transP-right (section₂-1 j) (\l -> section₂-2 j l >=> bp.step₃ j)



        -- section₂' : ∀ j -> -- PathP (\m -> c.base=ans j m == p j)
        --   (bp.step₁ j ∙∙ bp.step₂ j ∙∙ bp.step₃ j)
        --   ==
        --   _ -- (refl ∙∙ refl ∙∙ bp.step₃ j)
        -- section₂' j m =
        --   (\l ->
        --     transp (\k -> paths a ((j ∨ ~ m) ∧ (~ k ∨ j))) (j)
        --      (transp (\k -> paths a (j ∨ (k ∧ ~ m))) (j)
        --        (transp (\k -> paths a ((~ l ∨ j) ∧ (~ k ∨ j))) (j ∨ l)
        --          (p (~ l ∨ j)))))
        --   ∙∙
        --   ?
        --   ∙∙
        --   ?




        stage₁ : Path ((j : I) -> paths a j) (\j -> outS (c.ans j)) p
        stage₁ = (\l j -> (transp (\k -> paths a (~ k ∨ j)) j (p i1))) >=>
                 (\l j -> (refl ∙∙ refl ∙∙ bp.step₃ j) l)

        stage₂ : Path ((j : I) -> paths a j) (\j -> outS (c.ans j)) p
        stage₂ = (\l j -> (transp (\k -> paths a (~ k ∨ j)) j (p i1))) >=>
                 (\l j -> bp.step₃ j l)

        stage₃ : Path ((j : I) -> paths a j) (\j -> outS (c.ans j)) p
        stage₃ = (\l j -> bp.step₃ j l)



        step₀ : sol' == stage₀
        step₀ = refl

        step₁ : stage₀ == stage₁
        step₁ m = (\l j -> section₁ l j m) >=>
                  (\l j -> section₂ j m l)

        step₂ : stage₁ == stage₂
        step₂ m =
          (\l j -> (transp (\k -> paths a (~ k ∨ j)) j (p i1))) >=>
          (\l j -> (compPath-refl-left (bp.step₃ j) m) l)

        step₃ : stage₂ == stage₃
        step₃ = compPath-refl-left (\l j -> bp.step₃ j l)

        step₄ : stage₃ == ans-side₁
        step₄ = refl


        all-steps : sol' == ans-side₁
        all-steps = step₁ ∙∙ step₂ ∙∙ step₃

        square1 : Square sol' ans-side₁ refl refl
        square1 = all-steps

        square2 : Square (sym sol') (sym ans-side₁) refl refl
        square2 i j = square1 i (~ j)

        square3 : Square refl (sym sol') refl (sym ans-side₁)
        square3 = rotate-square-ABCR->CARB square2

        square4 : Square ans-side₁ refl sol' refl
        square4 i j = square3 (~ j) (~ i)


        ans-sq : Square ans-side₁ (reflᵉ p) sol' (reflᵉ p)
        ans-sq = square4

        ans : PathP (\l -> sol' l == p) ans-side₁ refl
        ans = ans-sq






      sol'+₂ : Sub (Path (Pushout f' g') (glue (a , sol' i0) i) (glue (a , sol' i1) i))
                   (i ∨ ~ i)
                   (\{ (i = i0) -> refl
                     ; (i = i1) -> refl
                     })
      sol'+₂ =
        inS (hcomp (\k -> \{ (i = i0) -> sol'-path₀ 1=1 k
                           ; (i = i1) -> sol'-path₁ 1=1 k
                           })
                   sol'+)


  ΣPushout-iso : Iso (Σ (Pushout f g) P) (Pushout f' g')
  ΣPushout-iso = iso fwd bkw fb bf





module _ {ℓA ℓB ℓC ℓP : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
         (f : A -> B) (g : A -> C)
         (F : B -> Type ℓP) (G : C -> Type ℓP) (eq : ∀ a -> F (f a) ≃ G (g a))
         where

  private
    P : Pushout f g -> Type ℓP
    P = Pushout-rec F G (\a -> ua (eq a))

    f' : Σ[ a ∈ A ] ((i : I) -> (ua (eq a) i)) -> Σ B F
    f' (a , p) = (f a , p i0)
    g' : Σ[ a ∈ A ] ((i : I) -> (ua (eq a) i)) -> Σ C G
    g' (a , p) = (g a , p i1)


  ΣPushout-iso' : Iso (Σ (Pushout f g) P) (Pushout f' g')
  ΣPushout-iso' = ΣPushout-iso P
