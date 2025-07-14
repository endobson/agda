{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.freudenthal4 where




open import base
open import pointed.base
open import cubical
open import equality-path
open import equality.square
open import equality.dependent-path
open import base
open import funext
open import functions.embedding
open import isomorphism
open import sigma
open import univalence

open import additive-group
open import order
open import functions
open import nat.order
open import order.instances.nat
open import additive-group.instances.nat
open import cubical
open import equality-path
open import equality.square
open import equality.square-compose
open import equality.square-compose2
open import equality.path-composition-equivalence
open import connected
open import hlevel.base
open import hlevel.pi
open import pointed.base
open import pointed.loop-space
open import truncation.generic
open import truncation.generic.path
open import truncation.generic.map
open import equivalence.base
open import equivalence
open import connected.wedge
open import connected.reduce

open import pointed.suspension


module _ {ℓ : Level} {A : Type ℓ} where
  transport=compPath : {a₁ a₂ a₃ : A} -> (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) ->
    transport (\i -> a₁ == p₂ i) p₁ == p₁ >=> p₂
  transport=compPath {a₁} {a₂} {a₃} p₁ p₂ i =
    transp (\j -> a₁ == p₂ (i ∨ j)) i ((compPath-filler p₁ p₂) i)



module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) where
  ΩΣf : A -> ⟨ Ω (Susp∙ A∙) ⟩
  ΩΣf a = meridian a >=> sym (meridian ★A)


module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) {n : Nat} (cA : isConnectedₙ n A) where
  private
    south-code : Path (Susp A) north south -> Type ℓ
    south-code p = Squashₙ (suc (suc (n + n))) (fiber meridian p)

    -- mid-code : A -> Path (Susp A) north south -> Type ℓ
    -- mid-code a₂ p =
    --   Squashₙ (suc (suc (n + n)))
    --     (Σ[ a₁ ∈ A ] (Square p (sym (meridian ★A)) (meridian a₁) (sym (meridian a₂))))

    north-code : Path (Susp A) north north -> Type ℓ
    north-code p = Squashₙ (suc (suc (n + n))) (fiber (ΩΣf A∙) p)

    module _ (a : A) (q₁ q₂ : Path (Susp A) north south) where

      path-for : (q₁ >=> sym (meridian a)) == q₂ >=> sym (meridian a) ->
                 (q₁ == q₂)
      path-for sq =
        ▪comp sq
              (\i j -> compPath-filler q₁ (sym (meridian a)) i j)
              (\i j -> compPath-filler q₂ (sym (meridian a)) (~ i) j)
              (\i j -> north)
              (\i j -> meridian a j)

      path-eq : (q₁ >=> sym (meridian a) == q₂ >=> sym (meridian a)) ≃
                (q₁ == q₂)
      path-eq = path-for , isEquiv-▪comp _ _ _ _




    module _ (q : Path (Susp A) north south) where
      private
        P : A -> A -> Type ℓ
        P a₁ a₂ =
          meridian a₂ >=> sym (meridian ★A) == q >=> (sym (meridian a₁)) ->
          (south-code q)

        hP : ∀ a₁ a₂ -> isOfHLevel (suc (suc (n + n))) (P a₁ a₂)
        hP a₁ a₂ =
          isOfHLevelΠ (suc (suc (n + n))) (\_ -> isOfHLevel-Squashₙ (suc (suc (n + n))))

        f₁ : ∀ a -> P a ★A
        f₁ a p = ∣ a , ans ∣
          where

          p' : meridian a >=> sym (meridian a) == q >=> (sym (meridian a))
          p' = (compPath-sym (meridian a) >=> sym (compPath-sym (meridian ★A))) >=>
               p

          ans : meridian a == q
          ans = path-for a (meridian a) q p'

          ans' : meridian a == q
          ans' = isEqInv (isEquiv->isEmbedding (isEquiv-compPath-right (sym (meridian a)) _) _ _) p'

        f₁' : ∀ a -> P a ★A
        f₁' a p = ∣ a , (\i j -> p' j (~ i)) ∣
          where
          check-p : refl == q >=> (sym (meridian a))
          check-p = sym (compPath-sym (meridian ★A)) >=> p

          p' : Square refl refl q (meridian a)
          p' = transP-right check-p (symP (doubleCompPath-filler q refl (sym (meridian a))))

        f₂' : ∀ a -> P ★A a
        f₂' a p = ∣ a , ans ∣
          where
          check-p : meridian a >=> sym (meridian ★A) == q >=> (sym (meridian ★A))
          check-p = p

          ans : meridian a == q
          ans = sym (compPath-refl-right (meridian a)) >=>
                cong (meridian a >=>_) (sym (compPath-sym (sym (meridian ★A)))) >=>
                sym (compPath-assoc _ _ _) >=>
                cong (_>=> (meridian ★A)) p >=>
                (compPath-assoc _ _ _) >=>
                cong (q >=>_) (compPath-sym (sym (meridian ★A))) >=>
                (compPath-refl-right q)




        f₂ : ∀ a -> P ★A a
        f₂ a p = ∣ a , ans ∣
          where
          ans : meridian a == q
          ans = path-for ★A (meridian a) q p


          ans' : meridian a == q
          ans' = isEqInv (isEquiv->isEmbedding (isEquiv-compPath-right (sym (meridian ★A)) _) _ _) p

        fp : f₁ ★A == f₂ ★A
        fp i p = ∣ ★A , ans-path i ∣ -- sym (cases.step₂ q (meridian ★A) p i) ∣
          where
          p' : meridian ★A >=> sym (meridian ★A) == q >=> (sym (meridian ★A))
          p' = (compPath-sym (meridian ★A) >=> sym (compPath-sym (meridian ★A))) >=>
               p

          p'=p : p' == p
          p'=p = cong (_>=> p) (compPath-sym _) >=> compPath-refl-left _

          ans-path : path-for ★A (meridian ★A) q p' == path-for ★A (meridian ★A) q p
          ans-path k = path-for ★A (meridian ★A) q (p'=p k)


        Σf = (extend-raw-wedge A∙ A∙ cA cA P hP f₁ f₂ fp)

      extend : ∀ a₁ a₂ ->
                 (meridian a₂ >=> sym (meridian ★A) == q >=> (sym (meridian a₁))) ->
                 south-code q
      extend = fst Σf


      extend/★A₂ : (a₁ : A) -> (meridian ★A >=> sym (meridian ★A) == q >=> (sym (meridian a₁))) -> south-code q
      extend/★A₂ = f₁



      extend/★A₁ : (Squashₙ (suc (suc (n + n)))
                    (Σ[ a₂ ∈ A ] (meridian a₂ >=> sym (meridian ★A) == q >=> (sym (meridian ★A))))) ->
                  south-code q
      extend/★A₁ =  ∥ₙ-map (\ (a₂ , p) ->  a₂ , path-for ★A (meridian a₂) q p)

      extend/★A₁-path : ∀ a₂ p -> extend/★A₁ (∣ a₂ , p ∣) == extend ★A a₂ p
      extend/★A₁-path a₂ p i = fst (snd (snd Σf)) a₂ (~ i) p

      extend/★A₂-path : ∀ a₁ p -> extend/★A₂ a₁ p == extend a₁ ★A p
      extend/★A₂-path a₁ p i = (fst (snd Σf)) a₁ (~ i) p


      isEquiv-extend/★A₁ : isEquiv extend/★A₁
      isEquiv-extend/★A₁ =
        ∥ₙ-map-preserves-isEquiv _
          (snd (existential-eq
            (\a -> (path-eq ★A (meridian a) q))))



    mid-fun : ∀ (a₁ : A) (q : Path (Susp A) north south) ->
      north-code (q >=> sym (meridian a₁)) -> south-code q
    mid-fun a₁ q =
      (∥ₙ-elim
        (\_ -> isOfHLevel-Squashₙ (suc (suc (n + n))))
        (\ (a₂ , sq) -> extend q a₁ a₂ sq))

    -- mid-funᵀ : ∀ (a₁ : A) (q : Path (Susp A) north south) ->
    --   north-code (q >=> sym (meridian a₁)) -> south-code q
    -- mid-funᵀ a₁ q =
    --   (∥ₙ-elim
    --     (\_ -> isOfHLevel-Squashₙ (suc (suc (n + n))))
    --     (\ (a₂ , sq) -> extend q a₁ a₂ sq))




    extend/★A₁-mid-path : ∀ q -> extend/★A₁ q == mid-fun ★A q
    extend/★A₁-mid-path q =
      funExt (∥ₙ-elim (\_ -> isOfHLevelPath (suc (suc (n + n))) (isOfHLevel-Squashₙ (suc (suc (n + n)))) _ _)
                      (\ (a , p) i -> extend/★A₁-path q a p i))


    mid-eq : ∀ (a₁ : A) (q : Path (Susp A) north south) ->
      north-code (q >=> sym (meridian a₁)) ≃ south-code q
    mid-eq a₁ q = mid-fun a₁ q , isEquiv-mid-fun
      where

      isEquiv-mid-fun/★A : isEquiv (mid-fun ★A q)
      isEquiv-mid-fun/★A =
        subst isEquiv (extend/★A₁-mid-path q) (isEquiv-extend/★A₁ q)

      opaque
        isEquiv-mid-fun : isEquiv (mid-fun a₁ q)
        isEquiv-mid-fun =
          ∥ₙ-elim (\_ -> isProp-isEquiv {f = mid-fun a₁ q}) handle ap
          where
          cA₀ : isConnected A
          cA₀ = reduce-isConnectedₙ₋₂ (suc-≤ (suc-≤ zero-≤)) cA

          ap : Squashₙ 1 (a₁ == ★A)
          ap = eqInv (squashed-path-eq 1 _ _) (isContr->isProp cA₀ _ _)

          handle : a₁ == ★A -> isEquiv (mid-fun a₁ q)
          handle p =
            transport (\i -> isEquiv (mid-fun (p (~ i)) q))
              isEquiv-mid-fun/★A




    -- mid-path : (a₁ : A) ->
    --   PathP (\i -> north == meridian a₁ i -> Type ℓ) north-code south-code
    -- mid-path a₁ =
    --   (\i q ->
    --     hcomp (\k -> \{ (i = i0) -> north-code (transport-sym (\j -> north == meridian a₁ j) q k)
    --                   ; (i = i1) -> south-code q
    --                   })
    --       (mid-path₁ (transp (\j -> north == meridian a₁ (i ∨ j)) i q) i))
    --   where

    --   mid-path₂ : ∀ (q : Path (Susp A) north south) ->
    --     north-code (q >=> sym (meridian a₁)) == south-code q
    --   mid-path₂ q = ua (mid-eq a₁ q)



    --   mid-path₁ : ∀ (q : Path (Susp A) north south) ->
    --     north-code (transport (cong (north ==_) (sym (meridian a₁))) q) == south-code q
    --   mid-path₁ q = cong north-code (transport=compPath q (sym (meridian a₁))) >=> mid-path₂ q

    module mid-path (a₁ : A) where
      right :
        Path (∀ (q : Path (Susp A) north south) -> Type ℓ)
             (\q -> north-code (q >=> sym (meridian a₁)))
             (\q -> south-code q)
      right i q = ua (mid-eq a₁ q) i


      left' :
        PathP (\i -> ∀ (q : Path (Susp A) north (meridian a₁ i)) -> north == north)
              (\q -> q)
              (\q -> (q >=> sym (meridian a₁)))
      left' i q =
        (hcomp (\k -> \{ (i = i0) -> q
                       ; (i = i1) -> transport=compPath q (sym (meridian a₁)) k
                       })
               (transp (\j -> north == meridian a₁ (i ∧ ~ j)) (~ i) q))

      left :
        PathP (\i -> ∀ (q : Path (Susp A) north (meridian a₁ i)) -> Type ℓ)
              (\q -> north-code q)
              (\q -> north-code (q >=> sym (meridian a₁)))
      left i q = north-code (left' i q)



    mid-path : (a₁ : A) ->
      PathP (\i -> north == meridian a₁ i -> Type ℓ) north-code south-code
    mid-path a₁ = transP-left (mid-path.left a₁) (mid-path.right a₁)


    mid-path-left'-refl : (a₁ : A)
      (q : Path (Susp A) north south) ->
      Path (Path (north == north) (q >=> sym (meridian a₁)) (q >=> sym (meridian a₁)))
        (\i -> mid-path.left' a₁ i ((compPath-filler q (sym (meridian a₁))) (~ i)))
        refl
    mid-path-left'-refl a₁ q = step₁ >=> ∙∙-refl
      where
      p₁ :
        Path (north == north)
          (q >=> sym (meridian a₁))
          (transport (\j -> north == meridian a₁ (~ j)) q)
      p₁ i =
        (transp (\j -> north == meridian a₁ (i ∧ ~ j)) (~ i)
                ((compPath-filler q (sym (meridian a₁))) (~ i)))

      stage₁ : (Path (north == north) (q >=> sym (meridian a₁)) (q >=> sym (meridian a₁)))
      stage₁ = refl ∙∙ p₁ ∙∙ sym p₁

      stage₂ : (Path (north == north) (q >=> sym (meridian a₁)) (q >=> sym (meridian a₁)))
      stage₂ = refl ∙∙ refl ∙∙ refl

      step₁ : stage₁ == stage₂
      step₁ k = refl ∙∙ (\i -> p₁ (i ∧ ~ k)) ∙∙ (\i -> p₁ (~ i ∧ ~ k))



    module mid-path' (a₁ : A) (i : I) (q : north == meridian a₁ i) where
      q' : north == south
      q' = transport (\j -> north == meridian a₁ (i ∨ j)) q

      mid-p : north-code (q' >=> sym (meridian a₁)) == south-code q'
      mid-p = ua (mid-eq a₁ q')

      left-p₁ : (q' >=> sym (meridian a₁)) ==
                transport (\j -> north == meridian a₁ (~ j)) q'
      left-p₁ = sym (transport=compPath _ _)

      left-p₂ : transport (\j -> north == meridian a₁ (~ j)) q' ==
                transport (\j -> north == meridian a₁ (i ∧ ~ j)) q
      left-p₂ k =
        transport (\j -> north == meridian a₁ (~ j ∧ (i ∨ ~ k)))
          (transp (\j -> north == meridian a₁ (i ∨ (j ∧ (i ∨ ~ k)))) k
            q)


      left-p : north-code (q' >=> sym (meridian a₁)) ==
               north-code (transport (\j -> north == meridian a₁ (i ∧ ~ j)) q)
      left-p = cong north-code (left-p₁ >=> left-p₂)

      left-p₀ : PartialP {ℓ} (~ i) (\{ (i = i0) -> (q' >=> sym (meridian a₁)) == q })
      left-p₀ (i = i0) =
        (cong (_>=> sym (meridian a₁)) (transport=compPath q (meridian a₁))) >=>
        (\k -> (q >=> (\i -> meridian a₁ (i ∧ ~ k))) >=> (\i -> meridian a₁ (~ i ∧ ~ k))) >=>
        compPath-refl-right _ >=>
        compPath-refl-right _


    mid-path' : (a₁ : A) ->
      PathP (\i -> north == meridian a₁ i -> Type ℓ) north-code south-code
    mid-path' a₁ i q =
      hcomp (\k -> \{ (i = i0) -> north-code (left-p₀ 1=1 k)
                    ; (i = i1) -> south-code (transportRefl q k)
                    })
        (mid-p i)
      where
      open mid-path' a₁ i q




    module _ (a₁ : A) (q₀ : north == south) where
      private
        f : north-code (q₀ >=> sym (meridian a₁)) -> south-code q₀
        f = mid-fun a₁ q₀

        sq : Square (q₀ >=> sym (meridian a₁)) q₀ refl (meridian a₁)
        sq = ▪comp (\i j -> south)
                   (symP (doubleCompPath-filler _ _ _) )
                   (\i j -> q₀ (~ i ∨ j))
                   (\i j -> q₀ j)
                   (\i j -> meridian a₁ (~ j ∨ i))

        f₂ : north-code (q₀ >=> sym (meridian a₁)) -> south-code q₀
        f₂ = transport (\i -> mid-path' a₁ i (sq i))

        module _ (i : I) where
          q : north == meridian a₁ i
          q = sq i
          open mid-path' a₁ i (sq i)




       -- mid-path'/square₁ :
       --   transport (\i -> mid-path' a₁ i (transport (\j -> north == meridian a₁ (~ j ∨ i)) q)) ==
       --   mid-fun a₁ q
       -- mid-path'/square = ?






    encode : ∀ (s : Susp A) -> (north == s) -> Type ℓ
    encode north = north-code
    encode south = south-code
    encode (meridian a₁ i) = mid-path a₁ i

    encode' :  Σ[ s ∈ Susp A ] (north == s) -> Type ℓ
    encode' (s , p) = encode s p


    module _
      (q : Path (Susp A) north south)
      (a₁ : A)
      (r : meridian ★A >=> sym (meridian ★A) ==
           q >=> sym (meridian a₁))
      where
      private

        r₂ : refl == q >=> sym (meridian a₁)
        r₂ = sym (compPath-sym (meridian ★A)) >=> r


        r' : meridian a₁ == q
        r' =
          ▪comp (compPath-sym (meridian a₁) >=> r₂)
                (\i j -> compPath-filler (meridian a₁) (sym (meridian a₁)) i j)
                (\i j -> compPath-filler q (sym (meridian a₁)) (~ i) j)
                (\i j -> north)
                (\i j -> meridian a₁ j)



        t : Square (q >=> sym (meridian a₁)) q (reflᵉ north) (meridian a₁)
        t = symP (compPath-filler q (sym (meridian a₁)))


      encode'-merid₁ :
        Path (encode south q)
             (substᵉ encode' (\i -> meridian a₁ i , t i) ∣ (★A , r) ∣)
             (∣ (a₁ , r') ∣)
      encode'-merid₁ = step₁ >=> step₂ >=> step₃
        where
        lhs : encode south q
        lhs = (substᵉ encode' (\i -> meridian a₁ i , t i) ∣ (★A , r) ∣)

        stage₁ : encode south q
        stage₁ = transport (\i -> (refl ∙∙
                                   (\j -> mid-path.left a₁ j (t j)) ∙∙
                                   (\j -> mid-path.right a₁ j q)) i)
                           (∣ (★A , r) ∣)

        step₀ : lhs == stage₁
        step₀ = refl

        stage₂ : encode south q
        stage₂ =
          (transport (\j -> mid-path.right a₁ j q)
            (transport (\j -> mid-path.left a₁ j (t j))
              (transport (reflᵉ (north-code (q >=> sym (meridian a₁))))
                (∣ (★A , r) ∣))))

        step₁ : stage₁ == stage₂
        step₁ = transport-∙∙ refl (\j -> mid-path.left a₁ j (t j)) (\j -> mid-path.right a₁ j q)
                  (∣ (★A , r) ∣)

        step₂-inner₁ :
          (transport (reflᵉ (north-code (q >=> sym (meridian a₁))))
            (∣ (★A , r) ∣)) ==
          (∣ (★A , r) ∣)
        step₂-inner₁ = transportRefl (∣ (★A , r) ∣)

        step₂-inner₂ :
          (transport (\j -> mid-path.left a₁ j (t j))
            (∣ (★A , r) ∣)) ==
          (∣ (★A , r) ∣)
        step₂-inner₂ =
          (\k -> transport (\i -> north-code (mid-path-left'-refl a₁ q k i)) (∣ (★A , r) ∣)) >=>
          transportRefl (∣ (★A , r) ∣)

        step₂-inner₃ :
          (transport (\j -> mid-path.right a₁ j q)
            (∣ (★A , r) ∣))
           == extend q a₁ ★A r
        step₂-inner₃ i = transport-ua (mid-eq a₁ q) i (∣ (★A , r) ∣)

        stage₃ : encode south q
        stage₃ = extend q a₁ ★A r

        step₂ : stage₂ == stage₃
        step₂ =
          cong (transport (\j -> mid-path.right a₁ j q))
            (cong (transport (\j -> mid-path.left a₁ j (t j))) step₂-inner₁ >=>
             step₂-inner₂) >=>
          step₂-inner₃

        step₃ : stage₃ == (∣ (a₁ , r') ∣)
        step₃ = sym (extend/★A₂-path q a₁ r) >=> (\i -> ∣ a₁ , r-path i ∣)
          where
          e⁻¹ : (meridian a₁ >=> sym (meridian a₁) == q >=> sym (meridian a₁)) -> meridian a₁ == q
          e⁻¹ = path-for a₁ (meridian a₁) q

          r-path : e⁻¹ ((compPath-sym (meridian a₁) >=> sym (compPath-sym (meridian ★A))) >=> r) == r'
          r-path = cong e⁻¹ (compPath-assoc _ _ r)







    module _
      (q : Path (Susp A) north south)
      (a₂ : A)
      (r : meridian a₂ >=> sym (meridian ★A) ==
           q >=> sym (meridian ★A))
      where
      private
        r' : meridian a₂ == q
        r' = transP-sides
              (compPath-filler (meridian a₂) (sym (meridian ★A)))
              r
              (symP (compPath-filler q (sym (meridian ★A))))


        r'₂ : meridian a₂ == q
        r'₂ =
          ▪comp r
                (\i j -> compPath-filler (meridian a₂) (sym (meridian ★A)) i j)
                (\i j -> compPath-filler q (sym (meridian ★A)) (~ i) j)
                (\i j -> north)
                (\i j -> meridian ★A j)


        t : Square (q >=> sym (meridian ★A)) q (reflᵉ north) (meridian ★A)
        t = symP (compPath-filler q (sym (meridian ★A)))


      encode'-merid₂ :
        Path (encode south q)
             (substᵉ encode' (\i -> meridian ★A i , t i) ∣ (a₂ , r) ∣)
             (∣ (a₂ , r'₂) ∣)
      encode'-merid₂ = step₁ >=> step₂ >=> step₃
        where
        lhs : encode south q
        lhs = (substᵉ encode' (\i -> meridian ★A i , t i) ∣ (a₂ , r) ∣)

        stage₁ : encode south q
        stage₁ = transport (\i -> (refl ∙∙
                                   (\j -> mid-path.left ★A j (t j)) ∙∙
                                   (\j -> mid-path.right ★A j q)) i)
                           (∣ (a₂ , r) ∣)

        step₀ : lhs == stage₁
        step₀ = refl

        stage₂ : encode south q
        stage₂ =
          (transport (\j -> mid-path.right ★A j q)
            (transport (\j -> mid-path.left ★A j (t j))
              (transport (reflᵉ (north-code (q >=> sym (meridian ★A))))
                (∣ (a₂ , r) ∣))))

        step₁ : stage₁ == stage₂
        step₁ = transport-∙∙ refl (\j -> mid-path.left ★A j (t j)) (\j -> mid-path.right ★A j q)
                  (∣ (a₂ , r) ∣)

        step₂-inner₁ :
          (transport (reflᵉ (north-code (q >=> sym (meridian ★A))))
            (∣ (a₂ , r) ∣)) ==
          (∣ (a₂ , r) ∣)
        step₂-inner₁ = transportRefl (∣ (a₂ , r) ∣)


        step₂-inner₂ :
          (transport (\j -> mid-path.left ★A j (t j))
            (∣ (a₂ , r) ∣)) ==
          (∣ (a₂ , r) ∣)
        step₂-inner₂ =
          (\k -> transport (\i -> north-code (mid-path-left'-refl ★A q k i)) (∣ (a₂ , r) ∣)) >=>
          transportRefl (∣ (a₂ , r) ∣)


        step₂-inner₃ :
          (transport (\j -> mid-path.right ★A j q)
            (∣ (a₂ , r) ∣))
           == extend q ★A a₂ r
        step₂-inner₃ i = transport-ua (mid-eq ★A q) i (∣ (a₂ , r) ∣)


        stage₃ : encode south q
        stage₃ = extend q ★A a₂ r

        step₂ : stage₂ == stage₃
        step₂ =
          cong (transport (\j -> mid-path.right ★A j q))
            (cong (transport (\j -> mid-path.left ★A j (t j))) step₂-inner₁ >=>
             step₂-inner₂) >=>
          step₂-inner₃


        step₃ : stage₃ == (∣ (a₂ , r'₂) ∣)
        step₃ = sym (extend/★A₁-path q a₂ r)







    center : ∀ s p -> encode s p
    center s p = transport (\i -> encode' (p i , (\j -> (p (j ∧ i))))) raw-center
      where
      raw-center : encode north refl
      raw-center = ∣ ★A , compPath-sym _ ∣


    center-path-fixed : ∀ a₁ ->
      center north (meridian a₁ >=> sym (meridian ★A)) == ∣ a₁ , refl ∣
    center-path-fixed a₁ = step₁ >=> step₂
      where
      lhs : encode' (north , (meridian a₁ >=> sym (meridian ★A)))
      lhs = center north (meridian a₁ >=> sym (meridian ★A))

      rhs : encode' (north , (meridian a₁ >=> sym (meridian ★A)))
      rhs = ∣ a₁ , refl ∣

      p₁ : Path (Σ[ s ∈ Susp A ] (north == s))
             (north , refl)
             (north , (meridian a₁ >=> sym (meridian ★A)))
      p₁ i = (meridian a₁ >=> sym (meridian ★A)) i ,
             (\j -> ((meridian a₁ >=> sym (meridian ★A)) (j ∧ i)))

      q₁ : Path (Σ[ s ∈ Susp A ] (north == s))
             (north , refl)
             (north , meridian a₁ >=> sym (meridian a₁))
      q₁ i = north , (compPath-sym (meridian a₁)) (~ i)

      q₂ : Path (Σ[ s ∈ Susp A ] (north == s))
             (north , meridian a₁ >=> sym (meridian a₁))
             (south , meridian a₁)
      q₂ i = meridian a₁ i , compPath-filler (meridian a₁) (sym (meridian a₁)) (~ i)

      q₃ : Path (Σ[ s ∈ Susp A ] (north == s))
             (south , meridian a₁)
             (north , meridian a₁ >=> sym (meridian ★A))
      q₃ i = meridian ★A (~ i) , compPath-filler (meridian a₁) (sym (meridian ★A)) i


      h : isSet (Σ[ s ∈ Susp A ] (north == s))
      h = isContr->isOfHLevel 2 (isContr-singleton north)

      p₁=q₁₂₃ : p₁ == q₁ ∙∙ q₂ ∙∙ q₃
      p₁=q₁₂₃ = h _ _ _ _

      stage₁ : encode north (meridian a₁ >=> sym (meridian ★A))
      stage₁ = transport (\i -> encode' (p₁ i)) ∣ ★A , compPath-sym _ ∣

      step₀ : lhs == stage₁
      step₀ = refl

      stage₂ : encode north (meridian a₁ >=> sym (meridian ★A))
      stage₂ =
       transport (\i -> encode' (q₃ i))
         (transport (\i -> encode' (q₂ i))
           (transport (\i -> encode' (q₁ i))
             ∣ ★A , compPath-sym _ ∣))

      step₁ : stage₁ == stage₂
      step₁ =
        (\k -> transport (\i -> ep₁=eq₁₂₃ k i) ∣ ★A , compPath-sym _ ∣) >=>
        transport-∙∙ (cong encode' q₁) (cong encode' q₂) (cong encode' q₃) (∣ ★A , compPath-sym _ ∣)
        where
        ep₁=eq₁₂₃ : cong encode' p₁ == cong encode' q₁ ∙∙ cong encode' q₂ ∙∙ cong encode' q₃
        ep₁=eq₁₂₃ = (\k -> cong encode' (\i -> p₁=q₁₂₃ k i)) >=> cong-∙∙ encode' q₁ q₂ q₃

      north₁ˡ : encode north (meridian a₁ >=> sym (meridian a₁))
      north₁ˡ = transport (\i -> encode' (q₁ i)) ∣ ★A , compPath-sym (meridian ★A) ∣

      north₁ʳ : encode north (meridian a₁ >=> sym (meridian a₁))
      north₁ʳ = ∣ ★A , compPath-sym (meridian ★A) >=> sym (compPath-sym (meridian a₁)) ∣

      north₁-p : north₁ˡ == north₁ʳ
      north₁-p = transP-sym north₁ˡ-center (symP north₁ʳ-center)
        where
        n₁-center : encode north refl
        n₁-center = ∣ ★A , compPath-sym (meridian ★A) ∣


        north₁ˡ-center : PathP (\k -> encode north (compPath-sym (meridian a₁) k))
                               north₁ˡ
                               n₁-center
        north₁ˡ-center = symP (transport-filler _ n₁-center)

        north₁ʳ-center : PathP (\k -> encode north (compPath-sym (meridian a₁) k))
                               north₁ʳ
                               n₁-center
        north₁ʳ-center k = ∣ ★A , compPath-filler (compPath-sym (meridian ★A)) (sym (compPath-sym (meridian a₁))) (~ k) ∣


      south₁ˡ : encode south (meridian a₁)
      south₁ˡ = transport (\i -> encode' (q₂ i)) north₁ʳ

      south₁ʳ : encode south (meridian a₁)
      south₁ʳ = ∣ a₁ , refl ∣

      south₁-p : south₁ˡ == south₁ʳ
      south₁-p = s₁-step₁ >=> (\i -> ∣ a₁ , s₁-step₂' i ∣)
        where
        s₁-center : encode south (meridian a₁)
        s₁-center = ∣ a₁ , _ ∣

        s₁-step₁ : south₁ˡ == s₁-center
        s₁-step₁ = encode'-merid₁ (meridian a₁) a₁ (compPath-sym (meridian ★A) >=> sym (compPath-sym (meridian a₁)))


        cps★ : (meridian ★A >=> sym (meridian ★A)) == refl
        cps★ = (compPath-sym (meridian ★A))
        cps₁ : (meridian a₁ >=> sym (meridian a₁)) == refl
        cps₁ = (compPath-sym (meridian a₁))

        dcp : Square refl (meridian a₁ >=> sym (meridian a₁)) (sym (meridian a₁)) (sym (meridian a₁))
        dcp = doubleCompPath-filler (meridian a₁) refl (sym (meridian a₁))

        module _ where
          private
            q : Path (Susp A) north south
            q = (meridian a₁)

            r : (meridian ★A >=> sym (meridian ★A)) == (q >=> sym (meridian a₁))
            r = (compPath-sym (meridian ★A) >=> sym (compPath-sym (meridian a₁)))


          s₁-step₂' :
            Path (meridian a₁ == meridian a₁)
            (▪comp (cps₁ >=> (sym cps★ >=> (cps★ >=> sym cps₁)))
                   (\i j -> compPath-filler (meridian a₁) (sym (meridian a₁)) i j)
                   (\i j -> compPath-filler q (sym (meridian a₁)) (~ i) j)
                   (\i j -> north)
                   (\i j -> meridian a₁ j))
            refl
          s₁-step₂' = s₁₂-step₁ >=> s₁₂-step₂ >=> s₁₂-step₃ >=> s₁₂-step₄
            where
            center-path : (cps₁ >=> (sym cps★ >=> (cps★ >=> sym cps₁))) ==
                          (\i j -> (meridian a₁ >=> sym (meridian a₁)) j)
            center-path =
              (\k -> cps₁ >=> sym (cps-simp k)) >=>
              compPath-sym cps₁
              where
              cps-simp : (sym (sym cps★ >=> (cps★ >=> sym cps₁))) == cps₁
              cps-simp = compPath-assoc cps₁ (sym cps★) cps★ >=>
                         cong (cps₁ >=>_) (compPath-sym _) >=>
                         compPath-refl-right cps₁

            s₁₂-lhs : (meridian a₁ == meridian a₁)
            s₁₂-lhs =
              (▪comp (cps₁ >=> (sym cps★ >=> (cps★ >=> sym cps₁)))
                     (\i j -> compPath-filler (meridian a₁) (sym (meridian a₁)) i j)
                     (\i j -> compPath-filler q (sym (meridian a₁)) (~ i) j)
                     (\i j -> north)
                     (\i j -> meridian a₁ j))

            s₁₂-stage₁ : (meridian a₁ == meridian a₁)
            s₁₂-stage₁ =
              (▪comp (\i j -> (meridian a₁ >=> sym (meridian a₁)) j)
                     (\i j -> compPath-filler (meridian a₁) (sym (meridian a₁)) i j)
                     (\i j -> compPath-filler q (sym (meridian a₁)) (~ i) j)
                     (\i j -> north)
                     (\i j -> meridian a₁ j))

            s₁₂-step₁ : s₁₂-lhs == s₁₂-stage₁
            s₁₂-step₁ k =
              (▪comp (center-path k)
                     (\i j -> compPath-filler (meridian a₁) (sym (meridian a₁)) i j)
                     (\i j -> compPath-filler q (sym (meridian a₁)) (~ i) j)
                     (\i j -> north)
                     (\i j -> meridian a₁ j))

            cpf : Square (meridian a₁) (meridian a₁ >=> sym (meridian a₁)) (reflᵉ north) (sym (meridian a₁))
            cpf = compPath-filler (meridian a₁) (sym (meridian a₁))

            s₁₂-stage₂ : (meridian a₁ == meridian a₁)
            s₁₂-stage₂ =
              (▪comp (\i j -> cpf i1 j)
                     (\i j -> cpf i j)
                     (\i j -> cpf (~ i) j)
                     (\i j -> north)
                     (\i j -> meridian a₁ j))

            s₁₂-step₂ : s₁₂-stage₁ == s₁₂-stage₂
            s₁₂-step₂ = refl

            s₁₂-stage₃ : (meridian a₁ == meridian a₁)
            s₁₂-stage₃ =
              (▪comp (\i j -> cpf i0 j)
                     (\i j -> cpf i0 j)
                     (\i j -> cpf i0 j)
                     (\i j -> north)
                     (\i j -> south))

            s₁₂-step₃ : s₁₂-stage₂ == s₁₂-stage₃
            s₁₂-step₃ k =
              (▪comp (\i j -> cpf (~ k) j)
                     (\i j -> cpf (i ∧ ~ k) j)
                     (\i j -> cpf (~ i ∧ ~ k) j)
                     (\i j -> north)
                     (\i j -> meridian a₁ (j ∨ k)))

            s₁₂-stage₄ : (meridian a₁ == meridian a₁)
            s₁₂-stage₄ i j = meridian a₁ j


            s₁₂-step₄ : s₁₂-stage₃ == s₁₂-stage₄
            s₁₂-step₄ = ▪comp-refl _






        -- s₁-step₂ :
        --   Path (meridian a₁ == meridian a₁)
        --   (\i j ->
        --     (transP-left (doubleCompPath-filler (meridian a₁) refl (sym (meridian a₁)))
        --       (sym (sym cps★ >=> (cps★ >=> sym cps₁))))
        --     (~ j) (~ i))
        --   refl
        -- s₁-step₂ = s₁₂-step₁ >=> s₁₂-step₂
        --   where

        --   s₁₂-lhs : (meridian a₁ == meridian a₁)
        --   s₁₂-lhs =
        --     (\i j ->
        --       (transP-left (doubleCompPath-filler (meridian a₁) refl (sym (meridian a₁)))
        --         (sym (sym cps★ >=> (cps★ >=> sym cps₁))))
        --       (~ j) (~ i))

        --   cps-simp : (sym (sym cps★ >=> (cps★ >=> sym cps₁))) == cps₁
        --   cps-simp = compPath-assoc cps₁ (sym cps★) cps★ >=>
        --              cong (cps₁ >=>_) (compPath-sym _) >=>
        --              compPath-refl-right cps₁


        --   s₁₂-stage₁ : Square (meridian a₁) (meridian a₁) refl refl
        --   s₁₂-stage₁ =
        --     (\i j ->
        --       (transP-left (doubleCompPath-filler (meridian a₁) refl (sym (meridian a₁))) cps₁)
        --       (~ j) (~ i))

        --   s₁₂-step₁ : s₁₂-lhs == s₁₂-stage₁
        --   s₁₂-step₁ k =
        --     (\i j ->
        --       (transP-left (doubleCompPath-filler (meridian a₁) refl (sym (meridian a₁))) (cps-simp k))
        --       (~ j) (~ i))

        --   s₁₂-stage₂ : Square refl refl (sym (meridian a₁)) (sym (meridian a₁))
        --   s₁₂-stage₂ =
        --     ▪comp (doubleCompPath-filler (meridian a₁) refl (sym (meridian a₁)))
        --           (\i j -> south)
        --           (\i j -> cps₁ i j)
        --           (\i j -> meridian a₁ (~ i))
        --           (\i j -> meridian a₁ (~ i))


        --   s₁₂-stage₂₅ : Square refl refl (sym (meridian a₁)) (sym (meridian a₁))
        --   s₁₂-stage₂₅ =
        --     ▪comp (\i j -> south)
        --           (\i j -> south)
        --           (\i j -> meridian a₁ (~ i))
        --           (\i j -> meridian a₁ (~ i ∨ j))
        --           (\i j -> meridian a₁ (~ i ∨ ~ j))

        --   s₁₂-step₂₅ : s₁₂-stage₂ == s₁₂-stage₂₅
        --   s₁₂-step₂₅ k =
        --     ▪comp (\i j -> doubleCompPath-filler (meridian a₁) refl (sym (meridian a₁)) (i ∧ ~ k) j)
        --           (\i j -> south)
        --           (\i j -> compPath-sym-filler (meridian a₁) (~ k) i j)
        --           (\i j -> meridian a₁ (~ i ∨ (j ∧ k)))
        --           (\i j -> meridian a₁ (~ i ∨ (~ j ∧ k)))

        --   s₁₂-stage₃ : Square refl refl (sym (meridian a₁)) (sym (meridian a₁))
        --   s₁₂-stage₃ =
        --     ▪comp (\i j -> meridian a₁ (~ i))
        --           (\i j -> south)
        --           (\i j -> north)
        --           (\i j -> meridian a₁ (~ i))
        --           (\i j -> meridian a₁ (~ i))

        --   s₁₂-step₂₆ : s₁₂-stage₂₅ == s₁₂-stage₃
        --   s₁₂-step₂₆ k =
        --     ▪comp (\i j -> meridian a₁ (~ i ∨ ~ k))
        --           (\i j -> south)
        --           (\i j -> meridian a₁ (~ i ∧ ~ k))
        --           (\i j -> meridian a₁ (~ i ∨ (j ∧ ~ k)))
        --           (\i j -> meridian a₁ (~ i ∨ (~ j ∧ ~ k)))

        --   s₁₂-stage₄ : Square refl refl (sym (meridian a₁)) (sym (meridian a₁))
        --   s₁₂-stage₄ = (\i j -> meridian a₁ (~ i))

        --   s₁₂-step₃ : s₁₂-stage₂ == s₁₂-stage₄
        --   s₁₂-step₃ = s₁₂-step₂₅ ∙∙ s₁₂-step₂₆ ∙∙ sym (transP-mid-filler _ _ _)

        --   s₁₂-step₂ : s₁₂-stage₁ == refl
        --   s₁₂-step₂ k = sym (▪ᵀ (symP (s₁₂-step₃ k)))





      south₂ˡ : encode south (meridian a₁)
      south₂ˡ = transport (\i -> encode' (q₃ (~ i))) ∣ a₁ , refl ∣

      south₂ʳ : encode south (meridian a₁)
      south₂ʳ = ∣ a₁ , refl ∣

      south₂-p : south₂ˡ == south₂ʳ
      south₂-p = s₂-step₁ >=> (\i -> ∣ a₁ , s₂-step₂' i ∣)
        where
        s₂-center : encode south (meridian a₁)
        s₂-center = ∣ a₁ ,
          transP-sides
            (compPath-filler (meridian a₁) (sym (meridian ★A)))
            refl
            (symP (compPath-filler (meridian a₁) (sym (meridian ★A)))) ∣

        q : Path (Susp A) north south
        q = (meridian a₁)

        r : (meridian a₁ >=> sym (meridian ★A)) == (q >=> sym (meridian ★A))
        r = refl

        s₂-center' : encode south (meridian a₁)
        s₂-center' = ∣ a₁ ,
          ▪comp r
                (\i j -> compPath-filler (meridian a₁) (sym (meridian ★A)) i j)
                (\i j -> compPath-filler q (sym (meridian ★A)) (~ i) j)
                (\i j -> north)
                (\i j -> meridian ★A j) ∣


        s₂-step₁ : south₂ˡ == s₂-center'
        s₂-step₁ = encode'-merid₂ (meridian a₁) a₁ refl

        s₂-step₂ :
          Path (meridian a₁ == meridian a₁)
          (transP-sym
            (compPath-filler (meridian a₁) (sym (meridian ★A)))
            (symP (compPath-filler (meridian a₁) (sym (meridian ★A)))))
          refl
        s₂-step₂ =
          (\k -> (transP-sym
            (\i -> compPath-filler (meridian a₁) (sym (meridian ★A)) (i ∧ (~ k)))
            (symP (\i -> compPath-filler (meridian a₁) (sym (meridian ★A)) (i ∧ (~ k)))))) >=>
          transP-sides->∙∙ refl refl refl >=>
          ∙∙-refl

        s₂-step₂' :
          Path (meridian a₁ == meridian a₁)
          (▪comp (\i j -> (meridian a₁ >=> sym (meridian ★A)) j)
                 (\i j -> compPath-filler (meridian a₁) (sym (meridian ★A)) i j)
                 (\i j -> compPath-filler q (sym (meridian ★A)) (~ i) j)
                 (\i j -> north)
                 (\i j -> meridian ★A j))
          refl
        s₂-step₂' = s₂₂-step₂ >=> s₂₂-step₃
          where
          s₂₂-lhs : (meridian a₁ == meridian a₁)
          s₂₂-lhs =
            (▪comp (\i j -> (meridian a₁ >=> sym (meridian ★A)) j)
                   (\i j -> compPath-filler (meridian a₁) (sym (meridian ★A)) i j)
                   (\i j -> compPath-filler q (sym (meridian ★A)) (~ i) j)
                   (\i j -> north)
                   (\i j -> meridian ★A j))

          cpf : Square (meridian a₁) (meridian a₁ >=> sym (meridian ★A)) (reflᵉ north) (sym (meridian ★A))
          cpf = compPath-filler (meridian a₁) (sym (meridian ★A))

          s₂₂-stage₁ : (meridian a₁ == meridian a₁)
          s₂₂-stage₁ =
            (▪comp (\i j -> cpf i1 j)
                   (\i j -> cpf i j)
                   (\i j -> cpf (~ i) j)
                   (\i j -> north)
                   (\i j -> meridian ★A j))

          s₂₂-step₁ : s₂₂-lhs == s₂₂-stage₁
          s₂₂-step₁ = refl


          s₂₂-stage₂ : (meridian a₁ == meridian a₁)
          s₂₂-stage₂ =
            (▪comp (\i j -> cpf i0 j)
                   (\i j -> cpf i0 j)
                   (\i j -> cpf i0 j)
                   (\i j -> north)
                   (\i j -> south))

          s₂₂-step₂ : s₂₂-stage₁ == s₂₂-stage₂
          s₂₂-step₂ k =
            (▪comp (\i j -> cpf (~ k) j)
                   (\i j -> cpf (i ∧ ~ k) j)
                   (\i j -> cpf (~ i ∧ ~ k) j)
                   (\i j -> north)
                   (\i j -> meridian ★A (j ∨ k)))


          s₂₂-stage₃ : (meridian a₁ == meridian a₁)
          s₂₂-stage₃ i j = meridian a₁ j

          s₂₂-step₃ : s₂₂-stage₂ == s₂₂-stage₃
          s₂₂-step₃ = ▪comp-refl _









      step₂ : stage₂ == rhs
      step₂ =
        cong (transport (\i -> encode' (q₃ i)))
         (cong (transport (\i -> encode' (q₂ i))) north₁-p >=>
          south₁-p >=>
          sym south₂-p) >=>
        transport-sym (\i -> encode' (q₃ (~ i))) rhs






    center-path-north' : ∀ p -> (v : fiber (ΩΣf A∙) p) -> center north p == ∣ v ∣
    center-path-north' p (a₁ , r) =
      J (\p r -> center north p == ∣ a₁ , r ∣) (center-path-fixed a₁) r


    center-path-north : ∀ p -> (v : encode north p) -> center north p == v
    center-path-north p =
      ∥ₙ-elim
        (\_ -> isOfHLevelPath (suc (suc (n + n))) (isOfHLevel-Squashₙ (suc (suc (n + n)))) _ _)
        (center-path-north' p)


    isContr-encode-north : ∀ p -> isContr (encode north p)
    isContr-encode-north p = center north p , center-path-north p

  isConnectedMap-ΩΣf : isConnectedMapₙ (n + n) (ΩΣf A∙)
  isConnectedMap-ΩΣf p = isContr-encode-north p
