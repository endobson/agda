{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.freudenthal3 where


open import base
open import pointed.base
open import cubical
open import equality-path
open import equality.square
open import equality.dependent-path
open import base
open import funext
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
open import pointed.freudenthal2
open import pointed.suspension

{-


module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) {n : Nat} (cA : isConnectedₙ n A) where
  open freudenthal A∙ cA

  private
    module _ (a₁ : A) (l : I) where
      private
        open encode₄-m a₁ l (\i -> meridian a₁ (i ∧ l))

        ans-sq : Square refl (meridian a₁) refl (meridian a₁)
        ans-sq i j = meridian a₁ (i ∧ j)

        q₁=mˡ : Square q₁ (reflᵉ (meridian a₁ l)) n->m n->m
        q₁=mˡ = symP (doubleCompPath-filler n->m refl (sym n->m))

        mˡ=n : Square (reflᵉ (meridian a₁ l)) (reflᵉ north) (sym n->m) (sym n->m)
        mˡ=n i j = n->m (~ i)

        q₁=n : q₁ == (reflᵉ north)
        q₁=n = ▪comp (\i j -> meridian a₁ l) q₁=mˡ mˡ=n (\i -> n->m) (\i -> sym n->m)

        q₁=n-filler :
          PathP (\k -> Square (q₁=mˡ (~ k)) (mˡ=n k)
                              (\i -> n->m (~ k))
                              (\i -> n->m (~ k)))
                (\i j -> meridian a₁ l)
                q₁=n
        q₁=n-filler = ▪comp-filler (\i j -> meridian a₁ l) _ _ _ _

        q₁=n-simp₀ : PartialP {a = ℓ} (~ l)  (\{ (l = i0) -> q₁=n == compPath-refl-right n->m })
        q₁=n-simp₀ (l = i0) = step₀ ∙∙ step₁ ∙∙ step₃
          where
          q₁=n-check : q₁=n ==
            ▪comp (\i j -> north) q₁=mˡ (\i j -> north) (\i j -> north) (\i j -> north)
          q₁=n-check = refl

          q₁=n' : q₁ == (reflᵉ north)
          q₁=n' = ▪comp q₁=mˡ (\i j -> (reflᵉ north >=> reflᵉ north) j) (\i j -> north) (\i j -> north) (\i j -> north)

          step₀ : q₁=n == q₁=n'
          step₀ k =
            ▪comp (\i j -> q₁=mˡ (i ∨ ~ k) j)
                  (\i j -> q₁=mˡ (i ∧ ~ k) j)
                  (\i j -> north)
                  (\i j -> north)
                  (\i j -> north)

          step₁ : q₁=n' == q₁=mˡ
          step₁ = ▪comp-refl q₁=mˡ

          step₃ : q₁=mˡ == compPath-refl-right (reflᵉ north)
          step₃ i j = compPath/doubleCompPath-filler-refl north (~ i) (~ j)



        q₂=mˡ : Square q₂ (reflᵉ (meridian a₁ l)) n->m (sym m->s)
        q₂=mˡ = (symP (doubleCompPath-filler n->m refl m->s))

        mˡ=m : Square (reflᵉ (meridian a₁ l)) (meridian a₁) (sym n->m) m->s
        mˡ=m = ▪ᵀ msq

        q₂=m : q₂ == (meridian a₁)
        q₂=m = ▪comp (\i j -> meridian a₁ l) q₂=mˡ mˡ=m (\i -> n->m) (\i -> m->s)

        q₂=m-filler :
          PathP (\k -> Square (q₂=mˡ (~ k)) (mˡ=m k)
                              (\i -> n->m (~ k))
                              (\i -> m->s k))
                (\i j -> meridian a₁ l)
                q₂=m
        q₂=m-filler = ▪comp-filler (\i j -> meridian a₁ l) _ _ _ _


        q₂=m-simp₁ : PartialP {a = ℓ} l (\{ (l = i1) -> q₂=m == compPath-refl-right n->m })
        q₂=m-simp₁ (l = i1) = q₂=m=q₂-m' ∙∙ q₂-m-path₂ ∙∙ (transP-sym step₃ (symP step₁))
          where

          msq-path₁ :
            PathP (\k -> Square (\i -> (meridian a₁ (k ∧ ~ i)))
                                (reflᵉ (meridian a₁ k))
                                (reflᵉ (meridian a₁ k))
                                (\j -> (meridian a₁ (k ∧ j))))
              (\_ _ -> north) msq
          msq-path₁ = ▪comp-filler _ _ _ _ _


          msq-path₂ :
            PathP (\k -> Square (\i -> (meridian a₁ (k ∧ ~ i)))
                                (reflᵉ (meridian a₁ k))
                                (reflᵉ (meridian a₁ k))
                                (\j -> (meridian a₁ (k ∧ j))))
              (\_ _ -> north) (\i j -> meridian a₁ (~ j ∨ i))
          msq-path₂ k i j = meridian a₁ (k ∧ (~ j ∨ i))

          msq-path : msq == (\i j -> meridian a₁ (~ j ∨ i))
          msq-path = transP-sym (symP msq-path₁) msq-path₂


          check-q₂=m :
            q₂=m == ▪comp (\i j -> south) q₂=mˡ (\i j -> msq j i) (\i j -> meridian a₁ j) (\i j -> south)
          check-q₂=m = refl

          q₂=m' : q₂ == (meridian a₁)
          q₂=m' = ▪comp (\i j -> south) q₂=mˡ
                        (\i j -> meridian a₁ (~ i ∨ j))
                        (\i j -> meridian a₁ j)
                        (\i j -> south)

          q₂=m=q₂-m' :
            q₂=m == q₂=m'
          q₂=m=q₂-m' k =
            ▪comp (\i j -> south) q₂=mˡ
                  (\i j -> msq-path k j i)
                  (\i j -> meridian a₁ j)
                  (\i j -> south)



          q₂=m'₂ : q₂ == (meridian a₁)
          q₂=m'₂ = ▪comp q₂=mˡ (\i j -> q₂ j)
                               (\i j -> meridian a₁ (~ i ∨ j))
                               (\i j -> meridian a₁ (i ∧ j))
                               (\i j -> south)


          q₂-m-path₂ : q₂=m' == q₂=m'₂
          q₂-m-path₂ k =
            ▪comp (\i j -> q₂=mˡ (i ∨ ~ k) j)
                  (\i j -> q₂=mˡ (i ∧ ~ k) j)
                  (\i j -> meridian a₁ (~ i ∨ j))
                  (\i j -> meridian a₁ ((i ∨ ~ k) ∧ j))
                  (\i j -> south)




          check-q₂=mˡ : Square q₂ (reflᵉ south) (meridian a₁) (reflᵉ south)
          check-q₂=mˡ = q₂=mˡ

          check-q₂=mˡ₂ : (symP q₂=mˡ) == (doubleCompPath-filler (meridian a₁) refl refl)
          check-q₂=mˡ₂ = refl

          check-rhs : compPath-refl-right n->m == (compPath-refl-right (meridian a₁))
          check-rhs = refl

          step₁ :
            PathP (\k -> Square (meridian a₁ >=> refl)
                                (\i -> (meridian a₁ (i ∨ k)))
                                (\j -> meridian a₁ (j ∧ k))
                                (reflᵉ south))
              (compPath-refl-right (meridian a₁))
              q₂=mˡ
          step₁ i j = compPath/doubleCompPath-filler (meridian a₁) i (~ j)


          step₃ :
            PathP (\k -> Square (meridian a₁ >=> refl)
                                (\i -> (meridian a₁ (i ∨ k)))
                                (\j -> meridian a₁ (j ∧ k))
                                (reflᵉ south))
              q₂=m'₂
              q₂=mˡ
          step₃ = symP (▪comp-filler _ _ _ _ _)



        stage₀ : Square q₁ q₂ refl (meridian a₁)
        stage₀ = (\_ -> n->m) ▪v refl ▪v msq

        stage₁ : Square q₁ q₂ refl (meridian a₁)
        stage₁ = ▪comp (\_ -> reflᵉ (meridian a₁ l))
                       q₁=mˡ
                       (symP q₂=mˡ)
                       (\_ -> n->m) msq

        step₁ : stage₀ == stage₁
        step₁ = ▪v=▪comp (\_ -> n->m) refl msq

        mid₁ : Square (reflᵉ (meridian a₁ l)) refl refl refl
        mid₁ _ _ = (meridian a₁ l)

        mid₂ : Square (reflᵉ (meridian a₁ l)) refl refl refl
        mid₂ = ▪comp ans-sq mˡ=n (symP mˡ=m) (\i j -> mˡ=n j i) (\i j -> mˡ=m (~ j) i)

        mid₃ : Square (reflᵉ (meridian a₁ l)) refl refl refl
        mid₃ = ▪comp
          (\i j -> meridian a₁ (i ∧ j))
          (\i j -> n->m (~ i))
          (\i j -> msq j (~ i))
          (\i j -> n->m (~ j))
          (\i j -> msq i (~ j))


        mid₄ : Square (sym n->m) (reflᵉ north) (sym n->m) (reflᵉ north)
        mid₄ =
          ▪comp
          (\i j -> north)
          (\i j -> n->m (~ i ∧ ~ j))
          (\i j -> north)
          (\i j -> n->m (~ i ∧ ~ j))
          (\i j -> north)

        mid₅ : Square (reflᵉ (meridian a₁ l)) refl refl refl
        mid₅ =
          ▪comp
          (\i j -> meridian a₁ l)
          (\i j -> meridian a₁ l)
          (\i j -> meridian a₁ l)
          (\i j -> meridian a₁ l)
          (\i j -> meridian a₁ l)


        msq-p : PathP (\k -> Square (\i -> n->m (k ∧ (~ i)))
                                    (\i -> meridian a₁ (k ∧ (l ∨ i)))
                                    (\j -> n->m k)
                                    (\j -> meridian a₁ (k ∧ j)))
                      (\_ _ -> north) msq
        msq-p = ▪comp-filler (\_ _ -> north) _ _ _ _

        mid₃=mid₄ :
          PathP (\k -> Square (\i -> n->m (~ i ∨ ~ k))
                              (\i -> n->m (~ k))
                              (\j -> n->m (~ j ∨ ~ k))
                              (\j -> n->m (~ k)))
                mid₃ mid₄
        mid₃=mid₄ k =
          ▪comp
            (\i j -> meridian a₁ ((i ∧ j) ∧ ~ k))
            (\i j -> n->m (~ i ∧ (~ j ∨ ~ k)))
            (\i j -> msq-p (~ k) j (~ i))
            (\i j -> n->m (~ j ∧ (~ i ∨ ~ k)))
            (\i j -> msq-p (~ k) i (~ j))

        mid₅=mid₄ :
          PathP (\k -> Square (\i -> n->m (~ i ∨ ~ k))
                              (\i -> n->m (~ k))
                              (\j -> n->m (~ j ∨ ~ k))
                              (\j -> n->m (~ k)))
                mid₅ mid₄
        mid₅=mid₄ k =
          ▪comp
          (\i j -> n->m (~ k))
          (\i j -> n->m ((~ i ∧ ~ j) ∨ ~ k))
          (\i j -> n->m (~ k))
          (\i j -> n->m ((~ i ∧ ~ j) ∨ ~ k))
          (\i j -> n->m (~ k))

        mid₃=mid₅ : mid₂ == mid₅
        mid₃=mid₅ = transP-sym mid₃=mid₄ (symP mid₅=mid₄)

        mid₅=mid₁ : mid₅ == mid₁
        mid₅=mid₁ = ▪comp-refl (\_ _ -> meridian a₁ l)



        mid₂=mid₃ : mid₂ == mid₃
        mid₂=mid₃ = refl



        tp₁ : Square q₁ q₂ refl (meridian a₁) ==
              Square (reflᵉ (meridian a₁ l)) refl refl refl
        tp₁ k = Square (q₁=mˡ k) (q₂=mˡ k) (mˡ=n (~ k)) (mˡ=m (~ k))

        tp₂ : Square (reflᵉ (meridian a₁ l)) refl refl refl ==
              Square refl (meridian a₁) refl (meridian a₁)
        tp₂ k = Square (mˡ=n k) (mˡ=m k) (mˡ=n k) (mˡ=m k)

        tp₃ : Square q₁ q₂ refl (meridian a₁) ==
              Square refl (meridian a₁) refl (meridian a₁)
        tp₃ k = Square (q₁=n k) (q₂=m k) refl (meridian a₁)

        tp₁₂=tp₃ : tp₁ >=> tp₂ == tp₃
        tp₁₂=tp₃ =
          sym (cong-∙∙ B->S bp₁ refl bp₂) >=> cong (cong B->S) bp₁₂=bp₃
          where
          B : Type ℓ
          B = Σ[ v₁ ∈ Susp A ] Σ[ v₂ ∈ Susp A ] Σ[ v₃ ∈ Susp A ] Σ[ v₄ ∈ Susp A ]
                 (v₁ == v₂ × v₃ == v₄ × v₁ == v₃ × v₂ == v₄)

          B->S : B -> Type ℓ
          B->S (_ , _ , _ , _ , e₁ , e₂ , e₃ , e₄) = Square e₁ e₂ e₃ e₄


          b₀ : B
          b₀ = north , north , north , south , q₁ , q₂ , refl , (meridian a₁)
          b₁ : B
          b₁ = meridian a₁ l , meridian a₁ l , meridian a₁ l , meridian a₁ l ,
               refl , refl , refl , refl
          b₂ : B
          b₂ = north , north , north , south ,
               refl , meridian a₁ , refl , meridian a₁

          bp₁ : b₀ == b₁
          bp₁ k = n->m k , n->m k , n->m k , m->s (~ k) ,
                  q₁=mˡ k , q₂=mˡ k , mˡ=n (~ k) , mˡ=m (~ k)

          bp₂ : b₁ == b₂
          bp₂ k = n->m (~ k) , n->m (~ k) , n->m (~ k) , m->s k ,
                  mˡ=n k , mˡ=m k , mˡ=n k , mˡ=m k

          bp₃ : b₀ == b₂
          bp₃ k = north , north , north , south ,
                  q₁=n k , q₂=m k , refl , (meridian a₁)

          bp₁₂-path : Square (bp₁ >=> bp₂) (reflᵉ b₁) bp₁ (sym bp₂)
          bp₁₂-path = symP (doubleCompPath-filler bp₁ refl bp₂)

          bp₃-path : Square (reflᵉ b₁) bp₃ (sym bp₁) bp₂
          bp₃-path k j =
            n->m (~ k) , n->m (~ k) , n->m (~ k) , m->s k ,
            (\i -> q₁=n-filler k j i) ,
            (\i -> q₂=m-filler k j i) ,
            refl ,
            (\j -> msq j k)

          bp₁₂=bp₃ : bp₁ >=> bp₂ == bp₃
          bp₁₂=bp₃ = transP-sym bp₁₂-path bp₃-path


        s₁=mid₁ : PathP (\k -> tp₁ k) stage₁ mid₁
        s₁=mid₁ = symP (▪comp-filler mid₁ _ _ _ _)

        mid₁=mid₂ : mid₁ == mid₂
        mid₁=mid₂ = sym mid₅=mid₁ >=> sym mid₃=mid₅


        mid₂=ans : PathP (\k -> tp₂ k) mid₂ ans-sq
        mid₂=ans = symP (▪comp-filler ans-sq _ _ _ _)

        s₁=mid₂ : PathP (\k -> tp₁ k) stage₁ mid₂
        s₁=mid₂ = transP-left s₁=mid₁ mid₁=mid₂


        s₁=ans' : PathP (\k -> (tp₁ >=> tp₂) k) stage₁ ans-sq
        s₁=ans' = transP s₁=mid₂ mid₂=ans

        s₁=ans : PathP (\k -> tp₃ k) stage₁ ans-sq
        s₁=ans = transport (\l -> PathP (\k -> tp₁₂=tp₃ l k) stage₁ ans-sq) s₁=ans'

        stage₂ : Square refl (meridian a₁) refl (meridian a₁)
        stage₂ = ▪comp stage₁ (sym q₁=n) q₂=m (\_ -> refl) (\_ -> refl)

        step₂ : PathP (\k -> Square (q₁=n k) (q₂=m k) refl (meridian a₁))
                      stage₁ stage₂
        step₂ = ▪comp-filler stage₁ _ _ _ _


        check-sq : sq == stage₀
        check-sq = refl

      sq-path : PathP (\k -> Square (q₁=n k) (q₂=m k) refl (meridian a₁))
                      sq ans-sq
      sq-path = transP-right step₁ s₁=ans

      edge₀ : Type ℓ
      edge₀ = encode₃.edge a₁ sq l

      edge₁ : Type ℓ
      edge₁ = encode₃.edge a₁ ans-sq l

      edge₂ : Type ℓ
      edge₂ =
        (hcomp (\k -> \{ (l = i0) -> north-code (compPath-refl-right n->m k)
                       ; (l = i1) -> south-code (compPath-refl-right n->m k)
                       })
          (encode₃.edge a₁ sq l))

      edge₂' : Type ℓ
      edge₂' =
        (hcomp (\k -> \{ (l = i0) -> north-code (q₁=n k)
                       ; (l = i1) -> south-code (q₂=m k)
                       })
          (encode₃.edge a₁ sq l))

      edge₂=edge₂' : edge₂ == edge₂'
      edge₂=edge₂' j =
        (hcomp (\k -> \{ (l = i0) -> north-code (q₁=n-simp₀ 1=1 (~ j) k)
                       ; (l = i1) -> south-code (q₂=m-simp₁ 1=1 (~ j) k)
                       })
          (encode₃.edge a₁ sq l))


      edge₃ : Type ℓ
      edge₃ =
        (hcomp (\k -> \{ (l = i0) -> north-code refl
                       ; (l = i1) -> south-code n->m
                       })
          (encode₃.edge a₁ ans-sq l))

      edge₃' : Type ℓ
      edge₃' = encode₃.edge a₁ ans-sq l


      edge₂'=edge₃ : edge₂' == edge₃
      edge₂'=edge₃ j =
        (hcomp (\k -> \{ (l = i0) -> north-code (q₁=n (k ∨ j))
                       ; (l = i1) -> south-code (q₂=m (k ∨ j))
                       })
          (encode₃.edge a₁ (sq-path j) l))

      edge₃'=edge₃ : edge₃' == edge₃
      edge₃'=edge₃ k =
        hfill (\k -> \{ (l = i0) -> north-code refl
                      ; (l = i1) -> south-code n->m
                      })
          (inS (encode₃.edge a₁ ans-sq l)) k

      edge₂=edge₃' : edge₂ == edge₃'
      edge₂=edge₃' =
        edge₂=edge₂' ∙∙
        edge₂'=edge₃ ∙∙
        sym edge₃'=edge₃


      edge-path : (encode₃.edge a₁ sq l) == (encode₃.edge a₁ ans-sq l)
      edge-path k = encode₃.edge a₁ (sq-path k) l


  opaque
    encode₄-path : ∀ a₁ ->
      Path (north-code refl == south-code (meridian a₁))
        (\i -> encode₄ (meridian a₁ i) (\j -> meridian a₁ (i ∧ j)))
        (\i -> encode₃.edge a₁ (\i j -> meridian a₁ (i ∧ j)) i)
    encode₄-path a₁ =
      ▪comp (\k i -> edge₂=edge₃' a₁ i k)
            (\_ i -> edge₂=edge₃' a₁ i i0)
            (\_ i -> edge₂=edge₃' a₁ i i1)
            (\i j -> ∙∙-refl {x = (north-code refl)} (~ j) i)
            (\i j -> ∙∙-refl {x = (south-code (meridian a₁))} j i)

    tencode₄-path : ∀ a₁ ->
      Path (north-code refl -> south-code (meridian a₁))
        (transport (\i -> encode₄ (meridian a₁ i) (\j -> meridian a₁ (i ∧ j))))
        (to-south (meridian a₁) a₁ ∘ from-north₃ (meridian a₁) a₁ (\i j -> meridian a₁ (i ∧ j)))
    tencode₄-path a₁ =
      (\k -> transport (encode₄-path a₁ k)) >=>
      transport-ua
        (to-south p₂ a₁ ∘ from-north₃ p₂ a₁ sq ,
         ∘-isEquiv (isEquiv-to-south p₂ a₁) (isEquiv-from-north₃ p₂ a₁ sq))
      where
      p₁ : Path (Susp A) north north
      p₁ = refl
      p₂ : Path (Susp A) north south
      p₂ = meridian a₁
      sq : Square p₁ p₂ refl (meridian a₁)
      sq i j = meridian a₁ (i ∧ j)




  module _ (magic : Magic) where
    isCenter-encode₄-north : ∀ (p : north == north) (v : encode₃ north p) -> encode₄-center north p == v
    isCenter-encode₄-north =
      (\p -> ∥ₙ-elim (\fib -> isOfHLevelPath (suc (suc (n + n)))
                              (isOfHLevel-Squashₙ (suc (suc (n + n)))) (encode₄-center north p) fib)
                     (handle p))
      where

      handle : ∀ (p : north == north) (v : (fiber (ΩΣf A∙) p)) -> encode₄-center north p == ∣ v ∣
      handle p (a , r) = ans
        where

        p₀ : Path (Σ (Susp A) (north ==_)) (north , refl) (north , (meridian a >=> sym (meridian ★A)))
        p₀ i = (meridian a >=> sym (meridian ★A)) i ,
               (\j -> (meridian a >=> sym (meridian ★A)) (j ∧ i))

        p₁ : Path (Σ (Susp A) (north ==_)) (north , refl) (south , (meridian a))
        p₁ i = meridian a i , (\j -> meridian a (j ∧ i))

        p₂ : Path (Σ (Susp A) (north ==_)) (south , (meridian a)) (south , (meridian a >=> refl))
        p₂ i = south , compPath-refl-right (meridian a) (~ i)

        p₃ : Path (Σ (Susp A) (north ==_)) (south , (meridian a >=> refl))
                                           (north , (meridian a >=> sym (meridian ★A)))
        p₃ i = meridian ★A (~ i) , (meridian a >=> (\j -> (meridian ★A (~ j ∨ ~ i))))

        p₄ : Path (Σ (Susp A) (north ==_)) (north , refl) (north , (meridian a >=> sym (meridian ★A)))
        p₄ = p₁ ∙∙ p₂ ∙∙ p₃

        p₀=p₄ : p₀ == p₄
        p₀=p₄ = isOfHLevelPath 1 (isContr->isProp (isContr-singleton north)) _ _ p₀ p₄


        step₁ :
          transport (\i -> (encode₄' (p₀ i))) (∣ ★A , compPath-sym (meridian ★A) ∣) ==
          transport (\i -> (encode₄' (p₃ i)))
            (transport (\i -> (encode₄' (p₂ i)))
              (transport (\i -> (encode₄' (p₁ i))) (∣ ★A , compPath-sym (meridian ★A) ∣)))
        step₁ =
          (\j -> transport (\i -> (encode₄' (p₀=p₄ j i))) (∣ ★A , compPath-sym (meridian ★A) ∣)) >=>
          (\j -> transport (\i -> (cong-∙∙ encode₄' p₁ p₂ p₃ j i)) (∣ ★A , compPath-sym (meridian ★A) ∣)) >=>
          transport-∙∙ (\i -> (encode₄' (p₁ i))) (\i -> (encode₄' (p₂ i))) (\i -> (encode₄' (p₃ i)))
                       (∣ ★A , compPath-sym (meridian ★A) ∣)


        step₂ :
          (transport (\i -> (encode₄' (p₂ i)))
            (transport (\i -> (encode₄' (p₁ i))) (∣ ★A , compPath-sym (meridian ★A) ∣))) ==
          (transport (\i -> (encode₄' (p₃ (~ i)))) ∣ (a , refl) ∣)
        step₂ = ?


        base : transport (\i -> (encode₄' (p₀ i)))
                 (∣ ★A , compPath-sym (meridian ★A) ∣) ==
               ∣ (a , refl) ∣
        base =
          step₁ >=>
          cong (transport (\i -> (encode₄' (p₃ i)))) step₂ >=>
          transport-sym (\i -> (encode₄' (p₃ (~ i)))) _






        Ans : ∀ p' (r' : meridian a >=> sym (meridian ★A) == p') -> Type _
        Ans p' r' = encode₄-center north p' == ∣ (a , r') ∣

        ans : encode₄-center north p == ∣ (a , r) ∣
        ans = J Ans base r





{-
  encode₃-m-mcb : (a₁ : A) ->
    PathP (\i ->
      Square (reflᵉ (meridian a₁ i)) (meridian a₁) (\j -> meridian a₁ (i ∧ ~ j)) (\j -> meridian a₁ (i ∨ j)))
      (encode₃-m.msq a₁ i0 (\j -> meridian a₁ (i0 ∧ j)))
      (encode₃-m.msq a₁ i1 (\j -> meridian a₁ (i1 ∧ j)))
  encode₃-m-mcb a₁ i = encode₃-m.msq a₁ i (\j -> meridian a₁ (i ∧ j))


  module _ (a₁ : A) (l : I) (magic : Magic) where
    private
      n->l : north == meridian a₁ l
      n->l j = meridian a₁ (l ∧ j)
      l->s : meridian a₁ l == south
      l->s j = meridian a₁ (l ∨ j)

      open encode₃-m a₁ l n->l


    q₁=refl : q₁ == (reflᵉ north)
    q₁=refl i =
      transp (\k -> north == n->l (~ i ∧ ~ k)) (~ l ∨ i)
             (\j -> n->l (~ i ∧ j))

    q₂=m : q₂ == (meridian a₁)
    q₂=m i =
      transp (\k -> north == l->s (i ∨ k)) (i ∨ l)
             (\j -> meridian a₁ ((i ∨ l) ∧ j))


    encode₃-m-sq-simp :
      PathP (\k -> Square (q₁=refl k) (q₂=m k)
                          refl (meridian a₁))
            (encode₃-m.sq a₁ l (\j -> meridian a₁ (l ∧ j)))
            (\i j -> meridian a₁ (i ∧ j))
    encode₃-m-sq-simp = ?
      where

      edge₁ : Square (\ll -> north)
                     (\ll -> transp (\k -> north == n->l (~ k ∨ ~ ll)) (~ l ∨ ~ ll) n->l i1)
                     (\jj -> n->l jj)
                     (\jj -> (transp (\k -> north == n->l (~ k)) (~ l) n->l) jj)
      edge₁ jj ll = (transp (\k -> north == n->l (~ k ∨ ~ ll)) (~ l ∨ ~ ll) n->l) jj


      edge₂ : Square (\ll -> north)
                     (\ll -> (transp (\k -> north == l->s (k ∧ ll)) (l ∨ ~ ll) n->l) i1)
                     (\jj -> n->l jj)
                     (\jj -> (transp (\k -> north == l->s (k)) (l) n->l) jj)
      edge₂ jj ll = (transp (\k -> north == l->s (k ∧ ll)) (l ∨ ~ ll) n->l) jj



      sq' : Square q₁ q₂ refl (meridian a₁)
      sq' =
        ▪comp (\ii jj -> n->l jj) (\ii jj -> edge₁ jj (~ ii))
                                  (\ii jj -> edge₂ jj ii)
                                  (\_ _ -> north)
                                  (\ii jj -> msq jj ii)


      sq'₂ : Square refl (meridian a₁) refl (meridian a₁)
      sq'₂ = ▪comp sq' (sym q₁=refl) q₂=m (\_ -> refl) (\_ -> refl)







      check-sq : sq' == sq
      check-sq = refl





-}



{-
  module _ (magic : Magic) where
    isCenter-encode₂-north : ∀ (p : north == north) (v : encode₂ north p) -> encode₂-center north p == v
    isCenter-encode₂-north =
      (\p -> ∥ₙ-elim (\fib -> isOfHLevelPath (suc (suc (n + n)))
                              (isOfHLevel-Squashₙ (suc (suc (n + n)))) (encode₂-center north p) fib)
                     (handle p))
      where

      handle : ∀ (p : north == north) (v : (fiber (ΩΣf A∙) p)) -> encode₂-center north p == ∣ v ∣
      handle p (a , r) = ans
        where

        p₀ : Path (Σ (Susp A) (north ==_)) (north , refl) (north , (meridian a >=> sym (meridian ★A)))
        p₀ i = (meridian a >=> sym (meridian ★A)) i ,
               (\j -> (meridian a >=> sym (meridian ★A)) (j ∧ i))

        p₁ : Path (Σ (Susp A) (north ==_)) (north , refl) (south , (meridian a))
        p₁ i = meridian a i , (\j -> meridian a (j ∧ i))

        p₂ : Path (Σ (Susp A) (north ==_)) (south , (meridian a)) (south , (meridian a >=> refl))
        p₂ i = south , compPath-refl-right (meridian a) (~ i)

        p₃ : Path (Σ (Susp A) (north ==_)) (south , (meridian a >=> refl))
                                           (north , (meridian a >=> sym (meridian ★A)))
        p₃ i = meridian ★A (~ i) , (meridian a >=> (\j -> (meridian ★A (~ j ∨ ~ i))))

        p₄ : Path (Σ (Susp A) (north ==_)) (north , refl) (north , (meridian a >=> sym (meridian ★A)))
        p₄ = p₁ ∙∙ p₂ ∙∙ p₃

        p₀=p₄ : p₀ == p₄
        p₀=p₄ = isOfHLevelPath 1 (isContr->isProp (isContr-singleton north)) _ _ p₀ p₄


        step₁ :
          transport (\i -> (encode₂' (p₀ i))) (∣ ★A , compPath-sym (meridian ★A) ∣) ==
          transport (\i -> (encode₂' (p₃ i)))
            (transport (\i -> (encode₂' (p₂ i)))
              (transport (\i -> (encode₂' (p₁ i))) (∣ ★A , compPath-sym (meridian ★A) ∣)))
        step₁ =
          (\j -> transport (\i -> (encode₂' (p₀=p₄ j i))) (∣ ★A , compPath-sym (meridian ★A) ∣)) >=>
          (\j -> transport (\i -> (cong-∙∙ encode₂' p₁ p₂ p₃ j i)) (∣ ★A , compPath-sym (meridian ★A) ∣)) >=>
          transport-∙∙ (\i -> (encode₂' (p₁ i))) (\i -> (encode₂' (p₂ i))) (\i -> (encode₂' (p₃ i)))
                       (∣ ★A , compPath-sym (meridian ★A) ∣)


        base : transport (\i -> (encode₂' (p₀ i)))
                 (∣ ★A , compPath-sym (meridian ★A) ∣) ==
               ∣ (a , refl) ∣
        base = magic






        Ans : ∀ p' (r' : meridian a >=> sym (meridian ★A) == p') -> Type _
        Ans p' r' = encode₂-center north p' == ∣ (a , r') ∣

        ans : encode₂-center north p == ∣ (a , r) ∣
        ans = J Ans base r

-}
-}
