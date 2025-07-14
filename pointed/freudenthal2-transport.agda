{-# OPTIONS --cubical --safe --exact-split #-}

module pointed.freudenthal2-transport where


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

open import pointed.suspension
open import pointed.freudenthal2

{-

module _ {ℓ ℓf : Level}
         {A : I -> Type ℓ} {a₀ : A i0} {b₀ : A i0} {b₁ : A i1} {a₁ : A i1}
         (p : Path (A i0) a₀ b₀) (q : PathP A b₀ b₁) (r : Path (A i1) b₁ a₁)
         (f : (i : I) -> A i -> Type ℓf)
         (v₀ : f i0 a₀)
  where
  private
    fp₀ : f i0 a₀ == f i0 b₀
    fp₀ i = f i0 (p i)
    fp₁ : f i0 b₀ == f i1 b₁
    fp₁ i = f i (q i)
    fp₂ : f i1 b₁ == f i1 a₁
    fp₂ i = f i1 (r i)

    v₁ : f i0 b₀
    v₁ = transport (\i -> f i0 (p i)) v₀
    v₂ : f i1 b₁
    v₂ = transport (\i -> f i (q i)) v₁
    v₃ : f i1 a₁
    v₃ = transport (\i -> f i1 (r i)) v₂



  opaque
    transport-transP-mid :
      transport (\i -> f i (transP-mid p q r i)) v₀ ==
      transport (\i -> fp₂ i)
       (transport (\i -> fp₁ i)
         (transport (\i -> fp₀ i) v₀))
    transport-transP-mid =
      transP-sym
        (symP (transport-filler (\i -> f i (transP-mid p q r i)) v₀))
        v₀=v₃
      where
      fpp₁ : (fp₀ >=> (fp₁ >=> fp₂)) == (fp₀ ∙∙ fp₁ ∙∙ fp₂)
      fpp₁ = sym (doubleCompPath-assoc-right fp₀ fp₁ fp₂)

      fpp₂ : (fp₀ ∙∙ fp₁ ∙∙ fp₂) == (\i -> f i (transP-mid p q r i))
      fpp₂ = transP-sym (symP ls) rs
        where
        ls : Square fp₁ (fp₀ ∙∙ fp₁ ∙∙ fp₂) (sym fp₀) fp₂
        ls = doubleCompPath-filler fp₀ fp₁ fp₂

        rs : Square fp₁ (\j -> f j (transP-mid p q r j))
                    (sym fp₀) fp₂
        rs i j = f j (transP-mid-filler p q r i j)



      vp₀ : PathP (\i -> fp₀ i) v₀ v₁
      vp₀ j = transp (\i -> f i0 (p (i ∧ j))) (~ j) v₀
      vp₁ : PathP (\i -> fp₁ i) v₁ v₂
      vp₁ j = transp (\i -> f (i ∧ j) (q (i ∧ j))) (~ j) v₁
      vp₂ : PathP (\i -> fp₂ i) v₂ v₃
      vp₂ j = transp (\i -> f i1 (r (i ∧ j))) (~ j) v₂

      v₀=v₃ : PathP (\i -> f i (transP-mid p q r i)) v₀ v₃
      v₀=v₃ = transport (\k -> PathP (\i -> ((fpp₁ >=> fpp₂) k i)) v₀ v₃)
                        (transP vp₀ (transP vp₁ vp₂))






module _ {ℓ : Level} (A∙@(A , ★A) : Type∙ ℓ) {n : Nat} (cA : isConnectedₙ n A) where
  open freudenthal A∙ cA

  private

    module _ (a : A) where
      tp : PathP (\i -> (north == meridian a i) -> Type ℓ)
                 (encode north)
                 (\q -> encode north (transport (\i -> north == meridian a (~ i)) q))
      tp j q = encode north (transp (\i -> north == meridian a (~ i ∧ j)) (~ j) q)




  t₀ : encode north refl
  t₀ = (∣ ★A , compPath-sym (meridian ★A) ∣)

  module _ (a : A) where
    t₁ : encode south (meridian a)
    t₁ = transport (\i -> (encode (meridian a i) (\j -> (meridian a) (i ∧ j)))) t₀

    convert₂ : encode south (meridian a) -> encode south (meridian a >=> refl)
    convert₂ = transport (\i -> (encode south (\j -> compPath-refl-right (meridian a) (~ i) j)))

    t₂ : encode south (meridian a >=> refl)
    t₂ = convert₂ t₁

    module _ where
      private
        pp : PathP (\i -> north == meridian a i) refl (meridian a)
        pp = (\i j -> (meridian a) (i ∧ j))

      sub-t₁ : encode north (transport (\i -> north == meridian a (~ i)) (meridian a))
      sub-t₁ =
        (transport (\j -> (tp a) j (pp j))
          (∣ ★A , compPath-sym (meridian ★A) ∣))

      sub-t₁' : encode north (transport (\i -> north == meridian a (~ i)) (meridian a))
      sub-t₁' =
        (transp (\j -> (tp a) j (pp j)) i0
          (∣ ★A , compPath-sym (meridian ★A) >=> refl ∣))

      sub-t₁-step₁ : sub-t₁ == sub-t₁'
      sub-t₁-step₁ k =
        (transp (\j -> (tp a) j (pp j)) i0
          (∣ ★A , compPath-refl-right (compPath-sym (meridian ★A)) (~ k) ∣))

      sub-t₁'₂-coherence :
         (meridian ★A >=> sym (meridian ★A) == (transport (\i -> north == meridian a (~ i)) (meridian a)))
      sub-t₁'₂-coherence = (compPath-sym (meridian ★A)) >=> inner-left
        where
        inner-left : refl == (transport (\i -> north == meridian a (~ i)) (meridian a))
        inner-left k = transp (\i -> north == meridian a (k ∧ ~ i)) (~ k) (\i -> meridian a (i ∧ k))

      sub-t₁'₂ : encode north (transport (\i -> north == meridian a (~ i)) (meridian a))
      sub-t₁'₂ = (∣ ★A , sub-t₁'₂-coherence ∣)

      sub-t₁-step₂ : sub-t₁' == sub-t₁'₂
      sub-t₁-step₂ k =
        (transp (\j -> (tp a) (k ∨ j) (pp (k ∨ j))) k (∣ ★A , (compPath-sym (meridian ★A)) >=> inner-left ∣))
        where
        inner-left : refl == _
        inner-left l = transp (\i -> north == meridian a (l ∧ k ∧ ~ i)) (~ l ∨ ~ k) (\i -> meridian a (i ∧ l ∧ k))


      sub-t₁-steps : sub-t₁ == sub-t₁'₂
      sub-t₁-steps = sub-t₁-step₁ >=> sub-t₁-step₂

      t₁' : (south-code (meridian a))
      t₁' = (to-south-raw (meridian a) ★A a (from-north-coherence (meridian a) a ★A sub-t₁'₂-coherence))

      path-t₁ : t₁ == t₁'
      path-t₁ =
        step₁ _ _ pp t₀ >=>
        cong (\p ->
                transport (\i -> ns-path (meridian a) a i)
                  (transport (\j -> (tp a) j (pp j)) p))
             (transportRefl t₀) >=>
        cong (\p -> transport (\i -> ns-path (meridian a) a i) p)
          sub-t₁-steps >=>
        (\i -> transport-ua (ns (meridian a) a , isEquiv-ns (meridian a) a) i sub-t₁'₂)
        where

          module _
            (p₀ : north == north) (p₁ : north == south)
            (pp : PathP (\i -> north == meridian a i) p₀ p₁)
            (v : encode north p₀)
            where
            step₁ :
              (transport (\i -> transP-mid refl (tp a)
                (\i q -> ns-path q a i) i (pp i)) v) ==
              (transport (\i -> ns-path p₁ a i)
                (transport (\j -> (tp a) j (pp j))
                  (transport (\i -> (encode north) p₀) v)))
            step₁ = transport-transP-mid (reflᵉ (encode north)) (tp a) (\i q -> ns-path q a i) (\i e -> e (pp i)) v


    t₂'₀ : south-code (meridian a >=> refl)
    t₂'₀ = convert₂ t₁'

    t₂'₁ : south-code (meridian a >=> refl)
    t₂'₁ =
      (to-south-raw m' ★A a (from-north-coherence m' a ★A
        (transport (\i -> (meridian ★A >=> sym (meridian ★A) ==
                          (transport (\j -> north == meridian a (~ j))
                            (\j -> compPath-refl-right (meridian a) (~ i) j))))
          sub-t₁'₂-coherence)))
      where

      m' : north == south
      m' = meridian a >=> refl

    t₂'₀=t₂'₁ : t₂'₀ == t₂'₁
    t₂'₀=t₂'₁ k =
      transp (\i -> (encode south (\j -> compPath-refl-right (meridian a) (~ i ∧ ~ k) j))) k
        (to-south-raw m' ★A a (from-north-coherence m' a ★A
          (transp (\i -> (meridian ★A >=> sym (meridian ★A) ==
                         (transport (\j -> north == meridian a (~ j))
                           (\j -> compPath-refl-right (meridian a) (~ i ∨ ~ k) j)))) (~ k)
            sub-t₁'₂-coherence)))

      where
      m' : north == south
      m' j = compPath-refl-right (meridian a) (~ k) j


    sub-t₂'₁-coherence :
       (meridian ★A >=> sym (meridian ★A) == (transport (\i -> north == meridian a (~ i)) (meridian a >=> refl)))
    sub-t₂'₁-coherence =
      transport (\i -> (meridian ★A >=> sym (meridian ★A) ==
                       (transport (\j -> north == meridian a (~ j))
                         (\j -> compPath-refl-right (meridian a) (~ i) j))))
       sub-t₁'₂-coherence

    -- Unused so far
    sub-t₂'-coherence :
       (meridian ★A >=> sym (meridian ★A) == (transport (\i -> north == meridian a (~ i)) (meridian a >=> refl)))
    sub-t₂'-coherence = (compPath-sym (meridian ★A)) >=> inner-left
      where
      inner-left : refl == (transport (\i -> north == meridian a (~ i)) (meridian a >=> refl))
      inner-left k = transp (\i -> north == meridian a (k ∧ ~ i)) (~ k) (inner-left₂ k)
        where
        inner-left₂ : PathP (\k -> north == meridian a k) refl (meridian a >=> refl)
        inner-left₂ =
          transP-left (doubleCompPath-filler refl refl (meridian a))
                      (\k -> (\i -> meridian a (i ∧ k)) ∙∙
                             reflᵉ (meridian a k) ∙∙
                             (\i -> meridian a (k ∨ i)))

    t₂' : south-code (meridian a >=> refl)
    t₂' = to-south-raw (meridian a >=> refl) ★A a (from-north-coherence (meridian a >=> refl) a ★A sub-t₂'₁-coherence)

    path-t₂ : t₂ == t₂'
    path-t₂ = cong convert₂ path-t₁ >=> t₂'₀=t₂'₁


    encode₃ : south-code (meridian a >=> refl) -> north-code (meridian a >=> sym (meridian ★A))
    encode₃ =
      transport (\i -> encode (meridian ★A (~ i)) (meridian a >=> (\j -> meridian ★A (~ j ∨ ~ i))))

    module _  where
      private
        p₀ : north == north
        p₀ = meridian a >=> sym (meridian ★A)
        p₁ : north == south
        p₁ = meridian a >=> refl
        pp : PathP (\i -> north == meridian ★A i) p₀ p₁
        pp i = (meridian a >=> (\j -> meridian ★A (~ j ∨ i)))

        step₁ : (v : encode south p₁) ->
          (transport (\i -> transP-mid refl (tp ★A)
            (\i q -> ns-path q ★A i) (~ i) (pp (~ i))) v) ==
          (transport (\i -> (encode north) p₀)
            (transport (\j -> (tp ★A) (~ j) (pp (~ j)))
              (transport (\i -> ns-path p₁ ★A (~ i)) v)))
        step₁ v =
          transport-transP-mid (\i q -> ns-path q ★A (~ i)) (\i -> tp ★A (~ i)) (reflᵉ (encode north))
                               (\i e -> e (pp (~ i))) v

      encode-back-path :
        (v : encode south p₁) ->
          transport (\i -> encode (meridian ★A (~ i)) (pp (~ i))) v ==
          (transport (\j -> (tp ★A) (~ j) (pp (~ j)))
            (isEqInv (isEquiv-from-north p₁ ★A)
              (isEqInv (isEquiv-to-south p₁ ★A) v)))

      encode-back-path v =
        step₁ v >=>
        transportRefl
          (transport (\j -> (tp ★A) (~ j) (pp (~ j)))
            (transport (\i -> ns-path p₁ ★A (~ i)) v)) >=>
        cong (transport (\j -> (tp ★A) (~ j) (pp (~ j))))
          (cong (\p -> transport p v)
                (sym-ua (ns p₁ ★A , isEquiv-ns p₁ ★A)) >=>
           (\i -> transport-ua (equiv⁻¹ (ns p₁ ★A , isEquiv-ns p₁ ★A)) i v) >=>
           (\i -> isEquiv-ns-inv-path p₁ ★A i v))
-}
