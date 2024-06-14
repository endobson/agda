{-# OPTIONS --cubical --safe --exact-split #-}

module real.glue-function where

open import additive-group
open import additive-group.instances.real
open import apartness
open import base
open import equality
open import equivalence
open import functions
open import funext
open import hlevel
open import heyting-field.instances.real
open import nat
open import order
open import metric-space
open import metric-space.instances.real
open import order.instances.real
open import order.instances.nat
open import order.minmax
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-field
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.real
open import ordered-semiring
open import ordered-semiring.instances.real
open import rational
open import rational.order
open import real
open import real.derivative3
open import real.derivative3.slope
open import real.apartness
open import real.order
open import real.arithmetic.multiplication.inverse
open import real.epsilon-bounded
open import real.epsilon-bounded.base
open import real.rational
open import real.sequence.harmonic
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.subspace
open import relation hiding (U)
open import ring.implementations.real
open import semiring
open import sequence
open import sigma.base
open import subset
open import subset.subspace
open import truncation

ℝ#0S : Subtype ℝ ℓ-one
ℝ#0S x = x # 0# , isProp-#

ℝ#0 : Type₁
ℝ#0 = Subspace ℝ#0S

isIncreasing : {ℓS : Level} (S : Subtype ℝ ℓS) -> (f : Subspace S -> ℝ) -> Type (ℓ-max ℓ-one ℓS)
isIncreasing S f = ∀ (x∈@(x , _) y∈@(y , _) : Subspace S) -> x < y -> f x∈ < f y∈

isNonDecreasing : {ℓS : Level} (S : Subtype ℝ ℓS) -> (f : Subspace S -> ℝ) -> Type (ℓ-max ℓ-one ℓS)
isNonDecreasing S f = ∀ (x∈@(x , _) y∈@(y , _) : Subspace S) -> x ≤ y -> f x∈ ≤ f y∈

private
  distance-diff-< : {a b c : ℝ} -> distance a b < diff c b -> c < a
  distance-diff-< {a} {b} {c} dist-ab<diff-cb = diff-0<⁻ 0<diff-ca
    where
    diff-ab<diff-cb : diff a b < diff c b
    diff-ab<diff-cb = trans-≤-< max-≤-left dist-ab<diff-cb

    0<diff-ca : 0# < diff c a
    0<diff-ca =
      subst2 _<_ (diff-trans >=> +-inverse) diff-trans (+₂-preserves-< diff-ab<diff-cb)

  distance-diff-<' : {a b c : ℝ} -> distance a b < diff a c -> b < c
  distance-diff-<' {a} {b} {c} dist-ab<diff-ac = diff-0<⁻ 0<diff-bc
    where
    diff-ab<diff-ac : diff a b < diff a c
    diff-ab<diff-ac = trans-≤-< max-≤-left dist-ab<diff-ac

    0<diff-bc : 0# < diff b c
    0<diff-bc =
      subst2 _<_ (diff-trans >=> +-inverse) diff-trans (+₁-preserves-< diff-ab<diff-ac)




module _ (f : (x : ℝ⁺) -> ℝ)
         (nondec-f : isNonDecreasing ℝ⁺S f)
         {lim : ℝ} (isLimit-lim : isLimitAt ℝ⁺S f 0# lim)
  where
  isNonDecreasing-limit-≤ : (x : ℝ⁺) -> lim ≤ f x
  isNonDecreasing-limit-≤ x⁺@(x , 0<x) fx<lim =
    unsquash isPropBot (∥-bind2 handle (isLimitAt.limit-point isLimit-lim)
                                       (isLimitAt.distance<ε isLimit-lim (ε , 0<ε)))
    where
    ε = diff (f x⁺) lim
    0<ε = diff-0<⁺ fx<lim
    handle : LimitTestSeq ℝ⁺S 0# ->
             Σ[ δ⁺@(δ , _) ∈ ℝ⁺ ]
               (∀ (x'∈@(x' , _) : ℝ⁺) -> distance 0# x' < δ -> distance lim (f x'∈) < ε) ->
             ∥ Bot ∥
    handle t (δ⁺@(δ , 0<δ) , close) = ∥-map handle2 (isLimit.distance<ε t.isLimit-seq (δ2 , 0<δ2))
      where
      δ2 = min δ x
      0<δ2 = min-greatest-< 0<δ 0<x
      module t = LimitTestSeq t
      handle2 : ∀Largeℕ' (\i -> distance 0# (t.seq i) < δ2) -> Bot
      handle2 (n , seq-close) = fp≤fx fx<fp
        where
        p : ℝ
        p = t.seq n
        p⁺ : Subspace ℝ⁺S
        p⁺ = p , t.S-seq n

        p<x : p < x
        p<x =
          trans-=-< (sym diff-step >=> +-left-zero)
            (trans-≤-< max-≤-left (trans-<-≤ (seq-close n refl-≤) min-≤-right))

        fp≤fx : f p⁺ ≤ f x⁺
        fp≤fx = nondec-f p⁺ x⁺ (weaken-< p<x)

        dist-lim-fp<ε : distance lim (f p⁺) < ε
        dist-lim-fp<ε = close p⁺ (trans-<-≤ (seq-close n refl-≤) min-≤-left)

        dist-lim-fp<ε' : distance (f p⁺) lim < ε
        dist-lim-fp<ε' = trans-=-< distance-commute dist-lim-fp<ε

        diff-lim-fp<ε : diff lim (f p⁺) < ε
        diff-lim-fp<ε = trans-≤-< max-≤-left dist-lim-fp<ε

        fx<fp : f x⁺ < f p⁺
        fx<fp = distance-diff-< dist-lim-fp<ε'



module _
  (f : (x : ℝ⁺) -> ℝ)
  (nondec-f : isNonDecreasing ℝ⁺S f)
  {lim : ℝ}
  (isLimit-lim : isLimitAt ℝ⁺S f 0# lim)
  ((g , 0≤g) : ℝ⁰⁺)
  where

  private
    fℚ : ℚ⁺ -> ℝ
    fℚ (q , 0<q) = (f (ℚ->ℝ q , ℚ->ℝ-preserves-< 0<q))
    module lim = Real lim
    module g = Real g


    L' : Pred ℚ ℓ-zero
    L' q = Σ[ r⁺@(r , 0<r) ∈ ℚ⁺ ] Σ[ gL-r ∈ g.L r ] (Real.L (f (g , 0<g 0<r gL-r)) q)
      where
      0<g : {r : ℚ} -> 0# < r -> g.L r -> 0# < g
      0<g 0<r gL-r = trans-< (ℚ->ℝ-preserves-< 0<r) (L->ℝ< gL-r)

    U' : Pred ℚ ℓ-zero
    U' q = Σ[ r⁺@(r , 0<r) ∈ ℚ⁺ ] Σ[ gL-r ∈ g.L r ] (Real.U (f (g , 0<g 0<r gL-r)) q)
      where
      0<g : {r : ℚ} -> 0# < r -> g.L r -> 0# < g
      0<g 0<r gL-r = trans-< (ℚ->ℝ-preserves-< 0<r) (L->ℝ< gL-r)

    L : Pred ℚ ℓ-zero
    L q = ∥ lim.L q ⊎ L' q ∥

    U : Pred ℚ ℓ-zero
    U q = ∥ Σ[ r⁺@(r , _) ∈ ℚ⁺ ] (g.U r × Real.U (fℚ r⁺) q) ⊎ U' q ∥

    Inhabited-L : Inhabited L
    Inhabited-L = ∥-map (\(q , l) -> q , ∣ inj-l l ∣) lim.Inhabited-L

    Inhabited-U : Inhabited U
    Inhabited-U = ∥-bind handle g.Inhabited-U
      where
      handle : Σ[ r ∈ ℚ ] (g.U r) -> ∃[ q ∈ ℚ ] U q
      handle (r , gU-r) = ∥-map handle2 (Real.Inhabited-U (fℚ r⁺))
        where
        0<r : 0# < r
        0<r = ℚ->ℝ-reflects-< (trans-≤-< 0≤g (U->ℝ< gU-r))
        r⁺ = r , 0<r
        handle2 : Σ[ q ∈ ℚ ] (Real.U (fℚ r⁺) q) -> Σ[ q ∈ ℚ ] U q
        handle2 (q , frU-q) = q , ∣ inj-l (r⁺ , gU-r , frU-q) ∣



    isLowerSet-L : isLowerSet L
    isLowerSet-L {q} {r} q<r Lr = ∥-map handle Lr
      where
      handle : lim.L r ⊎ L' r ->
               lim.L q ⊎ L' q
      handle (inj-l limL-r) = inj-l (lim.isLowerSet-L q<r limL-r)
      handle (inj-r (s⁺ , gL-s , fgL-r)) =
        inj-r (s⁺ , gL-s , Real.isLowerSet-L (f _) q<r fgL-r)


    isUpperSet-U : isUpperSet U
    isUpperSet-U {q} {r} q<r Uq = ∥-map handle Uq
      where
      handle : (Σ[ s⁺@(s , _) ∈ ℚ⁺ ] (g.U s × Real.U (fℚ s⁺) q) ⊎ U' q) ->
               (Σ[ s⁺@(s , _) ∈ ℚ⁺ ] (g.U s × Real.U (fℚ s⁺) r) ⊎ U' r)
      handle (inj-l (s⁺ , gU-s , fsU-q)) =
        inj-l (s⁺ , gU-s , Real.isUpperSet-U (fℚ s⁺) q<r fsU-q)
      handle (inj-r (s⁺ , gL-s , fgU-q)) =
        inj-r (s⁺ , gL-s , Real.isUpperSet-U (f _) q<r fgU-q)


    isUpperOpen-L : isUpperOpen L
    isUpperOpen-L q Lq = ∥-bind handle Lq
      where
      handle : lim.L q ⊎ L' q ->
               ∃[ s ∈ ℚ ] (q < s × L s)
      handle (inj-l limL-q) =
        ∥-map (\ (s , q<s , limL-s) -> s , q<s , ∣ inj-l limL-s ∣) (lim.isUpperOpen-L q limL-q)
      handle (inj-r (r⁺ , gL-r , fgL-q)) =
        ∥-map (\ (s , q<s , fgL-s) -> s , q<s , ∣ inj-r (r⁺ , gL-r , fgL-s) ∣)
              (Real.isUpperOpen-L (f _) q fgL-q)


    isLowerOpen-U : isLowerOpen U
    isLowerOpen-U q Lq = ∥-bind handle Lq
      where
      handle : (Σ[ r⁺@(r , _) ∈ ℚ⁺ ] (g.U r × Real.U (fℚ r⁺) q) ⊎ U' q) ->
               ∃[ s ∈ ℚ ] (s < q × U s)
      handle (inj-l (r⁺ , gU-r , frU-q)) =
        ∥-map (\ (s , s<q , frU-s) -> s , s<q , ∣ (inj-l (r⁺ , gU-r , frU-s)) ∣)
              (Real.isLowerOpen-U (fℚ r⁺) q frU-q)
      handle (inj-r (r⁺ , gL-r , fgU-q)) =
        ∥-map (\ (s , s<q , fgU-s) -> s , s<q , ∣ (inj-r (r⁺ , gL-r , fgU-s)) ∣)
              (Real.isLowerOpen-U (f _) q fgU-q)

    disjoint : Universal (Comp (L ∩ U))
    disjoint q (Lq , Uq) = unsquash isPropBot (∥-map2 handle Lq Uq)
      where
      handle : lim.L q ⊎ L' q ->
               (Σ[ r⁺@(r , _) ∈ ℚ⁺ ] (g.U r × Real.U (fℚ r⁺) q) ⊎ U' q) ->
               Bot
      handle (inj-r (r1⁺@(r1 , 0<r1) , gL-r1 , fgL-q)) (inj-l (r2⁺@(r2 , _) , gU-r2 , fr2U-q)) =
        irrefl-< (trans-< (trans-<-≤ q<fg fg≤fr2) fr2<q)
        where
        g<r2 : g < ℚ->ℝ r2
        g<r2 = U->ℝ< gU-r2
        fg≤fr2 : f (g , _) ≤ fℚ r2⁺
        fg≤fr2 = nondec-f _ _ (weaken-< g<r2)
        fr2<q : fℚ r2⁺ < ℚ->ℝ q
        fr2<q = U->ℝ< fr2U-q
        q<fg : ℚ->ℝ q < f (g , _)
        q<fg = L->ℝ< fgL-q

      handle (inj-r (r1⁺@(r1 , 0<r1) , gL-r1 , fgL-q)) (inj-r (r2⁺@(r2 , 0<r2) , gL-r2 , fgU-q)) =
        Real.disjoint (f _) q (subst (\r -> Real.L r q) fg-path fgL-q , fgU-q)
        where
        fg-path : f (g , _) == f (g , _)
        fg-path = cong f (cong (g ,_) (isProp-< (trans-< (ℚ->ℝ-preserves-< 0<r1) (L->ℝ< gL-r1))
                                                (trans-< (ℚ->ℝ-preserves-< 0<r2) (L->ℝ< gL-r2))))

      handle (inj-l limL-q) (inj-l (r⁺@(r , 0<r) , gU-r , frU-q)) =
        irrefl-< (trans-< (L->ℝ< limL-q) (trans-≤-< lim≤fr (U->ℝ< frU-q)))
        where
        lim≤fr : lim ≤ (fℚ r⁺)
        lim≤fr = isNonDecreasing-limit-≤ f nondec-f isLimit-lim (ℚ->ℝ r , ℚ->ℝ-preserves-< 0<r)
      handle (inj-l limL-q) (inj-r (r⁺@(r , 0<r) , gL-r , fgU-q)) =
        irrefl-< (trans-< (L->ℝ< limL-q) (trans-≤-< lim≤fg (U->ℝ< fgU-q)))
        where
        lim≤fg : lim ≤ (f (g , _))
        lim≤fg = isNonDecreasing-limit-≤ f nondec-f isLimit-lim
                   (g , (trans-< (ℚ->ℝ-preserves-< 0<r) (L->ℝ< gL-r)))


    located⁺ : (x y : ℚ) -> x < y -> 0# < g -> ∥ L x ⊎ U y ∥
    located⁺ x y x<y 0<g = ∥-map2 handle 0<g (fg.located x y x<y)
      where
      fg : ℝ
      fg = (f (g , 0<g))
      module fg = Real fg
      handle : (0# ℝ<' g) -> (fg.L x ⊎ fg.U y) -> L x ⊎ U y
      handle (ℝ<'-cons q 0U-q gL-q) (inj-l fgL-x) =
        inj-l ∣ inj-r ((q , U->ℚ< 0U-q) , gL-q , subst (\r -> Real.L r x) fg-path fgL-x) ∣
        where
        fg-path : f (g , _) == f (g , _)
        fg-path = cong f (cong (g ,_) (isProp-< 0<g _))
      handle (ℝ<'-cons q 0U-q gL-q) (inj-r fgU-y) =
        inj-r (∣ inj-r ((q , U->ℚ< 0U-q) , gL-q , subst (\r -> Real.U r y) fg-path fgU-y) ∣)
        where
        fg-path : f (g , _) == f (g , _)
        fg-path = cong f (cong (g ,_) (isProp-< 0<g _))



    located : (x y : ℚ) -> x < y -> ∥ L x ⊎ U y ∥
    located x y x<y = ∥-bind handle (lim.located x y x<y)
      where
      handle : (lim.L x ⊎ lim.U y) -> ∥ L x ⊎ U y ∥
      handle (inj-l limL-x) = ∣ (inj-l ∣ inj-l limL-x ∣) ∣
      handle (inj-r limU-y) =
        ∥-bind2 handle2 (isLimitAt.limit-point isLimit-lim)
                        (isLimitAt.distance<ε isLimit-lim (ε , 0<ε))
        where
        lim<y : lim < ℚ->ℝ y
        lim<y = U->ℝ< limU-y
        ε = diff lim (ℚ->ℝ y)
        0<ε : 0# < ε
        0<ε = diff-0<⁺ lim<y
        handle2 : LimitTestSeq ℝ⁺S 0# ->
                  Σ[ δ⁺@(δ , _) ∈ ℝ⁺ ]
                    (∀ (z⁺@(z , _) : ℝ⁺) -> (distance 0# z) < δ -> (distance lim (f z⁺)) < ε) ->
                  ∥ L x ⊎ U y ∥
        handle2 t (δ⁺@(δ , 0<δ) , close) = ∥-bind handle3 (isLimit.distance<ε t.isLimit-seq δ⁺)
          where
          module t = LimitTestSeq t
          handle3 : ∀Largeℕ' (\i -> distance 0# (t.seq i) < δ) -> ∥ L x ⊎ U y ∥
          handle3 (n1 , close-n1) = ∥-bind handle4 (isLimit.distance<ε t.isLimit-seq (δ2 , 0<δ2))
            where
            δ2 = diff 0# (t.seq n1)
            0<δ2 : 0# < δ2
            0<δ2 = trans-<-= (t.S-seq n1) (sym diff-step >=> +-left-zero)
            handle4 : ∀Largeℕ' (\i -> distance 0# (t.seq i) < δ2) -> ∥ L x ⊎ U y ∥
            handle4 (n2 , close-n2) = ∥-bind handle5 (comparison-< (t.seq n2) g (t.seq n1) n2<n1)
              where
              dist-n2<diff-n1 : distance 0# (t.seq n2) < diff 0# (t.seq n1)
              dist-n2<diff-n1 = close-n2 n2 refl-≤

              n2<n1 : (t.seq n2) < (t.seq n1)
              n2<n1 = distance-diff-<' dist-n2<diff-n1
              handle5 : ((t.seq n2) < g ⊎ g < (t.seq n1)) -> ∥ L x ⊎ U y ∥
              handle5 (inj-l n2<g) = located⁺ x y x<y (trans-< 0<n2 n2<g)
                where
                0<n2 : 0# < t.seq n2
                0<n2 = t.S-seq n2
              handle5 (inj-r g<n1) = ∥-map handle6 g<n1
                where
                handle6 : g ℝ<' (t.seq n1) -> L x ⊎ U y
                handle6 (ℝ<'-cons q gU-q n1L-q) =
                  inj-r ∣ inj-l ((q , 0<q) , gU-q , ℝ<->U fq<y) ∣
                  where
                  0<q : 0# < q
                  0<q = ℚ->ℝ-reflects-< (trans-≤-< 0≤g (U->ℝ< gU-q))

                  fn1<y : f (t.∈S n1) < ℚ->ℝ y
                  fn1<y = distance-diff-<' (close (t.∈S n1) (close-n1 n1 refl-≤))

                  fq≤fn1 : fℚ (q , 0<q) ≤ f (t.∈S n1)
                  fq≤fn1 = nondec-f _ _ (weaken-< (L->ℝ< n1L-q))

                  fq<y : fℚ (q , 0<q) < ℚ->ℝ y
                  fq<y = trans-≤-< fq≤fn1 fn1<y


  ans : ℝ
  ans = record
    { L = L
    ; U = U
    ; isProp-L = \_ -> squash
    ; isProp-U = \_ -> squash
    ; Inhabited-L = Inhabited-L
    ; Inhabited-U = Inhabited-U
    ; isLowerSet-L = isLowerSet-L
    ; isUpperSet-U = isUpperSet-U
    ; isUpperOpen-L = isUpperOpen-L
    ; isLowerOpen-U = isLowerOpen-U
    ; disjoint = disjoint
    ; located = located
    }
