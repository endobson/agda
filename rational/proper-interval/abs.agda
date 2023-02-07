{-# OPTIONS --cubical --safe --exact-split #-}

module rational.proper-interval.abs where

open import additive-group
open import base
open import equality
open import order
open import order.instances.rational
open import order.minmax
open import order.minmax.instances.rational
open import ordered-ring
open import ordered-semiring
open import ordered-semiring.instances.rational
open import rational
open import rational.minmax
open import rational.order
open import rational.proper-interval
open import rational.proper-interval.maxabs-multiplication
open import rational.squares
open import relation
open import ring
open import ring.implementations.rational
open import semiring
open import sign
open import sign.instances.rational
open import sum
open import truncation


ImbalancedI : Pred Iℚ ℓ-zero
ImbalancedI a = (- (Iℚ.l a)) ≤ (Iℚ.u a)

BalancedI : Pred Iℚ ℓ-zero
BalancedI a = (- (Iℚ.l a)) == (Iℚ.u a)

BalancedI->ImbalancedI : (a : Iℚ) -> BalancedI a -> ImbalancedI a
BalancedI->ImbalancedI a = path-≤

NonNegI->ImbalancedI : (a : Iℚ) -> NonNegI a -> ImbalancedI a
NonNegI->ImbalancedI a@(Iℚ-cons l u l≤u) nn-a = trans-≤ (trans-≤ -l≤0 0≤l) l≤u
  where
  0≤l = NonNeg-0≤ _ nn-a
  -l≤0 = minus-flips-0≤ 0≤l

i-maxabs≤->ImbalancedI : (a : Iℚ) -> (i-maxabs a ℚ≤ Iℚ.u a) -> ImbalancedI a
i-maxabs≤->ImbalancedI (Iℚ-cons l u l≤u) ma≤au =
  trans-ℚ≤ { - l} max-≤-right (trans-ℚ≤ {absℚ l} max-≤-left ma≤au)

ImbalancedI->0≤u : (a : Iℚ) -> ImbalancedI a -> (0r ≤ Iℚ.u a)
ImbalancedI->0≤u (Iℚ-cons l u l≤u) -l≤u = NonNeg-0≤ u nn-u
  where
  al≤u : absℚ l ℚ≤ u
  al≤u = maxℚ-property {P = _ℚ≤ u} l (- l) l≤u -l≤u

  nn-u : NonNeg u
  nn-u = NonNeg-≤ (absℚ l) u (NonNeg-absℚ l) al≤u


ImbalancedI->i-maxabs : (a : Iℚ) -> ImbalancedI a -> (i-maxabs a == Iℚ.u a)
ImbalancedI->i-maxabs (Iℚ-cons l u l≤u) -l≤u =
  max-≤-path al≤au >=> au=u
  where
  al≤u : absℚ l ℚ≤ u
  al≤u = maxℚ-property {P = _ℚ≤ u} l (- l) l≤u -l≤u

  nn-u : NonNeg u
  nn-u = NonNeg-≤ (absℚ l) u (NonNeg-absℚ l) al≤u

  au=u : absℚ u == u
  au=u = (absℚ-NonNeg nn-u)

  al≤au : absℚ l ℚ≤ absℚ u
  al≤au = trans-ℚ≤ {absℚ l} al≤u max-≤-left

ImbalancedI-i- : (ai : Iℚ) -> ImbalancedI ai ⊎ ImbalancedI (i- ai)
ImbalancedI-i- ai@(Iℚ-cons l u l≤u) = handle (split-< (- l) u)
  where
  handle : ((- l) < u ⊎ u ≤ (- l)) -> ImbalancedI ai ⊎ ImbalancedI (i- ai)
  handle (inj-l -l<u) = inj-l (weaken-< -l<u)
  handle (inj-r u≤-l) = inj-r (subst (_≤ (- l)) (sym minus-double-inverse) u≤-l)


i²-ImbalancedI : (ai : Iℚ) -> ImbalancedI ai -> Iℚ
i²-ImbalancedI ai@(Iℚ-cons l u l≤u) -l≤u = (Iℚ-cons (min (l * l) (l * u)) (u * u) lllu≤uu)
  where
  0≤u = ImbalancedI->0≤u ai -l≤u
  lu≤uu = *₂-preserves-≤ l≤u 0≤u

  lllu≤uu : min (l * l) (l * u) ≤ (u * u)
  lllu≤uu = trans-≤ min-≤-right lu≤uu

i²-ImbalancedI-path : (ai : Iℚ) -> (imb-ai : ImbalancedI ai) -> (i²-ImbalancedI ai imb-ai) == (ai i* ai)
i²-ImbalancedI-path ai@(Iℚ-cons l u l≤u) -l≤u = Iℚ-bounds-path l-path u-path
  where
  -l = - l
  l2 = Iℚ.l (ai i* ai)
  u2 = Iℚ.u (ai i* ai)

  0≤u = ImbalancedI->0≤u ai -l≤u

  lu≤uu = *₂-preserves-≤ l≤u 0≤u
  ul≤uu = *₁-preserves-≤ 0≤u l≤u
  ll≤uu = handle (split-< l 0r)
    where
    handle : (l < 0r ⊎ 0r ≤ l) -> (l * l) ≤ (u * u)
    handle (inj-r 0≤l) = trans-≤ (*₁-preserves-≤ 0≤l l≤u)
                                 (*₂-preserves-≤ l≤u 0≤u)
    handle (inj-l l<0) =
      subst (_≤ (u * u)) minus-extract-both
            (trans-≤ (*₁-preserves-≤ 0≤-l -l≤u)
                     (*₂-preserves-≤ -l≤u 0≤u))
      where
      0≤-l = (minus-flips-≤0 (weaken-< l<0))

  l-path : (min (l * l) (l * u)) == l2
  l-path = sym (cong (min (min (l * l) (l * u))) (min-≤-path ul≤uu >=> *-commute) >=>
                min-≤-path min-≤-right)

  max-lllu≤uu : max (l * l) (l * u) ≤ (u * u)
  max-lllu≤uu = maxℚ-property {P = _≤ (u * u)} (l * l) (l * u) ll≤uu lu≤uu

  u-path : (u * u) == u2
  u-path = sym (cong (max (max (l * l) (l * u))) (max-≤-path ul≤uu) >=>
                max-≤-path max-lllu≤uu)


i²-NonNegI : (ai : Iℚ) -> NonNegI ai -> Iℚ
i²-NonNegI ai@(Iℚ-cons l u l≤u)  nn-ai = (Iℚ-cons (l * l) (u * u) ll≤uu)
  where
  0≤l = NonNeg-0≤ l nn-ai

  ll≤uu : (l * l) ≤ (u * u)
  ll≤uu =
    trans-≤ (*₁-preserves-≤ 0≤l l≤u)
            (*₂-preserves-≤ l≤u (trans-≤ 0≤l l≤u))


i²-NonNegI-path : (ai : Iℚ) -> (nn-ai : NonNegI ai) -> i²-NonNegI ai nn-ai == (ai i* ai)
i²-NonNegI-path ai@(Iℚ-cons l u l≤u) nn-ai = Iℚ-bounds-path l-path u-path
  where
  0≤l = NonNeg-0≤ l nn-ai
  0≤u = trans-≤ 0≤l l≤u

  l2 = Iℚ.l (ai i* ai)
  u2 = Iℚ.u (ai i* ai)

  ll≤lu = *₁-preserves-≤ 0≤l l≤u
  ll≤ul = *₂-preserves-≤ l≤u 0≤l
  ul≤uu = *₁-preserves-≤ 0≤u l≤u
  lu≤uu = *₂-preserves-≤ l≤u 0≤u

  l-path : (l * l) == l2
  l-path = sym (cong2 min (min-≤-path ll≤lu) (min-≤-path ul≤uu) >=> min-≤-path ll≤ul)

  u-path : (u * u) == u2
  u-path = sym (cong2 max (max-≤-path ll≤lu) (max-≤-path ul≤uu) >=> max-≤-path lu≤uu)


i²-BalancedI : (ai : Iℚ) -> BalancedI ai -> Iℚ
i²-BalancedI ai@(Iℚ-cons l u l≤u) -l=u = Iℚ-cons (l * u) (u * u) lu≤uu
  where
  0≤u = ImbalancedI->0≤u ai (BalancedI->ImbalancedI ai -l=u)

  lu≤uu = *₂-preserves-≤ l≤u 0≤u


i²-BalancedI-path : (ai : Iℚ) -> (bal-ai : BalancedI ai) -> i²-BalancedI ai bal-ai == (ai i* ai)
i²-BalancedI-path ai@(Iℚ-cons l u l≤u) bal-ai = Iℚ-bounds-path l-path u-path
  where
  0≤u = ImbalancedI->0≤u ai (BalancedI->ImbalancedI ai bal-ai)
  l≤0 = subst (_≤ 0r) (cong -_ (sym bal-ai) >=> minus-double-inverse) (minus-flips-0≤ 0≤u)

  l2 = Iℚ.l (ai i* ai)
  u2 = Iℚ.u (ai i* ai)

  lu≤ll = *₁-flips-≤ l≤0 l≤u
  ul≤ll = *₂-flips-≤ l≤u l≤0
  ul≤uu = *₁-preserves-≤ 0≤u l≤u
  lu≤uu = *₂-preserves-≤ l≤u 0≤u
  ll=uu : (l * l) == (u * u)
  ll=uu = sym minus-extract-both >=> *-cong bal-ai bal-ai
  lu=ul : (l * u) == (u * l)
  lu=ul = *-commute


  l-path : (l * u) == l2
  l-path = sym (cong2 min (min-≥-path lu≤ll) (min-≤-path ul≤uu) >=>
                min-≤-path (path-≤ lu=ul))

  u-path : (u * u) == u2
  u-path = sym (cong2 max (max-≥-path lu≤ll) (max-≤-path ul≤uu) >=>
                max-≤-path (path-≤ ll=uu))



naive-i² : (a : Iℚ) -> ImbalancedI a -> Iℚ
naive-i² (Iℚ-cons l u l≤u) -l≤u = (Iℚ-cons (l * l) (u * u) ll≤uu)
  where
  ll≤uu : (l * l) ≤ (u * u)
  ll≤uu = unsquash isProp-≤ (∥-map handle (connex-≤ 0r l))
    where
    handle : (0r ≤ l ⊎ l ≤ 0r) -> (l * l) ≤ (u * u)
    handle (inj-l 0≤l) =
      trans-≤ (*₁-preserves-≤ 0≤l l≤u)
              (*₂-preserves-≤ l≤u (trans-≤ 0≤l l≤u))
    handle (inj-r l≤0) = subst (_≤ (u * u)) -l-l=ll -l-l≤uu
      where
      0≤-l = minus-flips-≤0 l≤0
      -l = - l

      -l-l≤uu = trans-≤ (*₁-preserves-≤ 0≤-l -l≤u)
                        (*₂-preserves-≤ -l≤u (trans-≤ 0≤-l -l≤u))
      -l-l=ll : (-l * -l) == l * l
      -l-l=ll = minus-extract-left >=> cong -_ minus-extract-right >=> minus-double-inverse



ℚ∈Iℚ-i∪₁ : (q : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q (a i∪ b)
ℚ∈Iℚ-i∪₁ q (Iℚ-cons al au _) (Iℚ-cons bl bu _) (al≤q , q≤au) =
  trans-ℚ≤ {min al bl} min-≤-left al≤q ,
  trans-ℚ≤ {q} q≤au max-≤-left

ℚ∈Iℚ-i∪₂ : (q : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q b -> ℚ∈Iℚ q (a i∪ b)
ℚ∈Iℚ-i∪₂ q a b q∈b = subst (ℚ∈Iℚ q) (i∪-commute b a) (ℚ∈Iℚ-i∪₁ q b a q∈b)

ℚ∈Iℚ-i-scale : (k q : ℚ) (a : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ (k * q) (i-scale k a)
ℚ∈Iℚ-i-scale k q a@(Iℚ-cons l u l≤u) (l≤q , q≤u) = handle (split-< k 0r)
  where
  handle : (k < 0r ⊎ 0r ℚ≤ k) -> ℚ∈Iℚ (k * q) (i-scale k a)
  handle (inj-l k<0) = subst (ℚ∈Iℚ (k * q)) (i-scale-NP-path (k , np-k) a) kq∈ka'
    where
    np-k : NonPos k
    np-k = ≤0-NonPos k (weaken-< k<0)

    kq∈ka' : ℚ∈Iℚ (k * q) (i-scale-NP (k , np-k) a)
    kq∈ka' = *₁-flips-≤ (weaken-< k<0) q≤u ,
             *₁-flips-≤ (weaken-< k<0) l≤q

  handle (inj-r 0≤k) = subst (ℚ∈Iℚ (k * q)) (i-scale-NN-path (k , nn-k) a) kq∈ka'
    where
    nn-k : NonNeg k
    nn-k = 0≤-NonNeg k 0≤k

    kq∈ka' : ℚ∈Iℚ (k * q) (i-scale-NN (k , nn-k) a)
    kq∈ka' = *₁-preserves-≤ 0≤k l≤q ,
             *₁-preserves-≤ 0≤k q≤u

ℚ∈Iℚ-⊆ : (q : ℚ) -> {a b : Iℚ} -> (a i⊆ b) -> ℚ∈Iℚ q a -> ℚ∈Iℚ q b
ℚ∈Iℚ-⊆ q {_} {b} (i⊆-cons bl≤al au≤bu) (al≤q , q≤au) =
  trans-ℚ≤ {Iℚ.l b} bl≤al al≤q , trans-ℚ≤ {q} q≤au au≤bu

ℚ∈Iℚ-* : (q r : ℚ) (a b : Iℚ) -> ℚ∈Iℚ q a -> ℚ∈Iℚ r b -> ℚ∈Iℚ (q * r) (a i* b)
ℚ∈Iℚ-* q r a@(Iℚ-cons al au al≤au) b q∈a r∈b =
  subst ∈ab *-commute rq∈ab
  where
  ab = (a i* b)
  abl = Iℚ.l ab
  abu = Iℚ.u ab

  ∈ab : Pred ℚ ℓ-zero
  ∈ab q = ℚ∈Iℚ q ab


  alr∈alb : ℚ∈Iℚ (al * r) (i-scale al b)
  alr∈alb = ℚ∈Iℚ-i-scale al r b r∈b

  alr∈ab : ℚ∈Iℚ (al * r) ab
  alr∈ab = ℚ∈Iℚ-i∪₁ (al * r) (i-scale al b) (i-scale au b) alr∈alb

  ral∈ab : ℚ∈Iℚ (r * al) ab
  ral∈ab = subst ∈ab *-commute alr∈ab

  aur∈aub : ℚ∈Iℚ (au * r) (i-scale au b)
  aur∈aub = ℚ∈Iℚ-i-scale au r b r∈b

  aur∈ab : ℚ∈Iℚ (au * r) ab
  aur∈ab = ℚ∈Iℚ-i∪₂ (au * r) (i-scale al b) (i-scale au b) aur∈aub

  rau∈ab : ℚ∈Iℚ (r * au) ab
  rau∈ab = subst ∈ab *-commute aur∈ab

  ra⊆ab : i-scale r a i⊆ ab
  ra⊆ab = i⊆-cons (minℚ-property {P = abl ℚ≤_} (r * al) (r * au) (fst ral∈ab) (fst rau∈ab))
                  (maxℚ-property {P = _ℚ≤ abu} (r * al) (r * au) (snd ral∈ab) (snd rau∈ab))

  rq∈ra : ℚ∈Iℚ (r * q) (i-scale r a)
  rq∈ra = ℚ∈Iℚ-i-scale r q a q∈a

  rq∈ab : ℚ∈Iℚ (r * q) ab
  rq∈ab = ℚ∈Iℚ-⊆ (r * q) ra⊆ab rq∈ra





ℚ∈Iℚ-l : (a : Iℚ) -> (ℚ∈Iℚ (Iℚ.l a) a)
ℚ∈Iℚ-l (Iℚ-cons l u l≤u) = refl-ℚ≤ , l≤u

ℚ∈Iℚ-u : (a : Iℚ) -> (ℚ∈Iℚ (Iℚ.u a) a)
ℚ∈Iℚ-u (Iℚ-cons l u l≤u) = l≤u , refl-ℚ≤



naive-i²-⊆-* : (a : Iℚ) -> (i : ImbalancedI a) -> (naive-i² a i) i⊆ (a i* a)
naive-i²-⊆-* a@(Iℚ-cons l u l≤u) i@-l≤u = a²⊆aa
  where
  a² = (naive-i² a i)
  aa = a i* a
  a²⊆aa : a² i⊆ aa
  a²⊆aa = i⊆-cons (fst (ℚ∈Iℚ-* l l a a (ℚ∈Iℚ-l a) (ℚ∈Iℚ-l a)))
                  (snd (ℚ∈Iℚ-* u u a a (ℚ∈Iℚ-u a) (ℚ∈Iℚ-u a)))


i*-i⊆-square-NonNegI⁻ : (ai bi : Iℚ) -> NonNegI ai -> NonNegI bi ->
                        (ai i* ai) i⊆ (bi i* bi) -> ai i⊆ bi
i*-i⊆-square-NonNegI⁻ ai@(Iℚ-cons al au al≤au) bi@(Iℚ-cons bl bu bl≤bu) nn-al nn-bl
                      (i⊆-cons b²l≤a²l  a²u≤b²u) = i⊆-cons bl≤al au≤bu
  where
  0≤al = NonNeg-0≤ al nn-al
  0≤bl = NonNeg-0≤ bl nn-bl
  0≤au = trans-≤ 0≤al al≤au
  0≤bu = trans-≤ 0≤bl bl≤bu

  blbl≤alal : (bl * bl) ≤ (al * al)
  blbl≤alal = subst2 _≤_ (cong Iℚ.l (sym (i²-NonNegI-path bi nn-bl)))
                         (cong Iℚ.l (sym (i²-NonNegI-path ai nn-al))) b²l≤a²l

  bl≤al : bl ≤ al
  bl≤al = squares-ordered-≤ 0≤al blbl≤alal

  auau≤bubu : (au * au) ≤ (bu * bu)
  auau≤bubu = subst2 _≤_ (cong Iℚ.u (sym (i²-NonNegI-path ai nn-al)))
                         (cong Iℚ.u (sym (i²-NonNegI-path bi nn-bl))) a²u≤b²u

  au≤bu : au ≤ bu
  au≤bu = squares-ordered-≤ 0≤bu auau≤bubu

i*-i⊆-square-NonNegI2⁻ : (ai bi : Iℚ) -> ImbalancedI ai -> NonNegI bi ->
                         (ai i* ai) i⊆ (bi i* bi) -> ai i⊆ bi
i*-i⊆-square-NonNegI2⁻ ai@(Iℚ-cons al au al≤au) bi@(Iℚ-cons bl bu bl≤bu) imb-ai nn-bi
                       aiai⊆bibi@(i⊆-cons b²l≤a²l  a²u≤b²u) =
  i*-i⊆-square-NonNegI⁻ ai bi nn-ai nn-bi aiai⊆bibi
  where
  0≤au = ImbalancedI->0≤u ai imb-ai
  0≤bl = NonNeg-0≤ bl nn-bi
  0≤blbl = *-preserves-0≤ 0≤bl 0≤bl
  a²l≤alau = fst (ℚ∈Iℚ-* _ _ ai ai (ℚ∈Iℚ-l ai) (ℚ∈Iℚ-u ai))
  b²l≤alau = trans-≤ b²l≤a²l a²l≤alau
  blbl≤alau = subst (_≤ (al * au)) (cong Iℚ.l (sym (i²-NonNegI-path bi nn-bi)))  b²l≤alau
  0≤alau = trans-≤ 0≤blbl blbl≤alau

  al≮0 : al ≮ 0r
  al≮0 al<0 = irrefl-< (trans-≤-< 0≤alau alau<0)
    where
    0<-al = minus-flips-<0 al<0
    0<au = trans-<-≤ 0<-al imb-ai
    alau<0 = subst ((al * au) <_) *-left-zero (*₂-preserves-< al<0 0<au)

  nn-ai : NonNegI ai
  nn-ai = 0≤-NonNeg al (proj-¬l (split-< al 0r) al≮0)



i*-i⊆-square-BalancedI⁻ : (ai bi : Iℚ) -> BalancedI bi ->
                           (ai i* ai) i⊆ (bi i* bi) -> ai i⊆ bi
i*-i⊆-square-BalancedI⁻ ai@(Iℚ-cons al au al≤au) bi@(Iℚ-cons bl bu bl≤bu) bal-bi
                         (i⊆-cons b²l≤a²l  a²u≤b²u) = i⊆-cons bl≤al au≤bu
  where
  0≤bu = ImbalancedI->0≤u bi (BalancedI->ImbalancedI bi bal-bi)

  l2 = Iℚ.l (ai i* ai)
  u2 = Iℚ.u (ai i* ai)

  blbu≤l2 : (bl * bu) ≤ l2
  blbu≤l2 = subst (_≤ l2) (cong Iℚ.l (sym (i²-BalancedI-path bi bal-bi))) b²l≤a²l

  u2≤bubu : u2 ≤ (bu * bu)
  u2≤bubu = subst (u2 ≤_) (cong Iℚ.u (sym (i²-BalancedI-path bi bal-bi))) a²u≤b²u

  auau≤u2 : (au * au) ≤ u2
  auau≤u2 = snd (ℚ∈Iℚ-* _ _ ai ai (ℚ∈Iℚ-u ai) (ℚ∈Iℚ-u ai))
  alal≤u2 : (al * al) ≤ u2
  alal≤u2 = snd (ℚ∈Iℚ-* _ _ ai ai (ℚ∈Iℚ-l ai) (ℚ∈Iℚ-l ai))

  auau≤bubu : (au * au) ≤ (bu * bu)
  auau≤bubu = trans-≤ auau≤u2 u2≤bubu

  alal≤bubu : (al * al) ≤ (bu * bu)
  alal≤bubu = trans-≤ alal≤u2 u2≤bubu
  malmal≤bubu = subst (_≤ (bu * bu)) (sym minus-extract-both) alal≤bubu

  au≤bu = squares-ordered-≤ 0≤bu auau≤bubu
  mal≤bu = squares-ordered-≤ 0≤bu malmal≤bubu
  mal≤mbl = subst ((- al) ≤_) (sym bal-bi) mal≤bu
  bl≤al = subst2 _≤_ minus-double-inverse minus-double-inverse (minus-flips-≤ mal≤mbl)






i*-preserves-ImbalancedI : (a b : Iℚ) -> ImbalancedI a -> ImbalancedI b -> ImbalancedI (a i* b)
i*-preserves-ImbalancedI a b imb-a imb-b = i-maxabs≤->ImbalancedI ab mab≤abu
  where
  ab = a i* b
  ma = i-maxabs a
  mb = i-maxabs b
  mab = i-maxabs ab
  au = Iℚ.u a
  bu = Iℚ.u b
  abu = Iℚ.u ab

  aubu≤abu : (au * bu) ℚ≤ abu
  aubu≤abu = snd (ℚ∈Iℚ-* au bu a b (ℚ∈Iℚ-u a) (ℚ∈Iℚ-u b))


  ma=au : ma == au
  ma=au = ImbalancedI->i-maxabs a imb-a

  mb=bu : mb == bu
  mb=bu = ImbalancedI->i-maxabs b imb-b

  mab=aubu : mab == (au * bu)
  mab=aubu = i-maxabs-i* a b >=> *-cong ma=au mb=bu

  mab≤abu : mab ℚ≤ abu
  mab≤abu = subst (_ℚ≤ abu) (sym mab=aubu) aubu≤abu


i-abs : Iℚ -> Iℚ
i-abs (Iℚ-cons l u l≤u) = (Iℚ-cons (max l 0r) (max (- l) u) lt)
  where
  LT = (max l 0r) ℚ≤ (max (- l) u)
  abstract
    lt : LT
    lt = handle (split-< l 0r)
      where
      handle : (l < 0r) ⊎ (0r ℚ≤ l) -> LT
      handle (inj-l l<0) =
        subst (_ℚ≤ (max (- l) u))
          (sym (max-<-path l<0))
          (trans-ℚ≤ {0r} (weaken-< (minus-flips-<0 l<0)) max-≤-left)
      handle (inj-r 0≤l) =
        subst2 (_ℚ≤_) (sym (max-≥-path 0≤l)) (sym (max-≤-path -l≤u)) l≤u
        where
        -l≤0 : (- l) ℚ≤ 0r
        -l≤0 = (minus-flips-0≤ 0≤l)
        -l≤u : (- l) ℚ≤ u
        -l≤u = trans-ℚ≤ { - l} (trans-ℚ≤ { - l}-l≤0 0≤l) l≤u
