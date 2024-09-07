{-# OPTIONS --cubical --safe --exact-split #-}

module real.series.cauchy-product where

open import additive-group
open import additive-group.instances.nat
open import additive-group.instances.real
open import base
open import equality-path
open import fin
open import fin.sum-pair
open import fin.sum-pair.triangle
open import finite-commutative-monoid
open import finite-commutative-monoid.dependent-split
open import finite-commutative-monoid.instances
open import finite-commutative-semigroup.minmax
open import finset
open import finset.instances
open import finset.instances.sum-pair
open import finsum
open import finsum.absolute-value
open import finsum.arithmetic
open import finsum.cardinality
open import finsum.order
open import finsum.sigma
open import functions
open import funext
open import heyting-field.instances.real
open import hlevel
open import isomorphism
open import metric-space
open import metric-space.instances.real
open import nat
open import nat.order
open import order
open import order.instances.nat
open import order.instances.real
open import order.minmax.instances.real
open import ordered-additive-group
open import ordered-additive-group.absolute-value
open import ordered-additive-group.instances.nat
open import ordered-additive-group.instances.real
open import ordered-field
open import ordered-ring.absolute-value
open import ordered-semiring
open import ordered-semiring.instances.real
open import ordered-semiring.instances.real-strong
open import real
open import real.arithmetic.multiplication.inverse
open import real.sequence.limit
open import real.sequence.limit.arithmetic
open import real.sequence.limit.zero
open import real.series
open import real.subspace
open import ring
open import ring.implementations.real
open import semiring
open import semiring.initial
open import sequence
open import sequence.partial-sums
open import sigma.base
open import subset.subspace
open import truncation


cauchy-product : Sequence ℝ -> Sequence ℝ -> Sequence ℝ
cauchy-product f g n = finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> f i * g j)

opaque
  isLimit-cauchy-product : {s1 s2 : Sequence ℝ} {l1 l2 : ℝ} ->
    isLimit (partial-sums s1) l1 -> isLimit (partial-sums s2) l2 -> isAbsConvergentSeries s1 ->
    isLimit (partial-sums (cauchy-product s1 s2)) (l1 * l2)
  isLimit-cauchy-product {a} {b} {limA} {limB} isLim-A isLim-B isAbsConv-a =
    isLimit-C
    where
    c : Sequence ℝ
    c = cauchy-product a b

    A : Sequence ℝ
    A = partial-sums a
    B : Sequence ℝ
    B = partial-sums b
    C : Sequence ℝ
    C = partial-sums c

    D : Sequence ℝ
    D n = finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> a i * (B j))

    C=D : (n : Nat) -> C n == D n
    C=D n = sym path2 >=> sym path1
      where
      path1 : finiteSum (\((fin-pair+ i j _) : FinPair+ n) -> a i * (B j)) ==
              finiteSum (\((fin-pair+ i j _) : FinPair+ n) ->
                (finiteSum (\((k , _) : Fin j) -> a i * b k)))
      path1 = cong finiteSum (funExt (\(fin-pair+ i j _) -> sym finiteSum-*))

      path2 : finiteSum (\((fin-pair+ i j _) : FinPair+ n) ->
                finiteSum (\((k , _) : Fin j) -> a i * b k)) ==
              finiteSum (\((k , _) : Fin n) ->
                finiteSum (\((fin-pair+ i j _) : FinPair+ k) -> a i * b j))
      path2 = sym (finiteSum-Σ _ _ _) >=>
              finiteMergeᵉ-convert-iso _ _ _ Fin-FinPair+-triangle-Iso _ >=>
              finiteSum-Σ _ _ _

    E : Sequence ℝ
    E n = finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> a i * (diff limB (B j))) +
          A (suc n) * limB

    D=E : (n : Nat) -> D n == E n
    D=E n =
      sym +-right-zero >=>
      +-right (sym +-inverse >=> +-commute) >=>
      sym +-assoc >=>
      +-left (+-right (sym minus-extract-right >=>
                       *-commute >=>
                       sym finiteSum-* >=>
                       cong finiteSum (funExt (\_ -> *-commute)) >=>
                       finiteMerge-convert-iso _ FinPair+-Fin-Iso _) >=>
              sym (finiteMerge-split _) >=>
              cong finiteSum (funExt (\(fin-pair+ i j _) -> sym *-distrib-+-left)))

    sum-absAs : ℝ
    sum-absAs = fst isAbsConv-a

    0≤sum-absAs : 0# ≤ sum-absAs
    0≤sum-absAs sum-absAs<0 =
      unsquash isPropBot (∥-map (\(n , f) -> 0≤part n (f n refl-≤))
                                (isLimit.upperℝ (snd isAbsConv-a) sum-absAs<0))
      where
      0≤part : ∀ n -> 0# ≤ partial-sums (abs ∘ a) n
      0≤part n = trans-≤ abs-0≤ finiteSum-abs≤

    partial≤full-absAs : ∀ (n : Nat) -> partial-sums (abs ∘ a) n ≤ sum-absAs
    partial≤full-absAs n sum<p =
      unsquash isPropBot (∥-map handle (isLimit.upperℝ (snd isAbsConv-a) sum<p))
      where
      handle : ∀Largeℕ' (\m -> partial-sums (abs ∘ a) m < partial-sums (abs ∘ a) n) -> Bot
      handle (N , f) = pn≤pM pM<pn
        where
        M : Nat
        M = n + N
        N≤M : N ≤ M
        N≤M = n , refl
        n≤M : n ≤ M
        n≤M = N , +-commuteᵉ N n

        d : ℝ
        d = partial-sums (dropN n (abs ∘ a)) N

        0≤d : 0# ≤ d
        0≤d = partial-sums-0≤ _ (\_ -> abs-0≤) _

        pM<pn : partial-sums (abs ∘ a) M < partial-sums (abs ∘ a) n
        pM<pn = f M N≤M
        pn≤pM : partial-sums (abs ∘ a) n ≤ partial-sums (abs ∘ a) M
        pn≤pM = trans-≤-= (trans-=-≤ (sym +-right-zero) (+₁-preserves-≤ 0≤d))
                          (partial-sums-dropN (abs ∘ a) n N)

    1+sum-absAs : ℝ
    1+sum-absAs = 1# + sum-absAs

    0<1+sum-absAs : 0# < 1+sum-absAs
    0<1+sum-absAs = trans-<-≤ 0<1 (trans-=-≤ (sym +-right-zero) (+₁-preserves-≤ 0≤sum-absAs))

    E1 : Sequence ℝ
    E1 n = finiteSum (\ ((fin-pair+ i j _) : FinPair+ n) -> a i * (diff limB (B j)))

    module _ ((ε , 0<ε) : ℝ⁺) where
      ε/2 : ℝ
      ε/2 = 1/2 * ε
      0<ε/2 : 0# < ε/2
      0<ε/2 = *-preserves-0< 0<1/2 0<ε

      ε1 : ℝ
      ε1 = ε/2 * ℝ1/ (1+sum-absAs , inj-r 0<1+sum-absAs)

      0<ε1 : 0# < ε1
      0<ε1 = *-preserves-0< 0<ε/2 (ℝ1/-preserves-0< 0<1+sum-absAs)

      ε1*Σa<ε/2 : (ε1 * sum-absAs) < ε/2
      ε1*Σa<ε/2 = trans-=-< *-assoc (trans-<-= (*₁-preserves-< 0<ε/2 Σa/[1+Σa]<1) *-right-one)
        where
        Σa<1+Σa : sum-absAs < 1+sum-absAs
        Σa<1+Σa = trans-=-< (sym +-left-zero) (+₂-preserves-< 0<1)

        Σa/[1+Σa]<1 : (ℝ1/ (1+sum-absAs , inj-r 0<1+sum-absAs) * sum-absAs) < 1#
        Σa/[1+Σa]<1 =
          trans-<-= (*₁-preserves-< (ℝ1/-preserves-0< 0<1+sum-absAs) Σa<1+Σa) ℝ1/-inverse

      isLimit-a : isLimit a 0#
      isLimit-a = isConvergentSeries->zero-limit (_ , isLim-A)

      module _ ((N-B , N-Bf) : ∀Largeℕ' (\n -> abs (diff limB (B n)) < ε1)) where
        B' : ℝ
        B' = finite⁺Max (\((i , _) : Fin (suc N-B)) -> abs (diff limB (B i))) + 1#

        0<B' : 0# < B'
        0<B' = trans-<-≤ 0<1 (trans-=-≤ (sym +-left-zero) (+₂-preserves-≤ 0≤max))
          where
          0≤max : 0# ≤ finite⁺Max (\((i , _) : Fin (suc N-B)) -> abs (diff limB (B i)))
          0≤max = trans-≤ abs-0≤ (finite⁺Max-≤ zero-fin)

        1/B' : ℝ
        1/B' = ℝ1/ (B' , inj-r 0<B')

        A-Bound : ℝ
        A-Bound = (ε/2 * 1/ℕ (suc N-B , tt)) * 1/B'

        0<A-Bound : 0# < A-Bound
        0<A-Bound = *-preserves-0< (*-preserves-0< 0<ε/2 (0<1/ℕ (suc N-B , tt))) (ℝ1/-preserves-0< 0<B')

        A-Bound-path : ((A-Bound * B') * ℕ->Semiring (suc N-B)) == ε/2
        A-Bound-path =
          *-left (*-assoc >=> *-right ℝ1/-inverse >=> *-right-one) >=>
          *-assoc >=> *-right (*-commute >=> ∃!-prop (∃!1/ℕ (suc N-B , tt))) >=> *-right-one


        module _ ((N-A , N-Af) : ∀Largeℕ' (\n -> abs (a n) < A-Bound)) where
          abs-E1-small : ∀Largeℕ' (\n -> abs (E1 n) < ε)
          abs-E1-small = N-A + N-B , small
            where
            small : (n : ℕ) -> ((N-A + N-B) ≤ n) -> abs (E1 n) < ε
            small n N-A+N-B≤n =
              trans-≤-< finiteSum-abs≤
                (trans-=-< path (trans-<-= (trans-≤-< (+₂-preserves-≤ case1)
                                                      (+₁-preserves-< case2)) 1/2-path))
              where
              Case1 : Type₀
              Case1 = Σ[ (fin-pair+ i j _) ∈ FinPair+ n ] (j < suc N-B)

              Case2 : Type₀
              Case2 = Σ[ (fin-pair+ i j _) ∈ FinPair+ n ] (suc N-B ≤ j)

              FS-C1 : FinSet ℓ-zero
              FS-C1 = Case1 , _

              FS-C2 : FinSet ℓ-zero
              FS-C2 = Case2 , _

              card-C1 : cardinality FS-C1 == suc N-B
              card-C1 = cardinality-path FS-C1 (_ , ∣ isoToEquiv card-iso ∣)
                where
                card-iso : Iso Case1 (Fin (suc N-B))
                card-iso .Iso.fun (fin-pair+ i j _ , j<sN-B) = j , j<sN-B
                card-iso .Iso.inv (j , j<sN-B@(k , p)) =
                  fin-pair+ (fst N-A+N-B≤n + (N-A + k)) j p2 , j<sN-B
                  where
                  p' : k + j == N-B
                  p' = cong pred (sym +'-right-suc >=> p)

                  p2 : (fst N-A+N-B≤n + (N-A + k)) + j == n
                  p2 = +-assocᵉ (fst N-A+N-B≤n) (N-A + k) j >=>
                       cong ((fst N-A+N-B≤n) +_) (+-assocᵉ N-A k j >=> (+-right p')) >=>
                       snd N-A+N-B≤n
                card-iso .Iso.rightInv _ = refl
                card-iso .Iso.leftInv _ =
                  ΣProp-path isProp-< (FinPair+-path₂ refl)


              C2-iso : Iso Case2 (Fin (fst N-A+N-B≤n + N-A))
              C2-iso .Iso.fun (fin-pair+ i j i+j=n , (k , k+sN-B=j)) =
                i , (k , +'-right-injective path)
                where
                path : (k + suc i) + N-B == ((fst N-A+N-B≤n) + N-A) + N-B
                path = +-left (+-commuteᵉ k (suc i)) >=>
                       +-assocᵉ (suc i) k N-B >=>
                       sym +'-right-suc >=>
                       +-right (sym +'-right-suc >=> k+sN-B=j) >=>
                       i+j=n >=>
                       sym (snd N-A+N-B≤n) >=>
                       sym (+-assocᵉ (fst N-A+N-B≤n) N-A N-B)


              C2-iso .Iso.inv (i , (k , k+si=Z)) = fin-pair+ i j i+j=n , (k , refl)
                where
                j : Nat
                j = (k + suc N-B)
                i+j=n : i + j == n
                i+j=n = sym (+-assocᵉ i k (suc N-B)) >=>
                        +'-right-suc >=>
                        +-left (+-commuteᵉ (suc i) k >=> k+si=Z) >=>
                        +-assocᵉ (fst N-A+N-B≤n) N-A N-B >=>
                        snd N-A+N-B≤n
              C2-iso .Iso.rightInv (i , _) = fin-i-path refl
              C2-iso .Iso.leftInv _ = ΣProp-path isProp-≤ (FinPair+-path₁ refl)


              isContr-lt : ((fin-pair+ i j _) : FinPair+ n) -> isContr (j < suc N-B ⊎ suc N-B ≤ j)
              isContr-lt (fin-pair+ i j _) =
                split-< j (suc N-B) ,
                isProp⊎ isProp-< isProp-≤ (\lt le -> convert-≤ le lt) _

              path : finiteSum (\((fin-pair+ i j _) : FinPair+ n) -> abs (a i * (diff limB (B j)))) ==
                     finiteSumᵉ FS-C1 (\((fin-pair+ i j _ , _) : Case1) -> abs (a i * (diff limB (B j)))) +
                     finiteSumᵉ FS-C2 (\((fin-pair+ i j _ , _) : Case2) -> abs (a i * (diff limB (B j))))
              path = finiteMerge-dependent-split _ isContr-lt _

              instance
                IFS-C1 : FinSetStr Case1
                IFS-C1 = record { isFin = snd FS-C1 }
                IFS-C2 : FinSetStr Case2
                IFS-C2 = record { isFin = snd FS-C2 }

              case1 : finiteSumᵉ FS-C1
                        (\((fin-pair+ i j _ , _) : Case1) ->
                          abs (a i * (diff limB (B j)))) ≤ ε/2
              case1 = lt3
                where
                module _ (i : ℕ) (j : ℕ) (i+j=n : i + j == n) (j<N-B : j < suc N-B) where
                  N-A≤i : N-A ≤ i
                  N-A≤i = +₂-reflects-≤ N-A+j≤i+j
                    where
                    N-A+j≤i+j : (N-A + j) ≤ (i + j)
                    N-A+j≤i+j = trans-≤ (+₁-preserves-≤ (pred-≤ j<N-B))
                                        (trans-≤-= N-A+N-B≤n (sym i+j=n))

                  lt1 : abs (diff limB (B j)) < B'
                  lt1 =
                    trans-≤-< (finite⁺Max-≤ (j , j<N-B))
                     (trans-=-< (sym +-right-zero) (+₁-preserves-< 0<1))

                  lt2 : abs (a i * (diff limB (B j))) ≤ ((A-Bound * B') * 1#)
                  lt2 =
                    (trans-≤-=
                      (trans-=-≤ abs-distrib-*
                        (trans-≤
                          (*₁-preserves-≤ abs-0≤ (weaken-< lt1))
                          (*₂-preserves-≤ (weaken-< (N-Af i N-A≤i)) (weaken-< 0<B'))))
                      (sym *-right-one))


                lt3 : finiteSumᵉ FS-C1
                        (\((fin-pair+ i j _ , _) : Case1) -> abs (a i * (diff limB (B j)))) ≤
                      ε/2
                lt3 =
                  trans-≤-= (finiteSum-preserves-≤
                              (\((fin-pair+ i j i+j=n , j<N-B) : Case1) ->
                                (lt2 i j i+j=n j<N-B)))
                    (finiteSum-* >=>
                     *-right (finiteSum-one >=> cong ℕ->Semiring card-C1) >=>
                     A-Bound-path)



              case2 : finiteSumᵉ _ (\((fin-pair+ i j _ , _) : Case2) ->
                                     abs (a i * (diff limB (B j)))) < ε/2
              case2 = lt4
                where
                module _ (i : ℕ) (j : ℕ) (sN-B≤j : suc N-B ≤ j) where
                  lt1 : abs (diff limB (B j)) < ε1
                  lt1 = N-Bf j (weaken-< sN-B≤j)

                lt2 : finiteSumᵉ _ (\((fin-pair+ i j _ , _) : Case2) ->
                                      abs (a i * (diff limB (B j)))) ≤
                      (ε1 * finiteSumᵉ _ (\((fin-pair+ i j _ , _) : Case2) -> abs (a i)))
                lt2 =
                  trans-≤-=
                    (finiteSum-preserves-≤
                       (\(fin-pair+ i j _ , sN-B≤j) ->
                         (trans-≤-=
                           (trans-=-≤ abs-distrib-*
                                      (*₁-preserves-≤ abs-0≤ (weaken-< (lt1 i j sN-B≤j))))
                           *-commute)))
                    finiteSum-*

                lt3 : finiteSumᵉ _ (\((fin-pair+ i j _ , _) : Case2) -> abs (a i)) ≤ sum-absAs
                lt3 = trans-=-≤ (finiteMerge-convert-iso _ (iso⁻¹ C2-iso) _)
                                (partial≤full-absAs _)


                lt4 : finiteSumᵉ _ (\((fin-pair+ i j _ , _) : Case2) ->
                                      abs (a i * (diff limB (B j)))) <
                      ε/2
                lt4 = trans-≤-< (trans-≤ lt2 (*₁-preserves-≤ (weaken-< 0<ε1) lt3))
                                ε1*Σa<ε/2


          E1-small-distance1 : ∀Largeℕ' (\n -> distance 0# (E1 n) < ε)
          E1-small-distance1 =
            subst ∀Largeℕ' (funExt (\n -> cong (_< ε) path)) abs-E1-small
            where
            path : {n : Nat} -> abs (E1 n) == distance 0# (E1 n)
            path = cong abs (sym diff-step >=> +-left-zero)

        E1-small-distance2 : ∀Largeℕ (\n -> distance 0# (E1 n) < ε)
        E1-small-distance2 =
          ∥-map E1-small-distance1 (isLimit0->abs<ε isLimit-a (A-Bound , 0<A-Bound))

      E1-small-distance3 : ∀Largeℕ (\n -> distance 0# (E1 n) < ε)
      E1-small-distance3 =
        ∥-bind E1-small-distance2 (isLimit.distance<ε isLim-B (ε1 , 0<ε1))


    isLimit-E1 : isLimit E1 0#
    isLimit-E1 = distance<ε->isLimit E1-small-distance3

    isLimit-A' : isLimit (A ∘ suc) limA
    isLimit-A' = dropN-preserves-limit isLim-A

    isLimit-C : isLimit C (limA * limB)
    isLimit-C =
      subst2 isLimit (sym (funExt C=D >=> funExt D=E)) (+-left-zero)
        (+-preserves-limit isLimit-E1 (*₂-preserves-limit isLimit-A'))
