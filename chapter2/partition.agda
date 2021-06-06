{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.partition where

open import abs
open import base
open import cubical
open import chapter2.totient
open import div
open import equality
open import equivalence
open import fin
open import finsum
open import finset
open import finset.instances
open import finsubset
open import functions
open import gcd.euclidean-algorithm
open import gcd.propositional
open import hlevel
open import isomorphism
open import int
open import linear-combo
open import nat
open import nat.bounded
open import prime-gcd
open import relatively-prime
open import semiring
open import ring.implementations
open import sigma
open import truncation
open import type-algebra
open import univalence


module _ {ℓ₁ : Level}  {D : Type ℓ₁} {{S : Semiring D}} where
  open Semiring S
  private
    sum = finiteSum

    ATop : {ℓ : Level} -> Type ℓ -> Type ℓ
    ATop A = A × Top

    isFinSetATop : {ℓ : Level} {A : Type ℓ} -> isFinSet A -> isFinSet (ATop A)
    isFinSetATop {A = A} e = ∥-map handle e
      where
      handle : Σ[ n ∈ Nat ] (A ≃ Fin n) -> Σ[ n ∈ Nat ] (ATop A ≃ Fin n)
      handle (n , (f , eq)) = n , (f ∘ fst , eq2)
        where
        eq2 : isEquiv (f ∘ fst)
        eq2 .equiv-proof j .fst .fst = (eq .equiv-proof j .fst .fst , tt)
        eq2 .equiv-proof j .fst .snd = (eq .equiv-proof j .fst .snd)
        eq2 .equiv-proof j .snd ((a , tt) , path) i =
          (fst (eq .equiv-proof j .snd (a , path) i) , tt) ,
           snd (eq .equiv-proof j .snd (a , path) i)

    ATopF : {ℓ : Level} -> {A : Type ℓ} -> isFinSet A -> FinSet ℓ
    ATopF e = ATop _ , isFinSetATop e

    top-eq : {ℓ : Level} {A : Type ℓ} {n : Nat} -> (A ≃ Fin n) -> (ATop A ≃ Fin n)
    top-eq (f , eq) = (f ∘ fst , eq2)
      where
      eq2 : isEquiv (f ∘ fst)
      eq2 .equiv-proof j .fst .fst = (eq .equiv-proof j .fst .fst , tt)
      eq2 .equiv-proof j .fst .snd = (eq .equiv-proof j .fst .snd)
      eq2 .equiv-proof j .snd ((a , tt) , path) i =
        (fst (eq .equiv-proof j .snd (a , path) i) , tt) ,
         snd (eq .equiv-proof j .snd (a , path) i)


  module _ {ℓ : Level} {A : Type ℓ} (f : A -> D) where

--    equiv-sum-Top : {n : Nat} -> (eq : (A ≃ Fin n)) ->
--                    equivSum S f eq == equivSum S (f ∘ fst) (top-eq eq)
--    equiv-sum-Top eq = refl

    transport-sum : {B : Type ℓ} -> (e : isFinSet A) -> (p : A == B)
                    -> sum (A , e) f == sum (B , (subst isFinSet p e))
                                         (transport (cong (\x -> x -> D) p) f)
    transport-sum e p k =
      sum (p k , transport-filler (\k -> (isFinSet (p k))) e k)
          (transport-filler (\k -> p k -> D) f k)


    transport-test : {B : Type ℓ} (p : A == B) ->
                     PathP (\i -> p i -> D) f (transport (cong (\x -> x -> D) p) f)
    transport-test p = transport-filler (\i -> (p i) -> D) f

    transport-test3 : {B : Type ℓ} (p : A == B) (b : B) ->
                      (transport (cong (\x -> x -> D) p) f b) == (f (transport (sym p) b))
    transport-test3 p b = transportRefl (f (transport (sym p) b))

    transport-test2 : {B : Type ℓ} (p : A == B) ->
                      (transport (cong (\x -> x -> D) p) f) == (f ∘ transport (sym p))
    transport-test2 p i b = transport-test3 p b i

    transport-test4 : {B : Type ℓ} (p : A == B) ->
                      PathP (\i -> p i -> D) f (f ∘ transport (sym p))
    transport-test4 p =
      transP-left (transport-test p) (transport-test2 p)

  module _ {ℓ : Level} (AF BF : FinSet ℓ) (f : ⟨ AF ⟩ -> D) where
    private
      A = ⟨ AF ⟩
      B = ⟨ BF ⟩

    transport-sum2 : (p : A == B) -> sum AF f == sum BF (f ∘ transport (sym p))
    transport-sum2 p =
      begin
        sum AF f
      ==< transport-sum f (snd AF) p >
        sum (B , (subst isFinSet p (snd AF))) (transport (cong (\x -> x -> D) p) f)
      ==< cong (sum (B , (subst isFinSet p (snd AF)))) (transport-test2 f p) >
        sum (B , (subst isFinSet p (snd AF))) (f ∘ transport (sym p))
      ==< cong (\x -> sum (B , x) (f ∘ transport (sym p)))
               (squash (subst isFinSet p (snd AF)) (snd BF)) >
        sum BF (f ∘ transport (sym p))
      end

  --module _ (AF : FinSet ℓ-zero) (f : ⟨ AF ⟩ -> D) where
  --  private
  --    A = ⟨ AF ⟩


  --    ×-Top' : (A : Type ℓ-zero) -> A == (A × Top)
  --    ×-Top' A = ua (isoToEquiv i)
  --      where
  --      open Iso
  --      i : Iso A (A × Top)
  --      i .fun a         = (a , tt)
  --      i .inv (a , tt)  = a
  --      i .rightInv _ = refl
  --      i .leftInv _ = refl

  --  sum-×-Top : sum AF f == sum (ATopF (snd AF)) (f ∘ fst)
  --  sum-×-Top = transport-sum2 AF (ATopF (snd AF)) f (×-Top' A)

  --module _ (isFinSet-Fin : isFinSet Boolean) (f : Boolean -> D) where
  --  private
  --    AF : FinSet ℓ-zero
  --    AF = Boolean , isFinSet-Fin


  --    ×-Top' : (A : Type ℓ-zero) -> A == (A × Top)
  --    ×-Top' A = ua (isoToEquiv i)
  --      where
  --      open Iso
  --      i : Iso A (A × Top)
  --      i .fun a         = (a , tt)
  --      i .inv (a , tt)  = a
  --      i .rightInv _ = refl
  --      i .leftInv _ = refl

  --  sum-×-Top : sum AF f == sum (ATopF (snd AF)) (f ∘ fst)
  --  sum-×-Top = transport-sum2 AF (ATopF (snd AF)) f (×-Top' Boolean)


   --sum-×-Top ∣ (n , eq) ∣ = refl
   --sum-×-Top (squash x y i) j = isSetDomain (sum ? f) (sum ? (f ∘ fst)) ? ? j i


  module _  (AF : FinSet ℓ-zero) (f : ⟨ AF ⟩ -> D) where
    private
      A = ⟨ AF ⟩

      ×-Top' : (A : Type ℓ-zero) -> (A × Top) ≃ A
      ×-Top' A = isoToEquiv (iso⁻¹ i)
        where
        open Iso
        i : Iso A (A × Top)
        i .fun a         = (a , tt)
        i .inv (a , tt)  = a
        i .rightInv _ = refl
        i .leftInv _ = refl


    sum-×-Top : sum AF f == sum (ATopF (snd AF)) (f ∘ fst)
    sum-×-Top = finiteSum-convert AF (ATopF (snd AF)) (×-Top' A) f


    --transport-filler (\i -> (p i) -> D) f


    --  begin
    --    (transport (cong (\x -> x -> D) p) f)
    --  ==<>
    --    (\b -> transp (\i -> D) i0 (f (transp (\j -> p (~ j)) i0 b)))
    --  ==<>
    --    (\b -> transp (\i -> D) i0 (f (transp (\j -> p (~ j)) i0 b)))
    --  ==< ? >
    --    (\a -> (f (transp (\j -> p (~ j)) i0 a)))
    --  ==<>
    --    (f ∘ transport (sym p))
    --  end


    --transport-sum2 : {B : Type} -> (eA : isFinSet A) (eB : isFinSet) (p : A == B)
    --                 -> sum (A , e) f == sum (B , eB)
    --                                     (transport (cong (\x -> x -> D) p) f)


Fin1 : Nat -> Type₀
Fin1 n = Σ[ i ∈ Nat⁺ ] (⟨ i ⟩ ≤ n)

module _ (n⁺ : Nat⁺) where
  n = ⟨ n⁺ ⟩

  A : Nat -> Type₀
  A d = Σ[ k ∈ Fin1 n ] (GCD' ⟨ ⟨ k ⟩ ⟩ n d)

  disjointA : {d1 d2 : Nat} (a1 : A d1) (a2 : A d2) -> ⟨ a1 ⟩ == ⟨ a2 ⟩ -> d1 == d2
  disjointA {d1} {d2} (((j1 , _ ) , _) , g1) (((j2 , _ ) , _) , g2) p =
    gcd'-unique g1' g2
    where
    p' : j1 == j2
    p' = cong (fst ∘ fst) p

    g1' : GCD' j2 n d1
    g1' = transport (\i -> GCD' (p' i) n d1) g1

  coveringA : (k : Fin1 n) -> Σ[ d ∈ Nat ] (GCD' ⟨ ⟨ k ⟩ ⟩ n d)
  coveringA k = gcd'-exists ⟨ ⟨ k ⟩ ⟩ n

  isPropGCD' : (k : Nat⁺) (d : Nat) -> isProp (GCD' ⟨ k ⟩ n d)
  isPropGCD' k⁺ d g1 g2 = (\i -> record
    { %a = isPropDiv' k⁺ (g1 .GCD'.%a) (g2 .GCD'.%a) i
    ; %b = isPropDiv' n⁺ (g1 .GCD'.%b) (g2 .GCD'.%b) i
    ; f = isPropΠ3 (\ _ _ _ -> isPropDiv' (d , dPos)) (g1 .GCD'.f) (g2 .GCD'.f) i
    })
    where
    dPos : Pos' d
    dPos = div'-pos->pos (g1 .GCD'.%b) (snd n⁺)

  module _ where
    private
      forward : Fin1 n -> (Σ Nat A)
      forward k = (fst (coveringA k) , (k , (snd (coveringA k))))

      backward : (Σ Nat A) -> Fin1 n
      backward (d , (k , g)) = k


    isoA : Iso (Fin1 n) (Σ Nat A)
    isoA .Iso.fun = forward
    isoA .Iso.inv = backward
    isoA .Iso.rightInv (d , (k , g)) =
      (\i -> dpath i , (k , gpath i))
      where
      k' = ⟨ ⟨ k ⟩ ⟩
      d2 : Nat
      d2 = fst (coveringA k)
      g2 : GCD' k' n d2
      g2 = snd (coveringA k)

      dpath : d2 == d
      dpath = disjointA (k , g2) (k , g) refl

      gpath : PathP (\i -> GCD' k' n (dpath i)) g2 g
      gpath = isProp->PathP (\i -> isPropGCD' ⟨ k ⟩ (dpath i)) g2 g
    isoA .Iso.leftInv _ = refl

  module _ where

    Divisors : Nat -> Type₀
    Divisors n = Σ[ d ∈ Nat ] (d div' n)

    isoADiv : Iso (Σ Nat A) (Σ[ d ∈ (Divisors n) ] (A ⟨ d ⟩))
    isoADiv .Iso.fun (d , (k , g)) = ((d , g .GCD'.%b) , (k , g))
    isoADiv .Iso.inv ((d , _) , a) = (d , a)
    isoADiv .Iso.rightInv ((d , d-div) , (k , g)) i = ((d , isPropDiv' n⁺ (g .GCD'.%b) d-div i) , (k , g))
    isoADiv .Iso.leftInv _ = refl

    diva->totative : (d : Nat) -> (d-div : (d div' n)) -> A d -> Totatives ⟨ d-div ⟩
    diva->totative  d d%n@(nd , nd-path) (((k , pos-k) , lt) , g) = q , record
      { pos-k = pos-q
      ; k≤n = q≤nd
      ; rp = q-rp
      }
      where
      d%k : d div' k
      d%k = (g .GCD'.%a)
      q = fst d%k
      q-path : q *' d == k
      q-path = snd d%k

      d⁺ : Nat⁺
      d⁺ = d , (div'-pos->pos d%k pos-k)
      pos-q = (div'-pos->pos' d%k pos-k)

      qd≤ndd : (q *' d) ≤ (nd *' d)
      qd≤ndd = transport (\i -> (q-path (~ i)) ≤ (nd-path (~ i))) lt
      q≤nd : q ≤ nd
      q≤nd = *-right-≤⁻ d⁺ qd≤ndd

      q-rp : RelativelyPrime⁰ q nd
      q-rp s (sq' , sq'-path) (snd' , snd'-path) = s==1
        where
        sd%k : (s *' d) div' k
        sd%k = sq' , sym (*'-assoc {sq'} {s} {d}) >=> (cong (_*' d) sq'-path) >=> q-path
        sd%n : (s *' d) div' n
        sd%n = snd' , sym (*'-assoc {snd'} {s} {d}) >=> (cong (_*' d) snd'-path) >=> nd-path

        sd%d : (s *' d) div' d
        sd%d = g .GCD'.f (s *' d) sd%k sd%n
        d%sd : d div' (s *' d)
        d%sd = s , refl

        sd==d : (s *' d) == d
        sd==d = div'-antisym sd%d d%sd

        s==1 : s == 1
        s==1 = *'-right-injective d⁺ (sd==d >=> sym (*'-left-one))


    totative->diva : (d : Nat) -> (d-div : (d div' n)) -> Totatives ⟨ d-div ⟩ -> A d
    totative->diva d d%n@(nd , nd-path) (q , tot) = (((q *' d) , pos-qd) , qd≤n) , gcd-d4
      where
      gcd1 : GCD' q nd 1
      gcd1 = relatively-prime->gcd (tot .Totient.rp)

      gcd-d : GCD ((int q) * (int d)) ((int nd) * (int d)) (int d)
      gcd-d .GCD.non-neg = tt
      gcd-d .GCD.%a = (int q) , refl
      gcd-d .GCD.%b = (int nd) , refl
      gcd-d .GCD.f s (sq' , sq-path) (snd' , snd-path) = s%d
        where
        p1 : s * sq' == (int d) * (int q)
        p1 = *-commute {s} {sq'} >=> sq-path >=> *-commute {int q} {int d}
        p2 : s * snd' == (int d) * (int nd)
        p2 = *-commute {s} {snd'} >=> snd-path >=> *-commute {int nd} {int d}

        lc : LinearCombination' q nd 1
        lc = gcd'->linear-combo gcd1
        module lc = LinearCombination lc

        path : s * (sq' * lc.x + snd' * lc.y) == (int d)
        path =
          begin
            s * (sq' * lc.x + snd' * lc.y)
          ==< *-distrib-+-left {s} >
            (s * (sq' * lc.x)) + (s * (snd' * lc.y))
          ==< (\i -> *-assoc {s} {sq'} {lc.x} (~ i) + *-assoc {s} {snd'} {lc.y} (~ i)) >
            ((s * sq') * lc.x) + ((s * snd') * lc.y)
          ==< (\i -> (p1 i) * lc.x + (p2 i) * lc.y) >
            (((int d) * (int q)) * lc.x) + (((int d) * (int nd)) * lc.y)
          ==< (\i -> *-assoc {int d} {int q} {lc.x} i + *-assoc {int d} {int nd} {lc.y} i) >
            ((int d) * ((int q) * lc.x)) + ((int d) * ((int nd) * lc.y))
          ==< sym (*-distrib-+-left {int d}) >
            (int d) * ((int q) * lc.x + (int nd) * lc.y)
          ==< (\i -> (int d) * (*-commute {int q} {lc.x} i + *-commute {int nd} {lc.y} i)) >
            (int d) * (lc.x * (int q) + lc.y * (int nd))
          ==< (\i -> (int d) * (lc.path i)) >
            (int d) * (int 1)
          ==< *-right-one >
            (int d)
          end

        s%d : s div (int d)
        s%d = (sq' * lc.x + snd' * lc.y) , *-commute {_} {s} >=> path

      gcd-d2 : GCD (int (q *' d)) (int (nd *' d)) (int d)
      gcd-d2 = transport (\i -> GCD (int-inject-*' {q} {d} (~ i))
                                    (int-inject-*' {nd} {d} (~ i)) (int d)) gcd-d

      gcd-d3 : GCD' (q *' d) (nd *' d) d
      gcd-d3 = gcd->gcd' gcd-d2

      gcd-d4 : GCD' (q *' d) n d
      gcd-d4 = transport (\i -> GCD' (q *' d) (nd-path i) d) gcd-d3

      q≤nd : q ≤ nd
      q≤nd = tot .Totient.k≤n
      qd≤ndd : (q *' d) ≤ (nd *' d)
      qd≤ndd = *-right-≤⁺ d q≤nd
      qd≤n : (q *' d) ≤ n
      qd≤n = fst qd≤ndd , snd qd≤ndd >=> nd-path

      pos-qd : Pos' (q *' d)
      pos-qd = *'-Pos'-Pos' (tot .Totient.pos-k) (div'-pos->pos d%n (snd n⁺))

    diva->totative->diva : (d : Nat) -> (d-div : (d div' n)) -> (a : A d) ->
                           totative->diva d d-div (diva->totative d d-div a) == a
    diva->totative->diva d d%n a = (\i -> path3 i , path4 i)
      where
      path1 : (fst (fst (fst (totative->diva d d%n (diva->totative d d%n a))))) ==
              (fst (fst (fst a)))
      path1 = snd ((snd a) .GCD'.%a)

      path2 : (fst (fst (totative->diva d d%n (diva->totative d d%n a)))) == (fst (fst a))
      path2 = (ΣProp-path isPropPos' path1)
      path3 : (fst (totative->diva d d%n (diva->totative d d%n a))) == (fst a)
      path3 = (ΣProp-path isProp≤ path2)

      path4 : PathP (\i -> GCD' (fst (fst (path3 i))) n d)
                    (snd (totative->diva d d%n (diva->totative d d%n a)))
                    (snd a)
      path4 = isProp->PathP (\j -> isPropGCD' (fst (path3 j)) d)
                            (snd (totative->diva d d%n (diva->totative d d%n a)))
                            (snd a)

    totative->diva->totative : (d : Nat) -> (d-div : (d div' n)) -> (tot : Totatives ⟨ d-div ⟩) ->
                               diva->totative d d-div (totative->diva d d-div tot) == tot
    totative->diva->totative d d%n tot = (ΣProp-path isProp-isTotativeOf refl)

    isoTotADiv : Iso (Σ[ d ∈ (Divisors n) ] (Totatives ⟨ (snd d) ⟩)) (Σ[ d ∈ (Divisors n) ] (A ⟨ d ⟩))
    isoTotADiv .Iso.fun ((d , d%n) , tot) = (d , d%n) , totative->diva d d%n tot
    isoTotADiv .Iso.inv ((d , d%n) , a) = (d , d%n) , diva->totative d d%n a
    isoTotADiv .Iso.rightInv ((d , d%n) , a) i = (d , d%n) , diva->totative->diva d d%n a i
    isoTotADiv .Iso.leftInv ((d , d%n) , tot) i = (d , d%n) , totative->diva->totative d d%n tot i

  isoFin1 : Iso (Fin1 n) (Fin n)
  isoFin1 .Iso.fun (((suc x) , tt) , lt) = (x , lt)
  isoFin1 .Iso.inv (x , lt) = (((suc x) , tt) , lt)
  isoFin1 .Iso.rightInv _ = refl
  isoFin1 .Iso.leftInv (((suc x) , tt) , lt) = refl


  combinedIso : Iso (Σ[ d ∈ (Divisors n) ] (Totatives ⟨ (snd d) ⟩)) (Fin n)
  combinedIso = isoFin1 ∘ⁱ (((iso⁻¹ isoA)  ∘ⁱ (iso⁻¹ isoADiv)) ∘ⁱ isoTotADiv)

  flipDivisors-equiv : Divisors n ≃ Divisors n
  flipDivisors-equiv = isoToEquiv i
    where
    i : Iso (Divisors n) (Divisors n)
    i .Iso.fun (a , (d , p)) = d , (a , *'-commute {a} {d} >=> p)
    i .Iso.inv (d , (a , p)) = a , (d , *'-commute {d} {a} >=> p)
    i .Iso.rightInv (d , (a , p)) = cong (\x -> (d , (a , x))) (isSetNat _ _ _ _)
    i .Iso.leftInv (a , (d , p)) = cong (\x -> (a , (d , x))) (isSetNat _ _ _ _)

  reindexed : (Σ[ d ∈ (Divisors n) ] (Totatives ⟨ d ⟩)) ≃
              (Σ[ d ∈ (Divisors n) ] (Totatives ⟨ (snd d) ⟩))
  reindexed = reindexΣ flipDivisors-equiv (\d -> (Totatives ⟨ d ⟩))

  combined-eq : (Σ[ d ∈ (Divisors n) ] (Totatives ⟨ d ⟩)) ≃ Fin n
  combined-eq = reindexed >eq> (isoToEquiv combinedIso)


  φ' : Divisors n -> Nat
  φ' (d , d%n) = φ (d , div'-pos->pos d%n (snd n⁺))

  isBoundedDivisor : isBounded (_div' n)
  isBoundedDivisor = suc n , (\d%n -> suc-≤ (div'->≤ d%n {snd n⁺}))

  isFinSet-Divisors : isFinSet (Divisors n)
  isFinSet-Divisors =
    boundedDecidableProp->isFinSet isBoundedDivisor (\d -> decide-div d n) (isPropDiv' n⁺)

  FinSet-Divisors : FinSet ℓ-zero
  FinSet-Divisors = Divisors n , isFinSet-Divisors

  combined-path : FinSet-Σ FinSet-Divisors (\(d , _) -> FinSet-Totatives d)
                  == FinSet-Fin n
  combined-path = (ΣProp-path isProp-isFinSet (ua combined-eq))


  finΣ : isFinSetΣ (Fin n)
  finΣ = n , ∣ idEquiv _ ∣

  theorem2-2 : finiteSum FinSet-Divisors φ' == n
  theorem2-2 =
    sym (cardnality-Σ3 FinSet-Divisors (\(d , _) -> FinSet-Totatives d))
    >=> cong cardnality combined-path
    >=> cardnality-path (FinSet-Fin n) finΣ


--module _ {ℓ₁ ℓ₂ ℓ₃ : Level}  {D : Type ℓ₁} (S : Semiring D)
--         (AF : FinSet ℓ₂) (PF : (a : ⟨ AF ⟩) -> FinSet ℓ₃) where
--  open Semiring S
--  private
--    A = ⟨ AF ⟩
--    P : A -> Type _
--    P a = ⟨ PF a ⟩
--    sum = finiteSum S
--
--  ΣF : FinSet _
--  ΣF = Σ A P , ?
--
--  ΣSum : (f : (Σ A P) -> D) -> sum ΣF f == sum AF (\a -> (sum (PF a) (\p -> f (a , p))))
--  ΣSum = ?
--
--
--module _ {ℓ₁ ℓ₂ ℓ₃ : Level}  {D : Type ℓ₁} (S : Semiring D)
--         (AF : FinSet ℓ₂) (PF : FinSet ℓ₃)
--         where
--  open Semiring S
--  private
--    A = ⟨ AF ⟩
--    P = ⟨ PF ⟩
--    sum = finiteSum S
--
--  module _ (val : A -> D) (part-key : A -> P) where
--
--    Pair0 : Type _
--    Pair0 = Σ[ a ∈ A ] Top
--
--    Pair1 : Type _
--    Pair1 = Σ[ a ∈ A ] (Σ[ p ∈ P ] (part-key a == p))
--
--    Pair2 : Type _
--    Pair2 = Σ[ p ∈ P ] (Σ[ a ∈ A ] (part-key a == p))
--
--
--    Pair1F : FinSet _
--    Pair1F = Pair1 , ?
--
--    Partition : P -> Type _
--    Partition p = Σ[ a ∈ A ] (part-key a == p)
--
--    isFinSet-Partition : {p : P} -> isFinSet (Partition p)
--    isFinSet-Partition = ?
--
--    PartitionF : P -> FinSet _
--    PartitionF p = Partition p , isFinSet-Partition
--
--    partitionedSum : (sum AF val) == (sum PF (\p -> sum (PartitionF p) (val ∘ fst)))
--    partitionedSum =
--      begin
--        (sum AF val)
--      ==< ? >
--        (sum PairF (val ∘ fst))
--      ==< ? >
--        (sum PF (\p -> sum (PartitionF p) (val ∘ fst)))
--      end
