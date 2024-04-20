{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.dirichlet where

open import additive-group using (AdditiveCommMonoid)
open import base
open import equality
open import equivalence
open import semiring
open import fin
open import hlevel.base
open import finset
open import nat
open import order
open import order.instances.nat
open import finset.instances.sigma
open import finsum
open import finsum.sigma
open import finsum.arithmetic
open import isomorphism
open import chapter2.mobius
open import chapter2.divisors
open import chapter2.partition
open import sigma.base
open import div
open import funext

open EqReasoning

module _ {ℓD : Level} {D : Type ℓD} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      IACM = ACM
    module S = Semiring S
    Divisors-flip-eq = flipDivisors-equiv

    PairedDivisor : Nat⁺ -> Type₀
    PairedDivisor n = Σ[ ij ∈ (Nat⁺ × Nat⁺) ] (proj₁ ij *⁺ proj₂ ij == n)

    paired-divisor-ext :
      {n : Nat⁺} {p1 p2 : PairedDivisor n} -> fst p1 == fst p2 -> p1 == p2
    paired-divisor-ext = ΣProp-path (isSetNat⁺ _ _)

    Divisor-PairedDivisor-eq : (n : Nat⁺) -> Divisor n ≃ PairedDivisor n
    Divisor-PairedDivisor-eq n = isoToEquiv i
      where
      open Iso
      forward : (Divisor n) -> (PairedDivisor n)
      forward (i , d@(j , p)) = (((j , div'-pos->pos' d (snd n)) , (i , div'-pos->pos d (snd n)))
                                 , ΣProp-path isPropPos' p)
      backward : (PairedDivisor n) -> (Divisor n)
      backward (((j , _) , (i , _)) , p) = (i , (j , cong fst p))
      i : Iso (Divisor n) (PairedDivisor n)
      i .fun = forward
      i .inv = backward
      i .rightInv pd@((j⁺@(j , _) , i⁺@(i , _)) , p) =
        (ΣProp-path (isSetNat⁺ _ _) (cong2 _,_ (ΣProp-path isPropPos' refl) (ΣProp-path isPropPos' refl)))
      i .leftInv _ = ΣProp-path (isPropDiv' n) refl

    FinSet-PairedDivisor : Nat⁺ -> FinSet ℓ-zero
    FinSet-PairedDivisor n =
      PairedDivisor n , isFinSet-equiv (Divisor-PairedDivisor-eq n) (snd (FinSet-Divisor n))

    TripledDivisor : Nat⁺ -> Type₀
    TripledDivisor n = Σ ((Nat⁺ × Nat⁺) × Nat⁺) (\((i , j) , k) -> (i *⁺ j) *⁺ k == n)

    PairedPairedDivisor-TripledDivisor-eq : (n : Nat⁺) ->
      (Σ (PairedDivisor n) (\((i , _) , _) -> PairedDivisor i)) ≃
      TripledDivisor n
    PairedPairedDivisor-TripledDivisor-eq n = isoToEquiv i
      where
      forward : (Σ (PairedDivisor n) (\((i , _) , _) -> PairedDivisor i)) ->
                TripledDivisor n
      forward (((_ , j) , path1) , ((i2 , j2) , path2)) =
        ((i2 , j2) , j) , cong (_*⁺ j) path2 >=> path1

      backward : TripledDivisor n ->
                 (Σ (PairedDivisor n) (\((i , _) , _) -> PairedDivisor i))
      backward (((i2 , j2) , j) , path) =
        (((i2 *⁺ j2 , j) , path) , ((i2 , j2) , refl))

      bf : (ppd : Σ (PairedDivisor n) (\((i , _) , _) -> PairedDivisor i)) ->
           backward (forward ppd) == ppd
      bf ppd@(pd@((i , j) , path1) , pd2@((i2 , j2) , path2)) = path9
        where
        path3 : snd (fst (fst (backward (forward ppd)))) == j
        path3 = refl
        path4 : fst (fst (fst (backward (forward ppd)))) == i
        path4 = path2
        path5 : (fst (backward (forward ppd))) == pd
        path5 = paired-divisor-ext (cong2 _,_ path4 path3)

        path5' : fst (fst (fst (backward (forward ppd)))) == i
        path5' k = fst (fst (path5 k))

        path7 : fst (snd (backward (forward ppd))) == fst pd2
        path7 = refl

        path8 : PathP (\k -> i2 *⁺ j2 == (path5' k))
                      (snd (snd (backward (forward ppd)))) (snd pd2)
        path8 = isProp->PathP (\_ -> isSetNat⁺ _ _)

        path6 : PathP (\k -> PairedDivisor (path5' k)) (snd (backward (forward ppd))) pd2
        path6 i = path7 i , path8 i

        path9 : backward (forward ppd) == ppd
        path9 i = path5 i , path6 i



      open Iso
      i : Iso (Σ (PairedDivisor n) (\((i , _) , _) -> PairedDivisor i))
              (TripledDivisor n)
      i .fun = forward
      i .inv = backward
      i .rightInv _ = (ΣProp-path (isSetNat⁺ _ _) refl)
      i .leftInv = bf

    FinSet-TripledDivisor : Nat⁺ -> FinSet ℓ-zero
    FinSet-TripledDivisor n =
      TripledDivisor n , isFinSet-equiv (PairedPairedDivisor-TripledDivisor-eq n)
                                        (snd (FinSet-Σ (FinSet-PairedDivisor n)
                                                       (\((i , _) , _) -> (FinSet-PairedDivisor i))))

    TripledDivisor-auto : (n : Nat⁺) -> TripledDivisor n ≃ TripledDivisor n
    TripledDivisor-auto n = isoToEquiv i
      where
      open Iso
      i : Iso (TripledDivisor n) (TripledDivisor n)
      i .fun (((i , j) , k) , path) = ((k , i) , j) , path2
        where
        i' = ⟨ i ⟩
        j' = ⟨ j ⟩
        k' = ⟨ k ⟩
        n' = ⟨ n ⟩
        path1 : (k' *' i') *' j' == n'
        path1 = *'-assoc {k'} {i'} {j'} >=> *'-commute {k'} {i' *' j'} >=> (cong fst path)

        path2 : (k *⁺ i) *⁺ j == n
        path2 = ΣProp-path isPropPos' path1
      i .inv (((i , j) , k) , path) = ((j , k) , i) , path2
        where
        i' = ⟨ i ⟩
        j' = ⟨ j ⟩
        k' = ⟨ k ⟩
        n' = ⟨ n ⟩
        path1 : (j' *' k') *' i' == n'
        path1 = *'-commute {j' *' k'} {i'} >=> sym (*'-assoc {i'} {j'} {k'}) >=> (cong fst path)

        path2 : (j *⁺ k) *⁺ i == n
        path2 = ΣProp-path isPropPos' path1
      i .rightInv _ = ΣProp-path (isSetNat⁺ _ _) refl
      i .leftInv _ = ΣProp-path (isSetNat⁺ _ _) refl



  abstract
    _⊗_ : (f g : Nat⁺ -> D) -> (Nat⁺ -> D)
    (f ⊗ g) n = finiteSumᵉ (FinSet-Divisor n) (\d -> f (divisor->nat⁺ n d) S.* g (divisor->nat⁺' n d))

    ⊗-eval : {f g : Nat⁺ -> D} {n : Nat⁺} ->
             (f ⊗ g) n == finiteSumᵉ (FinSet-Divisor n)
                                     (\d -> f (divisor->nat⁺ n d) S.* g (divisor->nat⁺' n d))
    ⊗-eval = refl


    ⊗-commute : {f g : Nat⁺ -> D} {n : Nat⁺} -> (f ⊗ g) n == (g ⊗ f) n
    ⊗-commute {f} {g} {n} =
      begin
        finiteSumᵉ (FinSet-Divisor n) (\d -> f (divisor->nat⁺ n d) S.* g (divisor->nat⁺' n d))
      ==< finiteSumᵉ-convert _ _ (Divisors-flip-eq n) _ >
        finiteSumᵉ (FinSet-Divisor n)
          (\d -> f (fst (divisor->nat⁺' n d) , _) S.*
                 g (fst (divisor->nat⁺ n d)  , _))
      ==< cong (finiteSumᵉ (FinSet-Divisor n))
               (funExt (\d -> (cong2 S._*_ (cong f (ΣProp-path isPropPos' refl))
                                           (cong g (ΣProp-path isPropPos' refl)))
                              >=> S.*-commute)) >
        finiteSumᵉ (FinSet-Divisor n) (\d -> g (divisor->nat⁺ n d) S.* f (divisor->nat⁺' n d))
      end

    FinDivisor : Nat⁺ -> Type₀
    FinDivisor n⁺@(n , _) = (Σ[ i ∈ Fin1 n ] (⟨ i ⟩ div⁺ n⁺))

    Divisor-FinDivisor-eq : (n : Nat⁺) -> Divisor n ≃ FinDivisor n
    Divisor-FinDivisor-eq n = isoToEquiv i
      where
      open Iso
      i : Iso (Divisor n) (FinDivisor n)
      i .fun (d , d%n) = ((d , div'-pos->pos d%n (snd n)), (div'->≤ d%n {snd n})) , d%n
      i .inv (((d , _) , _) , d%n) = d , d%n
      i .rightInv (((d , p) , lt) , d%n) =
        (ΣProp-path (isPropDiv' n) (ΣProp-path isProp-≤ (ΣProp-path isPropPos' refl)))
      i .leftInv _ = refl

    FinSet-FinDivisor : Nat⁺ -> FinSet ℓ-zero
    FinSet-FinDivisor n = FinDivisor n , isFinSet-equiv (Divisor-FinDivisor-eq n) (snd (FinSet-Divisor n))



    ⊗-eval' : {f g : Nat⁺ -> D} {n : Nat⁺} ->
              (f ⊗ g) n == finiteSumᵉ (FinSet-PairedDivisor n) (\((i , j) , _) -> f j S.* g i)
    ⊗-eval' {f} {g} {n} =
      begin
        finiteSumᵉ (FinSet-Divisor n) (\d -> f (divisor->nat⁺ n d) S.* g (divisor->nat⁺' n d))
      ==< finiteSumᵉ-convert _ _ (equiv⁻¹ (Divisor-PairedDivisor-eq n)) _ >
        finiteSumᵉ (FinSet-PairedDivisor n) _
      ==< cong (finiteSumᵉ (FinSet-PairedDivisor n))
               (funExt (\((i , j) , _) ->
                 cong2 (\x y -> f x S.* g y)
                       (ΣProp-path isPropPos' refl)
                       (ΣProp-path isPropPos' refl))) >
        finiteSumᵉ (FinSet-PairedDivisor n) (\((i , j) , _) -> f j S.* g i)
      end

    ⊗-eval'2 : {f g : Nat⁺ -> D} {n : Nat⁺} ->
              (f ⊗ g) n == finiteSumᵉ (FinSet-PairedDivisor n) (\((i , j) , _) -> g j S.* f i)
    ⊗-eval'2 {f} {g} {n} = ⊗-commute {f} {g} {n} >=> ⊗-eval' {g} {f} {n}


    ⊗-assoc : {f g h : Nat⁺ -> D} {n : Nat⁺} -> ((f ⊗ g) ⊗ h) n == (f ⊗ (g ⊗ h)) n
    ⊗-assoc {f} {g} {h} {n} =
      begin
        _
      ==< ⊗-eval'2 >
        finiteSumᵉ (FinSet-PairedDivisor n) (\((i , j) , _) -> h j S.* (f ⊗ g) i)
      ==< cong (finiteSumᵉ (FinSet-PairedDivisor n))
               (funExt (\((i , j) , _) ->
                 (cong (h j S.*_) (⊗-eval' {f} {g}) >=> sym finiteSum-*))) >
        finiteSumᵉ (FinSet-PairedDivisor n) (\((i , j) , _) ->
          finiteSumᵉ (FinSet-PairedDivisor i) (\((i2 , j2) , _) -> h j S.* (f j2 S.* g i2)))
      ==< sym (finiteSum-Σ (FinSet-PairedDivisor n) (\((i , j) , _) -> (FinSet-PairedDivisor i)) _) >
        finiteSumᵉ (FinSet-Σ (FinSet-PairedDivisor n) (\((i , j) , _) -> (FinSet-PairedDivisor i)))
          (\(((i , j) , _) , ((i2 , j2) , _)) -> h j S.* (f j2 S.* g i2))
      ==< finiteSumᵉ-convert _ _ (equiv⁻¹ (PairedPairedDivisor-TripledDivisor-eq n)) _ >
        finiteSumᵉ (FinSet-TripledDivisor n) (\(((i2 , j2) , j) , _) -> h j S.* (f j2 S.* g i2))
      ==< finiteSumᵉ-convert _ _ (equiv⁻¹ (TripledDivisor-auto n)) _ >
        finiteSumᵉ (FinSet-TripledDivisor n) (\(((i2 , j2) , j) , _) -> h i2 S.* (f j S.* g j2))
      ==< cong (finiteSumᵉ (FinSet-TripledDivisor n))
               (funExt (\(((i2 , j2) , j) , _) ->
                 (S.*-commute >=> S.*-assoc))) >
        finiteSumᵉ (FinSet-TripledDivisor n) (\(((i2 , j2) , j) , _) -> f j S.* (g j2 S.* h i2))
      ==< sym (finiteSumᵉ-convert _ _ (equiv⁻¹ (PairedPairedDivisor-TripledDivisor-eq n)) _) >
        finiteSumᵉ (FinSet-Σ (FinSet-PairedDivisor n) (\((i , j) , _) -> (FinSet-PairedDivisor i)))
          (\(((i , j) , _) , ((i2 , j2) , _)) -> f j S.* (g j2 S.* h i2))
      ==< finiteSum-Σ (FinSet-PairedDivisor n) (\((i , j) , _) -> (FinSet-PairedDivisor i)) _ >
        finiteSumᵉ (FinSet-PairedDivisor n) (\((i , j) , _) ->
          finiteSumᵉ (FinSet-PairedDivisor i) (\((i2 , j2) , _) -> f j S.* (g j2 S.* h i2)))
      ==< sym (cong (finiteSumᵉ (FinSet-PairedDivisor n))
                    (funExt (\((i , j) , _) ->
                      ((cong (f j S.*_) (⊗-eval' {g} {h})) >=> sym finiteSum-*)))) >
        finiteSumᵉ (FinSet-PairedDivisor n) (\((i , j) , _) -> f j S.* (g ⊗ h) i)
      ==< sym ⊗-eval' >
        _
      end
      where
      instance
        FinSetStr-PairedDivisor : {n : Nat⁺} -> FinSetStr (PairedDivisor n)
        FinSetStr-PairedDivisor {n} = record {isFin = snd (FinSet-PairedDivisor n)}
