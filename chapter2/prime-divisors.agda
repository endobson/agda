{-# OPTIONS --cubical --safe --exact-split -W noUnsupportedIndexedMatch #-}

module chapter2.prime-divisors where

open import additive-group
open import additive-group.instances.nat
open import base
open import chapter2.divisors
open import chapter2.multiplicative
open import discrete
open import div hiding (remainder)
open import equality
open import equivalence
open import finite-product
open import finset
open import finset.instances.base
open import finset.instances.sum
open import finset.subset
open import hlevel
open import isomorphism
open import nat
open import nat.bounded
open import nat.order
open import order
open import order.instances.nat
open import prime
open import prime-div-count
open import prime-div-count.computational
open import prime-factorization
open import prime-gcd
open import prime-power-factorization
open import relation
open import relatively-prime
open import semiring
open import semiring.exponentiation
open import semiring.instances.nat
open import sigma
open import sigma.base
open import type-algebra

private
  variable
    ℓ : Level
    A : Type ℓ

PrimeDivisor : Nat⁺ -> Type₀
PrimeDivisor (n , _) = Σ[ p ∈ Prime' ] ( ⟨ p ⟩ div' n)

private
  PrimeDivisor' : Nat⁺ -> Type₀
  PrimeDivisor' (n , _) = (Σ[ d ∈ Nat ] ((IsPrime' d) × (d div' n)))

  isFinSet-PrimeDivisor' : (n : Nat⁺) -> isFinSet (PrimeDivisor' n)
  isFinSet-PrimeDivisor' n⁺@(n , _) =
    boundedDecidableProp->isFinSet
      (isBounded-∩₂ (isBoundedDiv' n⁺))
      (Decidable-∩ Decidable-IsPrime' (\d -> decide-div d n))
      (isProp× isPropIsPrime' (isPropDiv' n⁺))


  PrimeDivisor'-eq : (n : Nat⁺) -> PrimeDivisor' n ≃ PrimeDivisor n
  PrimeDivisor'-eq n = isoToEquiv i
    where
    open Iso
    i : Iso (PrimeDivisor' n) (PrimeDivisor n)
    i .fun (d , (p , d%n)) = (d , p) , d%n
    i .inv ((d , p) , d%n) = d , (p , d%n)
    i .rightInv _ = refl
    i .leftInv _ = refl

abstract
  isFinSet-PrimeDivisor : (n : Nat⁺) -> isFinSet (PrimeDivisor n)
  isFinSet-PrimeDivisor n = isFinSet-equiv (PrimeDivisor'-eq n) (isFinSet-PrimeDivisor' n)

FinSet-PrimeDivisor : Nat⁺ -> FinSet ℓ-zero
FinSet-PrimeDivisor n = PrimeDivisor n , isFinSet-PrimeDivisor n

abstract
  Discrete-PrimeDivisor : (n : Nat⁺) -> Discrete (PrimeDivisor n)
  Discrete-PrimeDivisor n pd1@((p1 , isP1) , d1) pd2@((p2 , isP2) , d2) =
    handle (decide-nat p1 p2)
    where
    handle : Dec (p1 == p2) -> Dec (pd1 == pd2)
    handle (yes path) = yes (ΣProp-path (isPropDiv' n) (ΣProp-path isPropIsPrime' path))
    handle (no ¬path) = no (\path -> ¬path (cong fst (cong fst path)))



module _ (a b : Nat⁺) where
  private
    a' = ⟨ a ⟩
    b' = ⟨ b ⟩
  module _ (rp : RelativelyPrime⁺ a b) where
    private
      inner-eq : (p : Prime') -> (⟨ p ⟩ div' (a' *' b')) ≃ (⟨ p ⟩ div' a' ⊎ ⟨ p ⟩ div' b')
      inner-eq p = isoToEquiv i
        where
        open Iso
        i : Iso (⟨ p ⟩ div' (a' *' b')) (⟨ p ⟩ div' a' ⊎ ⟨ p ⟩ div' b')
        i .fun = prime-divides-a-factor p
        i .inv (inj-l p%a) = div'-mult' p%a b'
        i .inv (inj-r p%b) = div'-mult p%b a'
        i .leftInv _ = isPropDiv' (a *⁺ b) _ _
        i .rightInv p%a⊎b = handle (i .fun (i .inv p%a⊎b)) p%a⊎b
          where
          handle : (x y : (⟨ p ⟩ div' a' ⊎ ⟨ p ⟩ div' b')) -> x == y
          handle (inj-l x) (inj-l y) = cong inj-l (isPropDiv' a _ _)
          handle (inj-l x) (inj-r y) = bot-elim (Prime'.!=1 p (rp _ x y))
          handle (inj-r x) (inj-l y) = bot-elim (Prime'.!=1 p (rp _ y x))
          handle (inj-r x) (inj-r y) = cong inj-r (isPropDiv' b _ _)

    PrimeDivisor-*-eq : PrimeDivisor (a *⁺ b) ≃ (PrimeDivisor a ⊎ PrimeDivisor b)
    PrimeDivisor-*-eq = existential-eq inner-eq >eq> Σ-distrib-⊎

PrimeDivisor-1-eq : PrimeDivisor 1⁺ ≃ Bot
PrimeDivisor-1-eq = isoToEquiv i
  where
  open Iso
  i : Iso (PrimeDivisor 1⁺) Bot
  i .fun (p , p%1) = Prime'.¬%1 p p%1
  i .inv b = bot-elim b
  i .rightInv b = bot-elim b
  i .leftInv (p , p%1) = bot-elim (Prime'.¬%1 p p%1)

private
  prime-power-prime-divisor : (p1 p2 : Prime') (n : Nat) -> (⟨ p1 ⟩ div' (prime-power p2 n)) ->
                              p1 == p2
  prime-power-prime-divisor p1 p2 zero p1%p2n = bot-elim (Prime'.¬%1 p1 p1%p2n)
  prime-power-prime-divisor p1 p2 (suc n) p1%p2n = handle (prime-divides-a-factor p1 p1%p2n)
    where
    p1' = ⟨ p1 ⟩
    p2' = ⟨ p2 ⟩
    handle : (p1' div' p2') ⊎ p1' div' (prime-power p2 n) -> p1 == p2
    handle (inj-l path) = prime-self-divisor p1 p2 path
    handle (inj-r p1%p2n) = prime-power-prime-divisor p1 p2 n p1%p2n

PrimeDivisor-prime-power-eq : (p : Prime') (n : Nat⁺) -> PrimeDivisor (prime-power⁺ p ⟨ n ⟩) ≃ Top
PrimeDivisor-prime-power-eq p n⁺@(n , _) = isoToEquiv i
  where
  open Iso
  i : Iso (PrimeDivisor (prime-power⁺ p n)) Top
  i .fun _ = tt
  i .inv _ = p , prime-power-div p n⁺
  i .rightInv _ = refl
  i .leftInv d@(p2 , p2%pn) =
    ΣProp-path (isPropDiv' (prime-power⁺ p n)) (sym (prime-power-prime-divisor p2 p n p2%pn))

isContr-PrimeDivisor-prime-power :
  (p : Prime') (n : Nat⁺) -> isContr (PrimeDivisor (prime-power⁺ p ⟨ n ⟩))
isContr-PrimeDivisor-prime-power p n⁺@(n , _) =
  (p , prime-power-div p n⁺) ,
  \ (p2 , p2%pn) ->
    ΣProp-path (isPropDiv' (prime-power⁺ p n)) (sym (prime-power-prime-divisor p2 p n p2%pn))

isContr-PrimeDivisor->prime-power :
  (n : Nat⁺) -> (c : isContr (PrimeDivisor n)) -> Σ[ i ∈ ℕ ] (prime-power ⟨ ⟨ c ⟩ ⟩ i == ⟨ n ⟩)
isContr-PrimeDivisor->prime-power (zero , ())
isContr-PrimeDivisor->prime-power (suc zero , _) _ = 0 , refl
isContr-PrimeDivisor->prime-power n@(suc (suc _) , _) (pd@(p , _) , pd-unique) =
  handle-tree pft div'-refl
  where
  pft : PrimeFactorizationTree ⟨ n ⟩
  pft = compute-prime-factorization-tree (suc-≤ (suc-≤ zero-≤))

  handle-tree : {m : ℕ} -> PrimeFactorizationTree m -> m div' ⟨ n ⟩ ->
                Σ[ i ∈ ℕ ] (prime-power p i == m)
  handle-tree (prime-factorization-tree-prime p2) p2∣n =
    1 , *-right-one >=> cong fst p=p2
    where
    p=p2 : p == p2
    p=p2 = cong fst (pd-unique (p2 , p2∣n))
  handle-tree (prime-factorization-tree-composite {m1} {m2} t1 t2) (x , xm1m2=n) =
    fst rec1 + fst rec2 ,
    ^ℕ-distrib-+-left (fst rec1) (fst rec2) >=>
    *-cong (snd rec1) (snd rec2)
    where
    rec1 : Σ[ i ∈ ℕ ] (prime-power p i == m1)
    rec1 = handle-tree t1 (x * m2 , *-assocᵉ x m2 m1 >=>
                                    cong (x *_) (*-commuteᵉ m2 m1) >=> xm1m2=n)
    rec2 : Σ[ i ∈ ℕ ] (prime-power p i == m2)
    rec2 = handle-tree t2 (x * m1 , *-assocᵉ x m1 m2 >=> xm1m2=n)


isProp-PrimeDivCount : {p : Prime'} {a : Nat} {n : Nat} -> isProp (PrimeDivCount p a n)
isProp-PrimeDivCount {p} {a} {n} dc1 dc2 = (\i -> record
  { %a = %a-path i
  ; upper-bound = upper-bound-path i
  })
  where
  p' = ⟨ p ⟩
  %a-path : (PrimeDivCount.%a dc1) == (PrimeDivCount.%a dc2)
  %a-path = isPropDiv' (a , (PrimeDivCount.a-pos dc1)) _ _

  upper-bound-path : Path _ (PrimeDivCount.upper-bound dc1) (PrimeDivCount.upper-bound dc2)
  upper-bound-path = isPropΠ2 (\_ _ -> isProp-≤) _ _


PrimePowerFactor : Nat -> Type₀
PrimePowerFactor n = Σ[ pe ∈ (Prime' × Nat⁺) ] (PrimeDivCount (proj₁ pe) n (fst (proj₂ pe)))


PrimePowerFactor-1-eq : PrimePowerFactor 1 ≃ Bot
PrimePowerFactor-1-eq = isoToEquiv i
  where
  open Iso
  i : Iso (PrimePowerFactor 1) Bot
  i .fun ((p , n) , dc) = bot-elim (Prime'.¬%1 p (div'-trans (prime-power-div p n) (PrimeDivCount.%a dc)))
  i .inv b = bot-elim b
  i .rightInv b = bot-elim b
  i .leftInv ((p , n) , dc) =
    bot-elim (Prime'.¬%1 p (div'-trans (prime-power-div p n) (PrimeDivCount.%a dc)))



PrimePowerFactor-prime-power-eq : (p : Prime') (n : Nat⁺) -> PrimePowerFactor (prime-power p ⟨ n ⟩) ≃ Top
PrimePowerFactor-prime-power-eq p n⁺@(n , _) = isoToEquiv i
  where
  open Iso
  i : Iso (PrimePowerFactor (prime-power p n)) Top
  i .fun _ = tt
  i .inv _ = (p , n⁺) , prime-power-div-count p n
  i .rightInv _ = refl
  i .leftInv ((p2 , n2) , dc2) = ΣProp-path isProp-PrimeDivCount (cong2 _,_ p-path n-path)
    where
    dc : PrimeDivCount p (prime-power p n) n
    dc = prime-power-div-count p n

    p-path : p == p2
    p-path = sym (prime-power-prime-divisor p2 p n
                   (div'-trans (prime-power-div p2 n2) (PrimeDivCount.%a dc2)))
    n-path : n⁺ == n2
    n-path = ΣProp-path isPropPos'
               (prime-div-count-unique
                 (transport (\i -> PrimeDivCount (p-path i) (prime-power p n) n) dc) dc2)


module _ (a b : Nat) where
  module _ (rp : RelativelyPrime⁰ a b) where
    private
      inner-eq : (pe : (Prime' × Nat⁺)) ->
                 (PrimeDivCount (proj₁ pe) (a *' b) (fst (proj₂ pe))) ≃
                 ((PrimeDivCount (proj₁ pe) a (fst (proj₂ pe))) ⊎
                  (PrimeDivCount (proj₁ pe) b (fst (proj₂ pe))))
      inner-eq (p@(p' , _) , e⁺@(e , _)) = isoToEquiv i
        where

        forward : (PrimeDivCount p (a *' b) e) -> ((PrimeDivCount p a e) ⊎ (PrimeDivCount p b e))
        forward dc = handle (prime-divides-a-factor p p%ab)
          where
          ab-pos : Pos' (a *' b)
          ab-pos = PrimeDivCount.a-pos dc
          p%ab : p' div' (a *' b)
          p%ab = (div'-trans (prime-power-div p e⁺) (PrimeDivCount.%a dc))
          handle : (p' div' a) ⊎ (p' div' b) -> ((PrimeDivCount p a e) ⊎ (PrimeDivCount p b e))
          handle (inj-l p%a) = inj-l (transport (\i -> PrimeDivCount p a (path i)) (snd dc-a))
            where
            ¬p%b : ¬ (p' div' b)
            ¬p%b p%b = Prime'.!=1 p (rp _ p%a p%b)

            a⁺ : Nat⁺
            a⁺ = a , *'-Pos-left ab-pos

            dc-a : Σ Nat (PrimeDivCount p a)
            dc-a = compute-prime-div-count p a⁺

            dc-b : PrimeDivCount p b 0
            dc-b = ¬div-prime-div-count ¬p%b

            path : fst dc-a == e
            path = sym (+'-right-zero) >=>
                   prime-div-count-unique (*'-prime-div-count (snd dc-a) dc-b) dc


          handle (inj-r p%b) = inj-r (transport (\i -> PrimeDivCount p b (path i)) (snd dc-b))
            where
            ¬p%a : ¬ (p' div' a)
            ¬p%a p%a = Prime'.!=1 p (rp _ p%a p%b)

            b⁺ : Nat⁺
            b⁺ = b , *'-Pos-right {a} ab-pos

            dc-b : Σ Nat (PrimeDivCount p b)
            dc-b = compute-prime-div-count p b⁺

            dc-a : PrimeDivCount p a 0
            dc-a = ¬div-prime-div-count ¬p%a

            path : fst dc-b == e
            path = prime-div-count-unique (*'-prime-div-count dc-a (snd dc-b)) dc



        backward : ((PrimeDivCount p a e) ⊎ (PrimeDivCount p b e)) -> (PrimeDivCount p (a *' b) e)
        backward (inj-l dc) =
          transport (\i -> PrimeDivCount p (a *' b) (+'-right-zero {e} i))
                    (*'-prime-div-count dc (¬div-prime-div-count ¬p%b))
          where
          p%a : p' div' a
          p%a = (div'-trans (prime-power-div p e⁺) (PrimeDivCount.%a dc))

          ¬p%b : ¬ (p' div' b)
          ¬p%b p%b = Prime'.!=1 p (rp _ p%a p%b)

        backward (inj-r dc) = (*'-prime-div-count (¬div-prime-div-count ¬p%a) dc)
          where
          p%b : p' div' b
          p%b = (div'-trans (prime-power-div p e⁺) (PrimeDivCount.%a dc))

          ¬p%a : ¬ (p' div' a)
          ¬p%a p%a = Prime'.!=1 p (rp _ p%a p%b)

        open Iso
        i : Iso (PrimeDivCount p (a *' b) e)
                ((PrimeDivCount p a e) ⊎ (PrimeDivCount p b e))
        i .fun = forward
        i .inv = backward
        i .leftInv _ = isProp-PrimeDivCount _ _
        i .rightInv dc = handle (forward (backward dc)) dc
          where
          handle : (x y : ((PrimeDivCount p a e) ⊎ (PrimeDivCount p b e))) -> x == y
          handle (inj-l x) (inj-l y) = cong inj-l (isProp-PrimeDivCount _ _)
          handle (inj-l x) (inj-r y) =
            bot-elim (Prime'.!=1 p (rp _ (div'-trans (prime-power-div p e⁺) (PrimeDivCount.%a x))
                                         (div'-trans (prime-power-div p e⁺) (PrimeDivCount.%a y))))
          handle (inj-r x) (inj-l y) =
            bot-elim (Prime'.!=1 p (rp _ (div'-trans (prime-power-div p e⁺) (PrimeDivCount.%a y))
                                         (div'-trans (prime-power-div p e⁺) (PrimeDivCount.%a x))))
          handle (inj-r x) (inj-r y) = cong inj-r (isProp-PrimeDivCount _ _)


    PrimePowerFactor-*-eq : PrimePowerFactor (a *' b) ≃ (PrimePowerFactor a ⊎ PrimePowerFactor b)
    PrimePowerFactor-*-eq = existential-eq inner-eq >eq> Σ-distrib-⊎

PrimePowerFactor-0-eq : (PrimePowerFactor 0) ≃ Bot
PrimePowerFactor-0-eq = isoToEquiv i
  where
  open Iso
  i : Iso (PrimePowerFactor 0) Bot
  i .fun ((p , n) , dc) = PrimeDivCount.a-pos dc
  i .inv b = bot-elim b
  i .rightInv b = bot-elim b
  i .leftInv ((p , n) , dc) = bot-elim (PrimeDivCount.a-pos dc)



PrimeDivisor-PrimePowerFactor-eq : (n : Nat⁺) -> (PrimeDivisor n) ≃ (PrimePowerFactor ⟨ n ⟩)
PrimeDivisor-PrimePowerFactor-eq n@(n' , _)= isoToEquiv i
  where

  open Iso
  i : Iso (PrimeDivisor n) (PrimePowerFactor n')
  i .fun (p , p%n) = ((p , (fst Σdc , handle (fst Σdc) refl)) , dc)
    where

    Σdc : Σ Nat (PrimeDivCount p n')
    Σdc = compute-prime-div-count p n
    e = fst Σdc
    dc = snd Σdc

    handle : (e' : Nat) -> (e' == e) -> Pos' e
    handle (suc _) path = subst Pos' path tt
    handle zero path = subst Pos' path (PrimeDivCount.¬p%r dc p%r)
      where
      r = PrimeDivCount.r dc
      r-path : r == n'
      r-path = (sym *'-right-one) >=> cong (r *'_) (cong (prime-power p) path)
               >=> PrimeDivCount.r-path dc
      p%r : (fst p) div' r
      p%r = fst p%n , snd p%n >=> (sym r-path)



  i .inv ((p , e) , dc) = (p , (div'-trans (prime-power-div p e) (PrimeDivCount.%a dc)))
  i .leftInv (p , p%n) = ΣProp-path (isPropDiv' n) refl

  i .rightInv ((p , e2) , dc2) = ΣProp-path isProp-PrimeDivCount (cong2 _,_ p-path e-path)
    where
    e = prime-div-count p n
    dc = prime-div-count-proof p n

    p-path : p == p
    p-path = refl

    e-path : {e-pos : Pos' e} -> (e , e-pos) == e2
    e-path =
      ΣProp-path isPropPos'
                 (prime-div-count-unique
                   (transport (\i -> PrimeDivCount (p-path i) n' e) dc) dc2)



isFinSet-PrimePowerFactor : (n : Nat) -> isFinSet (PrimePowerFactor n)
isFinSet-PrimePowerFactor zero =
  isFinSet-equiv (equiv⁻¹ PrimePowerFactor-0-eq) (snd FinSet-Bot)
isFinSet-PrimePowerFactor n@(suc _) =
  isFinSet-equiv (PrimeDivisor-PrimePowerFactor-eq (n , tt)) (isFinSet-PrimeDivisor (n , tt))

module _ {D : Type ℓ} {ACM : AdditiveCommMonoid D} {{S : Semiring ACM}} where
  private
    instance
      M : Multiplication D
      M = SemiringMultiplication S

  module _ {f : Nat⁺ -> D} (m : Multiplicative f) where
    private
      f' : {n : Nat} -> PrimePowerFactor n -> D
      f' ((p , (e , _)) , _) = f (prime-power⁺ p e)


      FinSet-PrimePowerFactor : Nat -> FinSet ℓ-zero
      FinSet-PrimePowerFactor n = PrimePowerFactor n , isFinSet-PrimePowerFactor n


      factorization-case : {n : Nat⁺} -> PrimePowerFactorization ⟨ n ⟩ ->
                           finiteProduct (FinSet-PrimePowerFactor ⟨ n ⟩) f' == f n
      factorization-case {n} (ppf-base p e) =
        finiteProduct-convert (FinSet-PrimePowerFactor ⟨ n ⟩) FinSet-Top
                              (equiv⁻¹ (PrimePowerFactor-prime-power-eq p e)) _
        >=> finiteProduct-Top _
        >=> cong f (ΣProp-path isPropPos' refl)
      factorization-case (ppf-combine {a} {b} fa fb rp) =
        finiteProduct-convert (FinSet-PrimePowerFactor (a *' b))
                              (FinSet-⊎ (FinSet-PrimePowerFactor a) (FinSet-PrimePowerFactor b))
                              (equiv⁻¹ (PrimePowerFactor-*-eq a b rp)) _
        >=> finiteProduct-⊎ (FinSet-PrimePowerFactor a) (FinSet-PrimePowerFactor b) _
        >=> cong2 _*_ (factorization-case {a⁺} fa) (factorization-case {b⁺} fb)
        >=> sym (m .snd _ _ rp)
        >=> cong f (ΣProp-path isPropPos' refl)
        where
        a⁺ : Nat⁺
        a⁺ = _ , ppf->pos fa
        b⁺ : Nat⁺
        b⁺ = _ , ppf->pos fb


    Multiplicative-PrimePowerFactor :
      {n : Nat⁺} -> f n == finiteProduct (FinSet-PrimePowerFactor ⟨ n ⟩) f'
    Multiplicative-PrimePowerFactor {n = (suc zero) , _} =
      m .fst
      >=> sym (finiteProduct-Bot _)
      >=> sym (finiteProduct-convert (FinSet-PrimePowerFactor 1) (FinSet-Bot)
                                     (equiv⁻¹ (PrimePowerFactor-1-eq)) f')
    Multiplicative-PrimePowerFactor {n = (suc (suc _)) , _} =
      sym (factorization-case (compute-ppf (suc-≤ (suc-≤ zero-≤))))

    Multiplicative-PrimeDivisor :
      {n : Nat⁺} -> f n == finiteProduct (FinSet-PrimeDivisor n)
                            (\(p , _) -> (f (prime-power⁺ p (prime-div-count p n))))
    Multiplicative-PrimeDivisor =
      Multiplicative-PrimePowerFactor >=>
      finiteProduct-convert (FinSet-PrimePowerFactor _) (FinSet-PrimeDivisor _)
                            (PrimeDivisor-PrimePowerFactor-eq _) _
