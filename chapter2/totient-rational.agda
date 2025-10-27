{-# OPTIONS --cubical --safe --exact-split #-}

module chapter2.totient-rational where

open import additive-group
open import additive-group.instances.int
open import additive-group.instances.nat
open import base
open import chapter2.id-function
open import chapter2.multiplicative
open import chapter2.prime-divisors
open import chapter2.totient
open import commutative-monoid
open import equality
open import finite-product
open import finset
open import funext
open import int
open import int.add1
open import nat
open import nat.order
open import order
open import order.instances.nat
open import prime
open import prime-div-count.computational
open import rational
open import rational-prime
open import ring
open import ring.exponentiation
open import ring.implementations.int
open import ring.implementations.rational
open import semiring
open import semiring.instances.nat

private
  module Ring-ℚ = Ring Ring-ℚ

φℚ : Nat⁺ -> ℚ
φℚ n = ℕ->ℚ (φ n)

φℚ-one : φℚ 1⁺ == 1r
φℚ-one = cong ℕ->ℚ φ-one

module _ (p : Prime') where
  private
    p' = ⟨ p ⟩
    p⁺ = Prime'.nat⁺ p
  φℚ-prime : (φℚ p⁺) == ℕ->ℚ (pred p')
  φℚ-prime = cong ℕ->ℚ (φ-prime p)


  module _ (n : Nat⁺) where
    private
      n' = ⟨ n ⟩

      pred-n< : pred n' < n'
      pred-n< = same-pred-< n

      p^pn<p^n : (prime-power p (pred n')) < (prime-power p n')
      p^pn<p^n = handle n
        where
        handle : (n : Nat⁺) -> (prime-power p (pred ⟨ n ⟩)) < (prime-power p ⟨ n ⟩)
        handle (suc n , _) = ^-suc-< (Prime'.>1 p) n

      pred->sub1 : (int (pred n')) == (sub1 (int n'))
      pred->sub1 = handle n
        where
        handle : (n : Nat⁺) -> (int (pred ⟨ n ⟩)) == (sub1 (int ⟨ n ⟩))
        handle (suc n , _) = refl

    φℚ-prime-power : φℚ (prime-power⁺ p n') ==
                     (prime-powerℚ p (int n')) r* (1r r+ (r- (fst (Ring-ℚ.u1/ (ℚUnit-prime p)))))
    φℚ-prime-power =
      cong ℕ->ℚ (φ-prime-power p n) >=>
      cong ℤ->ℚ (ℕ->ℤ-minus p^pn<p^n) >=>
      Ringʰ.preserves-+ Ringʰ-ℤ->ℚ _ _ >=>
      (cong (_r+ ℤ->ℚ (- (ℕ->ℤ (prime-power p (pred n')))))
            (ℕ->ℚ-prime-power p n' >=>
             (sym (r*-left-one (prime-powerℚ p (int n')))))) >=>
      (cong ((1r r* (prime-powerℚ p (int n'))) r+_)
            (Ringʰ.preserves-minus Ringʰ-ℤ->ℚ _ >=>
             cong r-_ (ℕ->ℚ-prime-power p (pred n') >=>
                       cong (prime-powerℚ p) pred->sub1 >=>
                       cong fst (u^ℤ-sub1 (ℚUnit-prime p) (int n'))) >=>
             sym (r*-minus-extract-left
                   (fst (Ring-ℚ.u1/ (ℚUnit-prime p)))
                   (prime-powerℚ p (int n'))))) >=>
      sym (r*-distrib-r+-right 1r (r- (fst (Ring-ℚ.u1/ (ℚUnit-prime p))))
                               (prime-powerℚ p (int n'))) >=>
      r*-commute (1r r+ (r- (fst (Ring-ℚ.u1/ (ℚUnit-prime p))))) (prime-powerℚ p (int n'))






Multiplicative-φℚ : Multiplicative φℚ
Multiplicative-φℚ .fst = cong ℕ->ℚ (Multiplicative-φ .fst)
Multiplicative-φℚ .snd a b rp =
  cong ℕ->ℚ (Multiplicative-φ .snd a b rp) >=>
  Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ _ _

module _ where
  private
    assum1' : {ℓ : Level} (FA : FinSet ℓ) -> {f : ⟨ FA ⟩ -> ℕ} ->
              finiteProduct FA (\a -> (ℕ->ℚ (f a))) == ℕ->ℚ (finiteProduct FA f)
    assum1' FA = finiteProduct-homo-inject FA CM
      where
      CM : CommMonoidʰᵉ _ _ ℕ->ℚ
      CM = record
        { monoidʰ = record
          { preserves-ε = (Semiringʰ.preserves-1# Semiringʰ-ℕ->ℚ)
          ; preserves-∙ = (Semiringʰ.preserves-* Semiringʰ-ℕ->ℚ)
          }
        }

    φℚ-finiteProduct-step2 : {n : Nat⁺} ->
      (finiteProduct (FinSet-PrimeDivisor n) (\(p , _) -> (prime-powerℚ p (int (prime-div-count p n)))))
      == (ℕ->ℚ ⟨ n ⟩)
    φℚ-finiteProduct-step2 {n} =
      cong (\f -> finiteProduct (FinSet-PrimeDivisor n) f)
           (funExt (\(p , d) -> (sym (ℕ->ℚ-prime-power p (prime-div-count p n)))))
      >=> assum1' (FinSet-PrimeDivisor n)
      >=> cong ℕ->ℚ (sym (finiteProduct-PrimeDivisor-N⁰ n))



  φℚ-finiteProduct : {n : Nat⁺} ->
    φℚ n == (ℕ->ℚ ⟨ n ⟩) r* (finiteProduct (FinSet-PrimeDivisor n)
                              (\(p , _) -> (1r r+ (r- (fst (Ring-ℚ.u1/ (ℚUnit-prime p)))))))
  φℚ-finiteProduct {n} =
    Multiplicative-PrimeDivisor {f = φℚ} Multiplicative-φℚ {n} >=>
    cong (\f -> finiteProduct (FinSet-PrimeDivisor n) f)
         (funExt (\(p , d) -> φℚ-prime-power p (prime-div-count p n ,
                                                <->Pos' (prime-div->prime-div-count p n d)))) >=>
    finiteProduct-split (FinSet-PrimeDivisor n) >=>
    cong (_r* (finiteProduct (FinSet-PrimeDivisor n)
                (\(p , _) -> (1r r+ (r- (fst (Ring-ℚ.u1/ (ℚUnit-prime p))))))))
         (φℚ-finiteProduct-step2 {n})
