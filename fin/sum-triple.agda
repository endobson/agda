{-# OPTIONS --cubical --safe --exact-split #-}

module fin.sum-triple where

open import additive-group
open import additive-group.instances.nat
open import base
open import cubical
open import equality
open import fin.sum-pair
open import hlevel
open import isomorphism
open import nat

record FinTriple+ (n : Nat) : Type₀ where
  constructor fin-triple+
  field
    i : Nat
    j : Nat
    k : Nat
    ijk=n : i + (j + k) == n


module _ {n : Nat} where
  FinTriple+-split₁ : Iso (FinTriple+ n) (Σ[ (fin-pair+ i jk _) ∈ FinPair+ n ] (FinPair+ jk))
  FinTriple+-split₁ .Iso.fun (fin-triple+ i j k p) =
    (fin-pair+ i (j + k) p , fin-pair+ j k refl)
  FinTriple+-split₁ .Iso.inv (fin-pair+ i jk p₁ , fin-pair+ j k p₂) =
    fin-triple+ i j k (cong (i +_) p₂ >=> p₁)
  FinTriple+-split₁ .Iso.rightInv (fin-pair+ i jk p₁ , fin-pair+ j k p₂) =
    path3
    where
    path1 : PathP (\ii -> FinPair+ (p₂ ii)) (fin-pair+ j k refl) (fin-pair+ j k p₂)
    path1 ii = fin-pair+ j k (\jj -> p₂ (ii ∧ jj))

    path2 : PathP (\ii -> i + p₂ ii == n) (cong (i +_) p₂ >=> p₁) p₁
    path2 = isProp->PathP (\_ -> isSetNat _ _)

    path3 : Path (Σ[ (fin-pair+ i jk _) ∈ FinPair+ n ] (FinPair+ jk)) _ _
    path3 ii = fin-pair+ i (p₂ ii) (path2 ii) , path1 ii
  FinTriple+-split₁ .Iso.leftInv (fin-triple+ i j k p) ii =
    fin-triple+ i j k (isProp->PathPᵉ (\_ -> isSetNat _ _) (cong (i +_) refl >=> p) p ii)


  FinTriple+-split₂ : Iso (FinTriple+ n) (Σ[ (fin-pair+ ij k _) ∈ FinPair+ n ] (FinPair+ ij))
  FinTriple+-split₂ .Iso.fun (fin-triple+ i j k p) =
    (fin-pair+ (i + j) k (+-assocᵉ i j k >=> p) , fin-pair+ i j refl)
  FinTriple+-split₂ .Iso.inv (fin-pair+ ij k p₁ , fin-pair+ i j p₂) =
    fin-triple+ i j k (sym (+-assocᵉ i j k) >=> cong (_+ k) p₂ >=> p₁)
  FinTriple+-split₂ .Iso.rightInv (fin-pair+ ij k p₁ , fin-pair+ i j p₂) =
    path3
    where
    path1 : PathP (\ii -> FinPair+ (p₂ ii)) (fin-pair+ i j refl) (fin-pair+ i j p₂)
    path1 ii = fin-pair+ i j (\jj -> p₂ (ii ∧ jj))

    path2 : PathP (\ii -> p₂ ii + k == n)
                  (+-assocᵉ i j k >=> (sym (+-assocᵉ i j k) >=> cong (_+ k) p₂ >=> p₁))
                  p₁
    path2 = isProp->PathP (\_ -> isSetNat _ _)

    path3 : Path (Σ[ (fin-pair+ ij k _) ∈ FinPair+ n ] (FinPair+ ij)) _ _
    path3 ii = fin-pair+ (p₂ ii) k (path2 ii) , path1 ii
  FinTriple+-split₂ .Iso.leftInv (fin-triple+ i j k p) ii =
    fin-triple+ i j k (isProp->PathPᵉ (\_ -> isSetNat _ _)
                        (sym (+-assocᵉ i j k) >=> cong (_+ k) refl >=> (+-assocᵉ i j k >=> p)) p ii)
