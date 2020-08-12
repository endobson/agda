{-# OPTIONS --cubical --safe --exact-split #-}

module prime-power-factorization where

open import base
open import div
open import equality
open import functions
open import nat
open import prime
open import prime-gcd
open import prime-factorization
open import relation

private
  RP = RelativelyPrime'

data PrimePowerFactorization : Nat -> Type₀ where
  ppf-base : (p : Prime') -> (n : Nat⁺) -> PrimePowerFactorization (prime-power p ⟨ n ⟩)
  ppf-combine : {a b : Nat}
    -> PrimePowerFactorization a
    -> PrimePowerFactorization b
    -> RP a b
    -> PrimePowerFactorization (a *' b)

private
  PPF = PrimePowerFactorization

  prime->ppf : (p : Prime') -> PPF ⟨ p ⟩
  prime->ppf p@(p' , _) = transport (cong PPF ^'-right-one) (ppf-base p 1⁺)

  ppf-prime-merge : {n : Nat} (p : Prime')  -> PPF n -> PPF (⟨ p ⟩ *' n)
  ppf-prime-merge {m} p@(p' , _) ppf@(ppf-base p2@(p2' , _) (n , _)) =
    handle (decide-nat p' p2')
    where
    handle : Dec (p' == p2') -> PPF (p' *' m)
    handle (yes path) = transport (\i -> PPF (path (~ i) *' m))
                                  (ppf-base p2 ((suc n) , _))
    handle (no ¬path) =
      ppf-combine (prime->ppf p) ppf rp
      where
      distinct : p != p2
      distinct = ¬path ∘ (cong fst)

      rp : RP p' (prime-power p2 n)
      rp = relatively-prime-^' (distinct-primes->relatively-prime distinct) n
  ppf-prime-merge p@(p' , _) (ppf-combine {a} {b} t1 t2 rp) =
    handle (decide-div p' a) (decide-div p' b)
    where
    handle : Dec (p' div' a) -> Dec (p' div' b) -> PPF (p' *' (a *' b))
    handle (no ¬p%a) _ = transport (cong PPF path) ppf
      where
      rp-p-a : RP p' a
      rp-p-a = prime->relatively-prime p ¬p%a
      rp-a-pb : RP a (p' *' b)
      rp-a-pb = (relatively-prime-*' (rp-sym rp-p-a) rp)
      ppf : PPF (a *' (p' *' b))
      ppf = ppf-combine t1 (ppf-prime-merge p t2) rp-a-pb
      path : (a *' (p' *' b)) == (p' *' (a *' b))
      path = sym (*'-assoc {a} {p'}) >=> *'-left (*'-commute {a} {p'}) >=> *'-assoc {p'} {a}
    handle (yes _) (no ¬p%b) = transport (cong PPF path) ppf
      where
      rp-p-b : RP p' b
      rp-p-b = prime->relatively-prime p ¬p%b
      rp-pa-b : RP (p' *' a) b
      rp-pa-b = rp-sym (relatively-prime-*' (rp-sym rp-p-b) (rp-sym rp))
      ppf : PPF ((p' *' a) *' b)
      ppf = ppf-combine (ppf-prime-merge p t1) t2 rp-pa-b
      path : (p' *' a) *' b == p' *' (a *' b)
      path = *'-assoc {p'} {a}
    handle (yes p%a) (yes p%b) = bot-elim (Prime'.!=1 p (rp p' p%a p%b))

  ppf-pp-merge :
    {m : Nat} -> (p : Prime') -> (n : Nat) -> PPF m -> PPF (prime-power p n *' m)
  ppf-pp-merge p zero    t = transport (cong PPF (sym *'-left-one)) t
  ppf-pp-merge p (suc n) t = transport (cong PPF (sym (*'-assoc {⟨ p ⟩})))
                                       (ppf-prime-merge p (ppf-pp-merge p n t))

  ppf-tree-merge : {a b : Nat} -> PPF a -> PPF b -> PPF (a *' b)
  ppf-tree-merge (ppf-base p n) t = ppf-pp-merge p ⟨ n ⟩ t
  ppf-tree-merge (ppf-combine {a} {b} t1 t2 _) t3 =
   transport (cong PPF (sym (*'-assoc {a} {b})))
             (ppf-tree-merge t1 (ppf-tree-merge t2 t3))

  pft->ppf : {n : Nat} -> PrimeFactorizationTree n -> PPF n
  pft->ppf (prime-factorization-tree-prime p) = prime->ppf p
  pft->ppf (prime-factorization-tree-composite t1 t2) =
    ppf-tree-merge (pft->ppf t1) (pft->ppf t2)

compute-ppf : {n : Nat} -> n > 1 -> PPF n
compute-ppf n>1 = pft->ppf (compute-prime-factorization-tree n>1)
