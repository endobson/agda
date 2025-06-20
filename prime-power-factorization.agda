{-# OPTIONS --cubical --safe --exact-split #-}

module prime-power-factorization where

open import base
open import equality
open import functions
open import nat
open import nat.order
open import order
open import order.instances.nat
open import prime
open import prime-factorization
open import prime-gcd
open import relation
open import relatively-prime
open import nat.division
open import semiring.exponentiation
open import semiring.instances.nat
open import semiring.division
open import sigma.base

private
  RP = RelativelyPrime⁰

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
  prime->ppf p@(p' , _) = transport (cong PPF ^ℕ-one) (ppf-base p 1⁺)

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
      rp = relatively-prime-^ℕ (distinct-primes->relatively-prime distinct) n
  ppf-prime-merge p@(p' , _) (ppf-combine {a} {b} t1 t2 rp) =
    handle (decide-div p' a) (decide-div p' b)
    where
    handle : Dec (p' div a) -> Dec (p' div b) -> PPF (p' *' (a *' b))
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

ppf->pos : {a : Nat} -> PPF a -> Pos' a
ppf->pos (ppf-base p n) = (snd (prime-power⁺ p ⟨ n ⟩))
ppf->pos (ppf-combine ppf-a ppf-b _) = *'-Pos'-Pos' (ppf->pos ppf-a) (ppf->pos ppf-b)


abstract
  PPFElim : {ℓP : Level} (P : Nat⁺ -> Type ℓP) ->
            (∀ p n -> P (prime-power⁺ p n)) ->
            ((a b : Nat⁺) -> (RelativelyPrime⁺ a b) -> P a -> P b -> P (a *⁺ b)) ->
            (a : Nat⁺) -> P a
  PPFElim P P-prime P-coprime (zero , ())
  PPFElim P P-prime P-coprime (suc zero , _) = (P-prime (2 , 2-is-prime) 0)
  PPFElim P P-prime P-coprime (suc (suc n) , _) = handle (compute-ppf (suc-≤ (suc-≤ zero-≤)))
    where
    handle : ∀ {n} -> PrimePowerFactorization ⟨ n ⟩ -> P n
    handle (ppf-base p n) = subst P (ΣProp-path isPropPos' refl) (P-prime p ⟨ n ⟩)
    handle (ppf-combine fa fb coprime) =
     subst P (ΣProp-path isPropPos' refl)
      (P-coprime (_ , ppf->pos fa) (_ , ppf->pos fb) coprime (handle fa) (handle fb))




data OrderedPrimePowerFactorization : Nat -> Type₀ where
  oppf-[] : OrderedPrimePowerFactorization 1
  oppf-cons : {a : Nat}
    -> (p : Prime')
    -> (n : Nat⁺)
    -> (¬ (⟨ p ⟩ div a))
    -> OrderedPrimePowerFactorization a
    -> OrderedPrimePowerFactorization ((prime-power p ⟨ n ⟩) *' a)

private
  OPPF = OrderedPrimePowerFactorization

  merge-ppf-oppf : {a b : Nat} -> PPF a -> RP a b -> OPPF b -> OPPF (a *' b)
  merge-ppf-oppf {a} {b} (ppf-base p n@(suc n' , _)) rp oppf = oppf-cons p n ¬p%b oppf
    where
    ¬p%b : ¬ (⟨ p ⟩ div  b)
    ¬p%b p%b = Prime'.!=1 p (rp ⟨ p ⟩ (prime-power-div p n) p%b)
  merge-ppf-oppf {a} {b} (ppf-combine {a1} {a2} ta1 ta2 rp-as) rp-ab oppf =
    transport (cong OPPF index-path) (merge-ppf-oppf ta1 rp-a1-a2b (merge-ppf-oppf ta2 rp-a2-b oppf))
    where
    index-path : a1 *' (a2 *' b) == a *' b
    index-path = sym (*'-assoc {a1} {a2} {b})

    rp-a1-a2b : RP a1 (a2 *' b)
    rp-a1-a2b = no-shared-primes a1 (a2 *' b) f
      where
      f : (p : Prime') -> ⟨ p ⟩ div a1 -> ⟨ p ⟩ div (a2 *' b) -> Bot
      f p@(p' , _) p%a1 p%a2b = handle (prime-divides-a-factor p p%a2b)
        where
        handle : (p' div a2 ⊎ p' div b) -> Bot
        handle (inj-l p%a2) = Prime'.!=1 p (rp-as p' p%a1 p%a2)
        handle (inj-r p%b) = Prime'.!=1 p (rp-ab p' (div-*ʳ p%a1 a2) p%b)

    rp-a2-b : RP a2 b
    rp-a2-b d d%a2 d%b = rp-ab d (div-*ˡ d%a2 a1) d%b

  ppf->oppf : {a : Nat} -> PPF a -> OPPF a
  ppf->oppf ppf = transport (cong OPPF *'-right-one) (merge-ppf-oppf ppf rp-one oppf-[])


compute-oppf : (n : Nat⁺) -> OPPF ⟨ n ⟩
compute-oppf (suc zero    , _) = oppf-[]
compute-oppf (suc (suc _) , _) = ppf->oppf (compute-ppf (suc-≤ (suc-≤ zero-≤)))

oppf->pos : {a : Nat} -> OPPF a -> Pos' a
oppf->pos oppf-[] = tt
oppf->pos (oppf-cons p n _ oppf) = *'-Pos'-Pos' (snd (prime-power⁺ p ⟨ n ⟩)) (oppf->pos oppf)
