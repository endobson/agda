{-# OPTIONS --cubical --safe --exact-split #-}

module prime-factorization where

open import additive-group.instances.nat
open import base
open import commutative-monoid
open import decision
open import div
open import equality
open import functions
open import nat
open import nat.order
open import order
open import order.instances.nat
open import prime
open import semiring.instances.nat
open import unordered-list

open PrimeUpTo

open import ring.lists NatSemiring
  hiding (product)

prime-product : UList Prime' -> Nat
prime-product = unordered-product ∘ (map fst)

prime-productʰ : CommMonoidʰᵉ _ _ prime-product
prime-productʰ = CommMonoidʰ-∘ unordered-productʰ mapʰ

isPrimeFactorization : UList Prime' -> Nat -> Type₀
isPrimeFactorization primes n = prime-product primes == n

record PrimeFactorization (n : Nat) : Type₀ where
  constructor prime-factorization

  field
    primes : UList Prime'
    product : isPrimeFactorization primes n

  pos : Pos' n
  pos = transport (cong Pos' product) (pos-product primes)
    where
    pos-product : (ps : UList Prime') -> Pos' (prime-product ps)
    pos-product ps = UListElim.prop isPropPos' tt ::* ps
      where
      ::* : (p : Prime') {ps : UList Prime'} -> Pos' (prime-product ps)
            -> Pos' (prime-product (p :: ps))
      ::* p {ps} pos-ps = *'-Pos'-Pos' (Prime'.pos p) pos-ps

  nat⁺ : Nat⁺
  nat⁺ = n , pos

PrimeFactorization⁺ : Nat⁺ -> Type₀
PrimeFactorization⁺ (n , _) = PrimeFactorization n

private

  data Primality : Nat -> Type₀ where
    primality-prime : (p : Prime') -> Primality ⟨ p ⟩
    primality-composite : (a b : Nat) -> a > 1 -> b > 1 -> Primality (a *' b)

  -- ≤ recursion scheme that supports counting up
  data _≤u_ : Nat -> Nat -> Type₀ where
    refl-≤u : {m : Nat} -> m ≤u m
    step-≤u : {m n : Nat} -> suc m ≤u n -> m ≤u n

  ≤u->≤ : {m n : Nat} -> m ≤u n -> m ≤ n
  ≤u->≤ (refl-≤u {m}) = refl-≤
  ≤u->≤ (step-≤u rec) = (pred-≤ (right-suc-≤ (≤u->≤ rec)))

  div->composite : {d n : Nat} -> d != 0 -> d != 1 -> d != n -> n != 0 -> d div' n -> Primality n
  div->composite {d} d0 d1 dn n0 (x , p) =
    transport (\i -> Primality (p i))
              (primality-composite x d (≠->>1 x0 x1) (≠->>1 d0 d1))
    where
    ≠->>1 : {n : Nat} -> n != 0 -> n != 1 -> n > 1
    ≠->>1 {n = 0}             n0 n1 = bot-elim (n0 refl)
    ≠->>1 {n = 1}             n0 n1 = bot-elim (n1 refl)
    ≠->>1 {n = (suc (suc _))} n0 n1 = suc-≤ (suc-≤ zero-≤)

    x0 : x != 0
    x0 x==0 = n0 (sym p >=> (\i -> x==0 i *' d))
    x1 : x != 1
    x1 x==1 = dn (sym *'-left-one >=> (\i -> x==1 (~ i) *' d) >=> p)



  compute-primality : {p : Nat} -> p > 1 -> Primality p
  compute-primality p@{suc (suc p')} p>1  =
      rec (0≤i p' refl-≤u) (prime-up-to-two p p>1)
    where
    0≤i : (i : Nat) -> i ≤u p' -> 0 ≤u p'
    0≤i 0 pr = pr
    0≤i (suc i) pr = 0≤i i (step-≤u pr)

    rec : {i : Nat} -> i ≤u p' -> PrimeUpTo p (suc (suc i)) -> Primality p
    rec refl-≤u pr = primality-prime (_ , (prime-up-to->is-prime' pr))
    rec {i} (step-≤u step) pr with decide-div (suc (suc i)) p
    ... | no not-div = rec step (prime-up-to-suc pr not-div)
    ... | yes div = div->composite {suc (suc i)} {p}
                    (\ p -> bot-elim (zero-suc-absurd (sym p)))
                    (\ p -> bot-elim (zero-suc-absurd (sym (suc-injective p))))
                    (<->!= (suc-≤ (suc-≤ (≤u->≤ step))))
                    (\ p -> bot-elim (zero-suc-absurd (sym p)))
                    div
  compute-primality {suc zero} p>1 = bot-elim (irrefl-< p>1)
  compute-primality {zero}     p>1 = bot-elim (zero-≮ p>1)


data PrimeFactorizationTree : Nat -> Type₀ where
  prime-factorization-tree-prime : (p : Prime') -> PrimeFactorizationTree ⟨ p ⟩
  prime-factorization-tree-composite : {m n : Nat}
    -> PrimeFactorizationTree m
    -> PrimeFactorizationTree n
    -> PrimeFactorizationTree (m *' n)

compute-prime-factorization-tree : {n : Nat} -> n > 1 -> PrimeFactorizationTree n
compute-prime-factorization-tree {n} = strong-induction' cases n
  where

  >1-*'->both< : {a b m : Nat} -> a > 1 -> b > 1 -> a *' b == m -> (a < m × b < m)
  >1-*'->both< {a} {b} {m} a>1 b>1 a*b==m with (transport ≤==≤' a>1) | (transport ≤==≤' b>1)
  ... | (a' , ssa'==a) | (b' , ssb'==b) = a<m , b<m
    where
    ssa'*ssb'==m : (suc (suc a')) *' (suc (suc b')) == m
    ssa'*ssb'==m = transport (\i -> (ssa'==a (~ i)) *' (ssb'==b (~ i)) == m) a*b==m

    rearranged-b : (suc (suc (suc b'))) +' ((suc b') +' a' *' (suc (suc b'))) == m
    rearranged-b =
      sym (+'-right-suc {suc (suc b')})
      >=> ssa'*ssb'==m

    rearranged-a : (suc (suc (suc a'))) +' ((suc a') +' b' *' (suc (suc a'))) == m
    rearranged-a =
      sym (+'-right-suc {suc (suc a')})
      >=> (*'-commute {suc (suc b')} {suc (suc a')})
      >=> ssa'*ssb'==m

    sssa'≤Σ'm : (suc (suc (suc a'))) ≤' m
    sssb'≤Σ'm : (suc (suc (suc b'))) ≤' m
    sssa'≤Σ'm = (_ , rearranged-a)
    sssb'≤Σ'm = (_ , rearranged-b)

    a<m : a < m
    b<m : b < m
    a<m = transport (\i -> (≤==≤' {suc (ssa'==a i)} {m} (~ i))) sssa'≤Σ'm
    b<m = transport (\i -> (≤==≤' {suc (ssb'==b i)} {m} (~ i))) sssb'≤Σ'm

  cases : {m : Nat}
         -> ({n : Nat} -> n < m -> n > 1 -> PrimeFactorizationTree n)
         -> m > 1 -> PrimeFactorizationTree m
  cases f m>1 with (compute-primality m>1)
  ... | (primality-prime prime) = (prime-factorization-tree-prime prime)
  ... | (primality-composite a b a>1 b>1) with (>1-*'->both< a>1 b>1 refl)
  ...   | (a<m , b<m) = prime-factorization-tree-composite (f a<m a>1) (f b<m b>1)

private
  prime-factorization-* : {m n : Nat}
    -> PrimeFactorization m
    -> PrimeFactorization n
    -> PrimeFactorization (m *' n)
  prime-factorization-* (prime-factorization p1s pr1) (prime-factorization p2s pr2) =
    (prime-factorization
      (p1s ++ p2s)
      (p >=> (\i -> (pr1 i) *' (pr2 i))))
    where
    p = CommMonoidʰ.preserves-∙ prime-productʰ p1s p2s

  prime-factorization-base : (p : Prime') -> PrimeFactorization ⟨ p ⟩
  prime-factorization-base p =
    (prime-factorization
      (p :: [])
      (*'-right-one {⟨ p ⟩}))

  convert-prime-factorization : {n : Nat} -> PrimeFactorizationTree n -> PrimeFactorization n
  convert-prime-factorization (prime-factorization-tree-prime p) =
    prime-factorization-base p
  convert-prime-factorization (prime-factorization-tree-composite t1 t2) =
    prime-factorization-* (convert-prime-factorization t1) (convert-prime-factorization t2)

exists-prime-divisor : {n : Nat} -> n > 1 -> Σ[ p ∈ Prime' ] (⟨ p ⟩ div' n)
exists-prime-divisor {n} n>1 = rec (compute-prime-factorization-tree n>1) div'-refl
  where
  rec : {a : Nat} -> (PrimeFactorizationTree a) -> a div' n -> Σ[ p ∈ Prime' ] (⟨ p ⟩ div' n)
  rec (prime-factorization-tree-prime (a , prime-a)) a%n = (a , prime-a) , a%n
  rec {a} (prime-factorization-tree-composite {d} {e} df ef) a%n =
    rec ef (div'-trans (d , refl) a%n)

-- Prime factorizations exist and are computable

compute-prime-factorization : (n : Nat⁺) -> PrimeFactorization⁺ n
compute-prime-factorization (suc zero , _)    =
  (prime-factorization [] refl)
compute-prime-factorization (suc (suc n) , _) =
  convert-prime-factorization (compute-prime-factorization-tree (suc-≤ (zero-<)))

¬prime-factorization-zero : ¬ (PrimeFactorization 0)
¬prime-factorization-zero pf0 = (PrimeFactorization.pos pf0)

prime-prime-factorization : (p : Prime') -> PrimeFactorization ⟨ p ⟩
prime-prime-factorization p =
  (prime-factorization (p :: []) *'-right-one)

prime-power-prime-factorization : (p : Prime') -> (n : Nat) -> PrimeFactorization (prime-power p n)
prime-power-prime-factorization p zero    = (prime-factorization [] refl)
prime-power-prime-factorization p (suc n) = handle (prime-power-prime-factorization p n)
  where
  handle : (PrimeFactorization (prime-power p n)) -> (PrimeFactorization (prime-power p (suc n)))
  handle (prime-factorization factors path) =
    (prime-factorization (p :: factors) (cong (⟨ p ⟩ *'_) path))

*'-prime-factorization : {a b : Nat}
                         -> PrimeFactorization a -> PrimeFactorization b
                         -> PrimeFactorization (a *' b)
*'-prime-factorization {a} {b} (prime-factorization ps-a path-a)
                               (prime-factorization ps-b path-b) = record
  { primes = ps-a ++ ps-b
  ; product =
      CommMonoidʰ.preserves-∙ prime-productʰ ps-a ps-b
      >=> (\i -> (path-a i) *' (path-b i))
  }

Decidable-IsPrime' : Decidable IsPrime'
Decidable-IsPrime' zero = no (\p -> IsPrime'.pos p)
Decidable-IsPrime' (suc zero) = no (\p -> irrefl-< (IsPrime'.>1 p))
Decidable-IsPrime' n@(suc (suc _)) = handle (compute-primality (suc-≤ (suc-≤ zero-≤)))
  where
  handle : {n : Nat} -> Primality n -> Dec (IsPrime' n)
  handle (primality-prime p) = yes (snd p)
  handle (primality-composite a b a>1 b>1) = no ¬p
    where
    b%ab : b div' (a *' b)
    b%ab = a , refl
    ¬p : ¬ (IsPrime' (a *' b))
    ¬p isp = handle2 (prime-only-divisors p b%ab)
      where
      p : Prime'
      p = a *' b , isp
      handle2 : ¬ (b == (a *' b) ⊎ b == 1)
      handle2 (inj-r b==1) = <->!= b>1 (sym b==1)
      handle2 (inj-l b==a*'b) = <->!= a>1 (sym a==1)
        where
        b%ab2 : b div' (a *' b)
        b%ab2 = 1 , *'-left-one >=> b==a*'b
        ab⁺ : Nat⁺
        ab⁺ = a *' b , *'-Pos'-Pos' (<->Pos' a>1) (<->Pos' b>1)
        a==1 : a == 1
        a==1 = cong fst (isPropDiv' ab⁺ b%ab b%ab2)
