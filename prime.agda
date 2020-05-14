module prime where

open import equality
open import int
open import abs
open import nat
open import div



data Prime' : Nat -> Set where
  prime' : (p' : Nat)
          -> ((d : Nat) -> d <s (suc p') -> (d div' (suc p')) -> d == 1)
          -> Prime' (suc p')

data PrimeFactorization : Nat -> Set where
  prime-factorization-prime : {p : Nat} -> Prime' p -> PrimeFactorization p
  prime-factorization-composite : {m n : Nat}
    -> PrimeFactorization m
    -> PrimeFactorization n
    -> PrimeFactorization (m *' n)

data Primality : Nat -> Set where
  primality-prime : {p : Nat} -> Prime' p -> Primality p
  primality-composite : {a' b' : Nat} (a b : Nat) -> {a == (suc (suc a'))} -> {b == (suc (suc b'))}
                        -> Primality ((suc (suc a')) *' (suc (suc b')))

private
  data PrimeUpTo : Nat -> Nat -> Set where
    prime-up-to : (p' : Nat) -> (bound : Nat)
                  -> ((d : Nat) -> d <s bound -> (d div' (suc p')) -> d == 1)
                  -> PrimeUpTo (suc p') bound

  prime-up-to->prime' : {n : Nat} -> PrimeUpTo n n -> Prime' n
  prime-up-to->prime' (prime-up-to p' (suc p') f) = (prime' p' f)

  prime-up-to-zero : (p' : Nat) -> PrimeUpTo (suc p') zero
  prime-up-to-zero p' = prime-up-to p' zero (\ d ())

  prime-up-to-suc : {p b : Nat} -> PrimeUpTo p b -> ¬(b div' p) -> PrimeUpTo p (suc b)
  prime-up-to-suc (prime-up-to p' b f) ¬bp = (prime-up-to p' (suc b) g)
    where
    g : (d : Nat) -> d <s (suc b) -> (d div' (suc p')) -> d == 1
    g d refl-≤s dp = bot-elim (¬bp dp)
    g d (step-≤s d≤b) dp = f d d≤b dp

  prime-up-to-one : (p' : Nat) -> PrimeUpTo (suc p') 1
  prime-up-to-one p' = prime-up-to-suc (prime-up-to-zero p') pr
    where
    pr : ¬(0 div' (suc p'))
    pr 0p with (div'-zero->zero 0p)
    ...      | ()

  prime-up-to-two : (p' : Nat) -> PrimeUpTo (suc p') 2
  prime-up-to-two p' = prime-up-to p' 2 g
    where
    g : (d : Nat) -> d <s 2 -> (d div' (suc p')) -> d == 1
    g d refl-≤s dp = refl
    g d (step-≤s d≤b) dp with (prime-up-to-one p') 
    ... | (prime-up-to _ _ f) = f d d≤b dp

  2-is-prime : Prime' 2
  2-is-prime = prime-up-to->prime' (prime-up-to-two 1)

  data _≤u_ : Nat -> Nat -> Set where
    refl-≤u : {m : Nat} -> m ≤u m
    step-≤u : {m n : Nat} -> suc m ≤u n -> m ≤u n
  
  ≤u->≤ : {m n : Nat} -> m ≤u n -> m ≤ n
  ≤u->≤ (refl-≤u {m}) = same-≤ m
  ≤u->≤ (step-≤u rec) = (dec-≤ (suc-≤ (≤u->≤ rec)))
 

  div->composite : {d n : Nat} -> d != 0 -> d != 1 -> d != n -> n != 0 -> d div' n -> Primality n
  div->composite d0 d1 dn n0 (div'-exists 0 n x refl) = bot-elim (d0 refl)
  div->composite d0 d1 dn n0 (div'-exists 1 n x refl) = bot-elim (d1 refl)
  div->composite d0 d1 dn n0 (div'-exists d n 0 refl) = bot-elim (n0 refl)
  div->composite d0 d1 dn n0 (div'-exists d n 1 refl) = bot-elim (dn (sym (+'-right-zero {d})))
  div->composite d0 d1 dn n0 (div'-exists d@(suc (suc d')) n x@(suc (suc x')) refl) = 
    primality-composite x d {refl} {refl}

  >1 : {n' : Nat} -> 2 ≤ (suc (suc n'))
  >1 {n'} = inc-≤ (inc-≤ zero-≤)

  compute-primality : {p : Nat} -> p > 1 -> Primality p
  compute-primality {suc (suc p')} (inc-≤ (inc-≤ _)) =
      rec (0≤i p' refl-≤u) (prime-up-to-two (suc p'))
    where
    0≤i : (i : Nat) -> i ≤u p' -> 0 ≤u p'
    0≤i 0 pr = pr
    0≤i (suc i) pr = 0≤i i (step-≤u pr)
    
    rec : {i : Nat} -> i ≤u p' -> PrimeUpTo (suc (suc p')) (suc (suc i)) -> Primality (suc (suc p'))
    rec refl-≤u pr = primality-prime (prime-up-to->prime' pr)
    rec {i} (step-≤u step) pr with decide-div (suc (suc i)) (suc (suc p'))
    ... | no not-div = rec step (prime-up-to-suc pr not-div)
    ... | yes div = div->composite {suc (suc i)} {suc (suc p')} 
                    (\ ()) (\ ()) (<->!= (inc-≤ (inc-≤ (≤u->≤ step)))) (\ ()) div

    
  compute-prime-factorization : {n : Nat} -> n > 1 -> PrimeFactorization n
  compute-prime-factorization {p} p>1  = rec p>1 (same-≤ p)
    where
    rec : {i : Nat} {p : Nat} -> p > 1 -> (p ≤ i) -> PrimeFactorization p
    rec () zero-≤
    rec (inc-≤ ()) (inc-≤ zero-≤)
    rec _ (inc-≤ (inc-≤ zero-≤)) = (prime-factorization-prime 2-is-prime)
    rec {_} p@{suc (suc p')} p>1 (inc-≤ p-bound) with (compute-primality p>1)
    ... | (primality-prime prime) = (prime-factorization-prime prime)
    ... | (primality-composite m@(suc (suc m')) n@(suc (suc n')) {refl} {refl}) =
          (prime-factorization-composite
            (rec (>1) (trans-≤ (dec-≤ m-bound) p-bound))
            (rec (>1) (trans-≤ (dec-≤ n-bound) p-bound)))
          where
          base-eq-m : n *' m == p
          base-eq-n : m *' n == p
          base-eq-m = *'-commute {n} {m} >=> base-eq-n
          base-eq-n = refl

          rearranged-eq2-m : (suc m) +' (1 +' (m' +' n' *' m)) == p
          rearranged-eq2-n : (suc n) +' (1 +' (n' +' m' *' n)) == p
          rearranged-eq2-m = sym (+'-right-suc {m}) >=> base-eq-m
          rearranged-eq2-n = sym (+'-right-suc {n}) >=> base-eq-n

          m-bound : (suc m ≤ p)
          n-bound : (suc n ≤ p)
          m-bound = (≤-a+'b==c rearranged-eq2-m)
          n-bound = (≤-a+'b==c rearranged-eq2-n)



    PrimeDivisor : Nat -> Nat -> Set
    PrimeDivisor n d = Prime' d × d div' n

    -- exists-prime-divisor : (n' : Nat) -> exists (PrimeDivisor (suc (suc n')))
    -- exists-prime-divisor n' = rec1 (compute-prime-factorization n')
    --   where 
    --   rec1 : (n : Nat) -> (PrimeFactorization n)




-- data Prime : Int -> Set where
--   prime : (p : Int) -> Pos p
--           -> ((d : Int) -> Pos d -> (d div p) -> (d != (int 1)) -> (d == p))
--           -> Prime p
--
-- prime'->prime : {p : Nat} -> Prime' p -> {Pos (int p)} -> Prime (int p)
-- prime'->prime {p} (prime' p' f) {pos-p} = (prime (int p) pos-p g)
--   where
--   g : (d : Int) -> Pos d -> (d div (int p)) -> (d != (int 1)) -> (d == (int p))
--   g (pos d') pos-d d-div-p not-1 = (cong int (f (suc d') nat-< d-div'-p nat-d-not-0 nat-d-not-1))
--     where
--     nat-≤-base : (suc d') ≤ abs' (int p)
--     nat-≤-base = div-abs-≤ {pos d'} {int p} {pos-d} {pos-p} d-div-p
--     nat-≤ : (suc d') ≤ p
--     nat-≤ rewrite (sym (abs'-int-id {p})) = nat-≤-base
--     nat-d-not-0 : (suc d') != 0
--     nat-d-not-0 ()
--     nat-d-not-1 : (suc d') != 1
--     nat-d-not-1 pr = not-1 (cong int pr)
--     d-div-p'-base : (suc d') div' abs' (int p)
--     d-div-p'-base = div->div' {pos d'} {int p} d-div-p
--     d-div-p' : (suc d') div' p
--     d-div-p' rewrite (sym (abs'-int-id {p})) = d-div-p'-base
