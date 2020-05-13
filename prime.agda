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
  prime-factor-one : PrimeFactorization 1
  prime-factor-prime : {m n : Nat}
    -> (p : Prime' m)
    -> (f : PrimeFactorization n)
    -> PrimeFactorization (m *' n)


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
