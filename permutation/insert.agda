{-# OPTIONS --cubical --safe --exact-split #-}

module permutation.insert where

open import base
open import equality
open import fin
open import functions
open import hlevel
open import isomorphism
open import nat
open import nat.order
open import sigma.base

data InsertPerm : Nat -> Type₀ where
  [] : InsertPerm 0
  _::_ : {n : Nat} -> Fin (suc n) -> InsertPerm n -> InsertPerm (suc n)

private
  FinInj : Nat -> Type₀
  FinInj n = Σ (Fin n -> Fin n) Injective

private
  module insert-iso where
    encode-iperm' : {n : Nat} -> InsertPerm n -> (Fin n -> Fin n)
    encode-iperm' [] i = i
    encode-iperm' (ins :: perm) =
      fin-rec ins (avoid-fin ins ∘ (encode-iperm' perm))

    encode-iperm'-inj : {n : Nat} -> (i : InsertPerm n) -> Injective (encode-iperm' i)
    encode-iperm'-inj [] {j1} {j2} p = bot-elim (¬fin-zero j1)
    encode-iperm'-inj (ins :: perm) {zero   , lt1} {zero   , lt2} p = fin-i-path refl
    encode-iperm'-inj (ins :: perm) {zero   , lt1} {suc j2 , lt2} p =
      bot-elim (avoid-fin-no-path _ (sym p))
    encode-iperm'-inj (ins :: perm) {suc j1 , lt1} {zero   , lt2} p =
      bot-elim (avoid-fin-no-path _ p)
    encode-iperm'-inj (ins :: perm) {suc j1 , lt1} {suc j2 , lt2} p =
      fin-i-path (cong suc (cong Fin.i path))
      where
      path : (j1 , pred-≤ lt1) == (j2 , pred-≤ lt2)
      path = encode-iperm'-inj perm (avoid-fin-inj ins p)

    encode-iperm : {n : Nat} -> InsertPerm n -> FinInj n
    encode-iperm i = encode-iperm' i , encode-iperm'-inj i

    abstract
      smaller-fun' : {n : Nat} -> (f : Fin (suc n) -> Fin (suc n))
                    -> Injective f -> (Fin n -> Fin n)
      smaller-fun' f f-inj x = remove-fin (f zero-fin) (f (suc-fin x))
                               (zero-fin!=suc-fin ∘ f-inj)

      smaller-fun'-inj : {n : Nat} (f : Fin (suc n) -> Fin (suc n)) -> (f-inj : Injective f)
                         -> Injective (smaller-fun' f f-inj)
      smaller-fun'-inj f f-inj {j1} {j2} p =
        suc-fin-injective
          (f-inj (remove-fin-inj (f zero-fin) (f (suc-fin j1)) (f (suc-fin j2))
                                 (zero-fin!=suc-fin ∘ f-inj) (zero-fin!=suc-fin ∘ f-inj) p))

    smaller-fun : {n : Nat} -> (FinInj (suc n)) -> (FinInj n)
    smaller-fun (f , f-inj) = smaller-fun' f f-inj , smaller-fun'-inj f f-inj

    abstract

      smaller-fun-path' :
        {n : Nat} (f : FinInj (suc n)) (i : (Fin n)) ->
        avoid-fin (⟨ f ⟩ zero-fin) (⟨ smaller-fun f ⟩ i)
          == ⟨ f ⟩ (suc-fin i)
      smaller-fun-path' (f , f-inj) i =
        avoid-fin-remove-fin-path (f zero-fin) (f (suc-fin i))
                                 (zero-fin!=suc-fin ∘ f-inj)

      smaller-encode' : {n : Nat} -> (ins : Fin (suc n)) (perm : InsertPerm n)
                        -> smaller-fun' (encode-iperm' (ins :: perm)) (encode-iperm'-inj (ins :: perm))
                           == (encode-iperm' perm)
      smaller-encode' {zero}      ins perm = isPropΠ (\_ -> isPropFin0) _ _
      smaller-encode' {n@(suc _)} ins perm = ans
        where
        module _ where
          f = encode-iperm' (ins :: perm)
          f-inj = encode-iperm'-inj (ins :: perm)
          g = encode-iperm' perm

        point : (i : Fin n) -> smaller-fun' f f-inj i == g i
        point i = ans
          where
          ans2 : Path (Fin n)
                  (remove-fin ins
                              (avoid-fin ins
                                        (g ((Fin.i i) , pred-≤ (suc-≤ (Fin.i<n i)))))
                              (zero-fin!=suc-fin ∘ f-inj))
                  (g i)
          ans2 = remove-fin-avoid-fin-path ins _ (zero-fin!=suc-fin ∘ f-inj)
                 >=> (cong g (fin-i-path refl))

          ans : remove-fin ins (f (suc-fin i)) (zero-fin!=suc-fin ∘ f-inj)
                == g i
          ans = ans2

        ans : smaller-fun' f f-inj == g
        ans k i = point i k


    decode-iperm : {n : Nat} -> FinInj n -> InsertPerm n
    decode-iperm {zero}  f = []
    decode-iperm {suc n} f = (⟨ f ⟩ zero-fin) :: (decode-iperm (smaller-fun f))


    encode'-decode-point : {n : Nat} -> (fi : FinInj n) -> (x : Fin n)
                           -> encode-iperm' (decode-iperm fi) x == (fst fi) x
    encode'-decode-point {zero} (f , f-inj) x = bot-elim (¬fin-zero x)
    encode'-decode-point {suc n} fi@(f , _) =
      fin-elim encode'-decode-point0 encode'-decode-point-suc
      where
      encode'-decode-point0 : encode-iperm' (decode-iperm fi) zero-fin == f zero-fin
      encode'-decode-point0 = cong f (fin-i-path refl)

      encode'-decode-point-suc :
        (x : Fin n) -> encode-iperm' (decode-iperm fi) (suc-fin x) == f (suc-fin x)
      encode'-decode-point-suc x = ans
        where
        fi' : FinInj n
        fi' = smaller-fun fi
        f' = fst fi'

        rec : encode-iperm' (decode-iperm fi') x == f' x
        rec = encode'-decode-point fi' x

        ans4 : avoid-fin (f zero-fin) (f' x) == f (suc-fin x)
        ans4 = smaller-fun-path' fi x

        ans2 : avoid-fin (f zero-fin)
                (encode-iperm' (decode-iperm fi') x) == f (suc-fin x)
        ans2 = cong (avoid-fin (f zero-fin)) rec
               >=> ans4

        ans : encode-iperm' (decode-iperm fi) (suc-fin x) == f (suc-fin x)
        ans = fin-rec-suc-point (f zero-fin)
                (avoid-fin (f zero-fin) ∘ (encode-iperm' (decode-iperm fi'))) x
              >=> ans2

    encode'-decode : {n : Nat} -> (fi : FinInj n)
                     -> encode-iperm' (decode-iperm fi) == (fst fi)
    encode'-decode fi i x = encode'-decode-point fi x i

    encode-decode : {n : Nat} -> (fi : FinInj n)
                    -> encode-iperm (decode-iperm fi) == fi
    encode-decode fi = ΣProp-path (isPropInjective isSetFin) (encode'-decode fi)


    decode-encode : {n : Nat} -> (perm : InsertPerm n)
                    -> decode-iperm (encode-iperm perm) == perm
    decode-encode []            = refl
    decode-encode {suc n} (ins :: perm) = cong (ins ::_) perm-path
      where
      f : Fin (suc n) -> Fin (suc n)
      f = encode-iperm' (ins :: perm)
      f-inj : Injective f
      f-inj = encode-iperm'-inj (ins :: perm)
      Σsf : FinInj n
      Σsf = smaller-fun (f , f-inj)

      smaller-encode : Σsf == (encode-iperm perm)
      smaller-encode = ΣProp-path (isPropInjective isSetFin) (smaller-encode' ins perm)

      perm-path : (decode-iperm Σsf) == perm
      perm-path = cong decode-iperm smaller-encode >=> decode-encode perm


    fin-injective-insert-permutation-iso :
      {n : Nat} -> Iso (FinInj n) (InsertPerm n)
    fin-injective-insert-permutation-iso .Iso.fun = decode-iperm
    fin-injective-insert-permutation-iso .Iso.inv = encode-iperm
    fin-injective-insert-permutation-iso .Iso.rightInv = decode-encode
    fin-injective-insert-permutation-iso .Iso.leftInv  = encode-decode

open insert-iso public using
  ( encode-iperm
  ; encode-iperm'
  ; decode-iperm
  ; fin-injective-insert-permutation-iso
  ) renaming
  ( decode-encode to decode-encode-iperm
  ; encode-decode to encode-decode-iperm
  ; encode'-decode to encode'-decode-iperm
  )
