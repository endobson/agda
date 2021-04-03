{-# OPTIONS --cubical --safe --exact-split #-}

module swap-permutation where

open import base
open import cubical
open import equality
open import equivalence
open import fin
open import functions
open import isomorphism
open import nat
open import new-permutation
open import relation

open Iso

data Insert : Nat -> Type₀ where
  insert-first : {n : Nat} -> Insert n
  insert-skip : {n : Nat} -> Insert n -> Insert (suc n)

data InsertPerm : Nat -> Type₀ where
  [] : InsertPerm 0
  _::_ : {n : Nat} -> Insert n -> InsertPerm n -> InsertPerm (suc n)



private
  -- Insert the `m+1`th element into a list of `n` elements that range over
  -- the finite set of `m` elements.
  add-insert : {n m : Nat} -> Insert n
               -> ((FinInd' n) -> (FinInd' m))
               -> ((FinInd' (suc n)) -> (FinInd' (suc m)))
  add-insert insert-first    f zero     = zero
  add-insert insert-first    f (suc j)  = suc (f j)
  add-insert (insert-skip i) f zero     = suc (f zero)
  add-insert (insert-skip i) f (suc j) = (add-insert i (f ∘ suc) j)

  -- The index for the new element
  insert->index : {n : Nat} -> Insert n -> FinInd' (suc n)
  insert->index insert-first    = zero
  insert->index (insert-skip i) = suc (insert->index i)

  -- The adjusted index of an index for an old element
  insert->old-index : {n : Nat} -> Insert n
                      -> FinInd' n -> FinInd' (suc n)
  insert->old-index insert-first    j       = (suc j)
  insert->old-index (insert-skip i) zero    = zero
  insert->old-index (insert-skip i) (suc j) = suc (insert->old-index i j)

  add-insert-rev : {n : Nat} -> Insert n
                   -> ((FinInd' n) -> (FinInd' n))
                   -> ((FinInd' (suc n)) -> (FinInd' (suc n)))
  add-insert-rev i g zero    = insert->index i
  add-insert-rev i g (suc j) = insert->old-index i (g j)

  private
    rightInvNew : {n m : Nat} (f : ((FinInd' n) -> (FinInd' m)))
                  -> (ins : Insert n)
                  -> add-insert ins f (insert->index ins) == zero
    rightInvNew f insert-first    = refl
    rightInvNew f (insert-skip i) = rightInvNew (f ∘ suc) i

    rightInvOld : {n m : Nat} (f : ((FinInd' n) -> (FinInd' m)))
                  -> (ins : Insert n)
                  -> (j : FinInd' n)
                  -> add-insert ins f (insert->old-index ins j) == suc (f j)
    rightInvOld f insert-first    j       = refl
    rightInvOld f (insert-skip i) zero    = refl
    rightInvOld f (insert-skip i) (suc j) = rightInvOld (f ∘ suc) i j

  add-insert-right-inv : {n : Nat}
    -> (f g : ((FinInd' n) -> (FinInd' n)))
    -> ((y : (FinInd' n)) -> (f (g y)) == y)
    -> (ins : Insert n)
    -> (x : FinInd' (suc n))
    -> add-insert ins f (add-insert-rev ins g x) == x
  add-insert-right-inv f g _ ins zero = rightInvNew f ins
  add-insert-right-inv f g fg ins (suc j) =
    rightInvOld f ins (g j) >=> cong suc (fg j)

  private
    leftInvOld' : {n m : Nat} (f : ((FinInd' n) -> (FinInd' m)))
                  -> (ins : Insert n)
                  -> (x : FinInd' (suc n))
                  -> add-insert ins f x == zero
                  -> insert->index ins == x
    leftInvOld' f insert-first      zero    p = refl
    leftInvOld' f insert-first      (suc _) p =
      bot-elim (fin-ind'-zero!=suc (sym p))
    leftInvOld' f (insert-skip ins) zero    p =
      bot-elim (fin-ind'-zero!=suc (sym p))
    leftInvOld' f (insert-skip ins) (suc x) p =
      cong suc (leftInvOld' (f ∘ suc) ins x p)

    leftInvOld : {n : Nat} (f g : ((FinInd' n) -> (FinInd' n)))
                 -> (ins : Insert n)
                 -> (x : FinInd' (suc n))
                 -> add-insert ins f x == zero
                 -> add-insert-rev ins g (add-insert ins f x) == x
    leftInvOld f g ins x p = path >=> leftInvOld' f ins x p
      where
      path : add-insert-rev ins g (add-insert ins f x) == insert->index ins
      path = cong (add-insert-rev ins g) p

    leftInvNew' : {n m : Nat}
                  (f : ((FinInd' n) -> (FinInd' m)))
                  (ins : Insert n)
                  (x : FinInd' (suc n))
                  (y : FinInd' m)
                  -> (add-insert ins f x) == suc y
                  -> Σ[ z ∈ FinInd' n ] (f z == y × insert->old-index ins z == x)
    leftInvNew'             f insert-first      zero    y p = bot-elim (fin-ind'-zero!=suc p)
    leftInvNew'             f insert-first      (suc j) y p = j , (fin-ind'-suc-injective p , refl)
    leftInvNew'             f (insert-skip ins) zero    y p = zero , (fin-ind'-suc-injective p , refl)
    leftInvNew' {n = suc n} f (insert-skip ins) (suc j) y p =
      suc (fst rec) , (fst (snd rec) , cong suc (snd (snd rec)))
      where
      rec : Σ[ z ∈ FinInd' n ] ((f ∘ suc) z == y × insert->old-index ins z == j)
      rec = leftInvNew' (f ∘ suc) ins j y p

    leftInvNew : {n : Nat} (f g : ((FinInd' n) -> (FinInd' n)))
                 -> ((z : (FinInd' n)) -> g (f z) == z)
                 -> (ins : Insert n)
                 -> (x : FinInd' (suc n))
                 -> (y : FinInd' n)
                 -> add-insert ins f x == suc y
                 -> add-insert-rev ins g (add-insert ins f x) == x
    leftInvNew {n} f g gf ins x y y-path = path
      where
      z-paths : Σ[ z ∈ FinInd' n ] ((f z == y) × insert->old-index ins z == x)
      z-paths = leftInvNew' f ins x y y-path
      z       = fst z-paths
      z-path1 = fst (snd z-paths)
      z-path2 = snd (snd z-paths)

      path : add-insert-rev ins g (add-insert ins f x) == x
      path = cong (add-insert-rev ins g) y-path
             >=> cong (insert->old-index ins ∘ g) (sym z-path1)
             >=> cong (insert->old-index ins) (gf z)
             >=> z-path2

  add-insert-left-inv : {n : Nat}
    -> (f g : ((FinInd' n) -> (FinInd' n)))
    -> ((y : (FinInd' n)) -> (g (f y)) == y)
    -> (ins : Insert n)
    -> (x : FinInd' (suc n))
    -> add-insert-rev ins g (add-insert ins f x) == x
  add-insert-left-inv {n} f g gf ins x = helper (add-insert ins f x) refl
    where
    helper : (y : FinInd' (suc n)) -> add-insert ins f x == y
             -> add-insert-rev ins g (add-insert ins f x) == x
    helper zero    p = leftInvOld f g ins x p
    helper (suc y) p = leftInvNew f g gf ins x y p



  module _ where
    open Iso
    add-insert-auto : {n : Nat} -> Insert n
                      -> Auto (FinInd' n)
                      -> Auto (FinInd' (suc n))
    (add-insert-auto ins isoN) .fun = add-insert     ins (fun isoN)
    (add-insert-auto ins isoN) .inv = add-insert-rev ins (inv isoN)
    (add-insert-auto ins isoN) .rightInv =
      add-insert-right-inv (fun isoN) (inv isoN) (rightInv isoN) ins
    (add-insert-auto ins isoN) .leftInv =
      add-insert-left-inv (fun isoN) (inv isoN) (leftInv isoN) ins


  insert-perm->perm : {n : Nat} -> InsertPerm n -> Auto (FinInd' n)
  insert-perm->perm []        = id-iso
  insert-perm->perm (i :: ip) = add-insert-auto i (insert-perm->perm ip)

  index->insert : {n : Nat} -> FinInd' (suc n) -> Insert n
  index->insert               zero    = insert-first
  index->insert {n = (suc _)} (suc i) = insert-skip (index->insert i)


--  module _ where
--    open Iso
--    split-insert-auto : {n : Nat}
--                        -> Auto (FinInd' (suc n))
--                        -> Insert n × Auto (FinInd' n)
--    split-insert-auto {n} i =
--      index->insert (fun i zero) , id-iso
--      where
--      new-iso : Auto (FinInd' n)
--      new-iso .fun = ?
--      new-iso .inv = ?
--      new-iso .rightInv = ?
--      new-iso .leftInv = ?

data Swap : Nat -> Type₀ where
  swap      : {n : Nat} -> Swap (suc (suc n))
  swap-skip : {n : Nat} -> Swap n -> Swap (suc n)

SwapPerm' : Nat -> Nat -> Type₀
SwapPerm' n l = Fin l -> Swap n

SwapPerm : Nat -> Type₀
SwapPerm n = Σ Nat (SwapPerm' n)

finSwap : {n : Nat} -> Swap n -> FinInd' n -> FinInd' n
finSwap swap           zero          = (suc zero)
finSwap swap           (suc zero)    = zero
finSwap swap           (suc (suc x)) = (suc (suc x))
finSwap (swap-skip sw) zero          = zero
finSwap (swap-skip sw) (suc x)       = suc (finSwap sw x)

finSwapPerm' : {n : Nat} -> (l : Nat) -> SwapPerm' n l -> FinInd' n -> FinInd' n
finSwapPerm' zero    _     x = x
finSwapPerm' (suc l) swaps = finSwap (swaps zero-fin) ∘ (finSwapPerm' l (swaps ∘ suc-fin))

finSwapPerm : {n : Nat} -> SwapPerm n -> FinInd' n -> FinInd' n
finSwapPerm (l , swaps) = finSwapPerm' l swaps
