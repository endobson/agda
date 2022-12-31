{-# OPTIONS --cubical --safe --exact-split #-}

module permutation.swap-tree where

open import base
open import equality
open import fin
open import functions
open import nat
open import nat.order
open import permutation.insert

data SwapTree : Nat -> Type₀ where
  id-swap-tree : {n : Nat} -> SwapTree n
  swap-swap-tree : {n : Nat} -> SwapTree (suc (suc n))
  compose-swap-tree : {n : Nat} -> SwapTree n -> SwapTree n -> SwapTree n
  ignore-swap-tree : {n : Nat} -> SwapTree n -> SwapTree (suc n)

private
  one-fin : {n : Nat} -> Fin (suc (suc n))
  one-fin = suc-fin zero-fin

encode-swap-tree : {n : Nat} -> SwapTree n -> Fin n -> Fin n
encode-swap-tree id-swap-tree x = x
encode-swap-tree swap-swap-tree =
  fin-rec one-fin (fin-rec zero-fin (\x -> suc-fin (suc-fin x)))
encode-swap-tree (compose-swap-tree t1 t2) =
  encode-swap-tree t1 ∘ encode-swap-tree t2
encode-swap-tree (ignore-swap-tree t) =
  fin-rec zero-fin (suc-fin ∘ encode-swap-tree t)


insert->swap-tree : {n : Nat} -> Fin n -> SwapTree n
insert->swap-tree {zero}          = bot-elim ∘ ¬fin-zero
insert->swap-tree {suc zero}    _ = id-swap-tree
insert->swap-tree {suc (suc _)} =
  fin-rec id-swap-tree
    (\i -> compose-swap-tree (ignore-swap-tree (insert->swap-tree i)) swap-swap-tree)

iperm->swap-tree : {n : Nat} -> InsertPerm n -> SwapTree n
iperm->swap-tree [] = id-swap-tree
iperm->swap-tree (index :: perm) =
   compose-swap-tree (insert->swap-tree index) (ignore-swap-tree (iperm->swap-tree perm))

private
  enc-st : {n : Nat} -> SwapTree n -> (Fin n -> Fin n)
  enc-st = encode-swap-tree
  ∘-st : {n : Nat} -> SwapTree n -> SwapTree n -> SwapTree n
  ∘-st = compose-swap-tree
  ign-st : {n : Nat} -> SwapTree n -> SwapTree (suc n)
  ign-st = ignore-swap-tree
  swap-st : {n : Nat} -> SwapTree (suc (suc n))
  swap-st = swap-swap-tree

  ins->st : {n : Nat} -> Fin n -> SwapTree n
  ins->st = insert->swap-tree
  ip->st : {n : Nat} -> InsertPerm n -> SwapTree n
  ip->st = iperm->swap-tree

abstract
  private
    insert-swap-tree-path0 :
      {n : Nat} -> (ins : (Fin (suc n)))
      -> enc-st (ins->st ins) zero-fin == ins
    insert-swap-tree-path0 {zero} ins = isPropFin1 zero-fin ins
    insert-swap-tree-path0 {suc _} (0     , lt) = fin-i-path refl
    insert-swap-tree-path0 {suc n} ins@(suc i , lt) =
      begin
        enc-st (ins->st ins) zero-fin
      ==<>
        enc-st (∘-st (ign-st (ins->st ins')) swap-st) zero-fin
      ==<>
        enc-st (ign-st (ins->st ins')) one-fin
      ==<>
        fin-rec zero-fin (suc-fin ∘ enc-st (ins->st ins')) one-fin
      ==< fin-rec-suc-point zero-fin (suc-fin ∘ enc-st (ins->st ins')) zero-fin >
        (suc-fin ∘ enc-st (ins->st ins')) zero-fin
      ==< cong suc-fin (insert-swap-tree-path0 ins') >
        (suc-fin ins')
      ==< fin-i-path refl >
        ins
      end
      where
      ins' : Fin (suc n)
      ins' = i , pred-≤ lt


    insert-swap-tree-path-suc' :
      {n : Nat} -> (ins : (Fin (suc n))) -> (x : Fin n)
      -> enc-st (ins->st ins) (suc-fin x) == (avoid-fin ins x)
    insert-swap-tree-path-suc' {zero}  _ x = bot-elim (¬fin-zero x)
    insert-swap-tree-path-suc' {suc _} ins@(0     , lt) x = refl
    insert-swap-tree-path-suc' {suc _} ins@(suc i , lt) x@(zero , lt2) = refl
    insert-swap-tree-path-suc' {suc n} ins@(suc i , lt) x@(suc j , lt2) =
      begin
        enc-st (ins->st ins) (suc-fin x)
      ==<>
        enc-st (∘-st (ign-st (ins->st ins')) swap-st) (suc-fin x)
      ==<>
        (enc-st (ign-st (ins->st ins')) ∘ (enc-st swap-st)) (suc-fin x)
      ==<>
        (enc-st (ign-st (ins->st ins'))
          ((fin-rec one-fin (fin-rec zero-fin (\x -> suc-fin (suc-fin x))))
           (suc-fin x)))
      ==< cong (enc-st (ign-st (ins->st ins')))
               (fin-rec-suc-point one-fin (fin-rec zero-fin (\x -> suc-fin (suc-fin x)))
                                  x) >
        enc-st (ign-st (ins->st ins')) (suc-fin (suc-fin x'))
      ==<>
        fin-rec zero-fin (suc-fin ∘ enc-st (ins->st ins')) (suc-fin (suc-fin x'))
      ==< fin-rec-suc-point zero-fin (suc-fin ∘ enc-st (ins->st ins')) (suc-fin x') >
        suc-fin (enc-st (ins->st ins') (suc-fin x'))
      ==< cong suc-fin (insert-swap-tree-path-suc' ins' x') >
        suc-fin (avoid-fin ins' x')
      ==<>
        avoid-fin ins x
      end
      where
      ins' : Fin (suc n)
      ins' = i , pred-≤ lt
      x' : Fin n
      x' = j , pred-≤ lt2


    insert-swap-tree-path-suc :
      {n : Nat} -> (ins : (Fin (suc n))) -> (f : Fin n -> Fin n)
      -> (x : Fin n)
      -> enc-st (ins->st ins) (fin-rec zero-fin (suc-fin ∘ f) (suc-fin x))
         ==
         fin-rec ins (avoid-fin ins ∘ f) (suc-fin x)
    insert-swap-tree-path-suc ins f x =
      begin
        enc-st (ins->st ins) (fin-rec zero-fin (suc-fin ∘ f) (suc-fin x))
      ==< cong (enc-st (ins->st ins)) (fin-rec-suc-point zero-fin (suc-fin ∘ f) x) >
        enc-st (ins->st ins) (suc-fin (f x))
      ==< insert-swap-tree-path-suc' ins (f x) >
        (avoid-fin ins (f x))
      ==< sym (fin-rec-suc-point ins (avoid-fin ins ∘ f) x) >
        fin-rec ins (avoid-fin ins ∘ f) (suc-fin x)
      end

    insert-swap-tree-point-path : {n : Nat} -> (ins : (Fin (suc n))) -> (f : Fin n -> Fin n)
      -> (x : Fin (suc n))
      -> enc-st (ins->st ins) (fin-rec zero-fin (suc-fin ∘ f) x)
         ==
         fin-rec ins (avoid-fin ins ∘ f) x
    insert-swap-tree-point-path {n} ins f =
      fin-elim (insert-swap-tree-path0 ins) (insert-swap-tree-path-suc ins f)

    insert-swap-tree-path : {n : Nat} -> (ins : (Fin (suc n))) -> (f : Fin n -> Fin n)
      -> enc-st (ins->st ins) ∘ fin-rec zero-fin (suc-fin ∘ f)
         ==
         fin-rec ins (avoid-fin ins ∘ f)
    insert-swap-tree-path ins f k x = insert-swap-tree-point-path ins f x k


  iperm-swap-tree-path : {n : Nat} -> (ip : InsertPerm n)
                         -> enc-st (ip->st ip) == encode-iperm' ip
  iperm-swap-tree-path [] = refl
  iperm-swap-tree-path {suc zero} (ins :: []) =
    cong (\i -> encode-iperm' (i :: [])) (isPropFin1 zero-fin ins)

  iperm-swap-tree-path {suc (suc _)} (ins :: perm) =
    begin
      enc-st (ip->st (ins :: perm))
    ==<>
      enc-st (∘-st (ins->st ins) (ign-st (ip->st perm)))
    ==<>
      (enc-st (ins->st ins)) ∘ (enc-st (ign-st (ip->st perm)))
    ==< insert-swap-tree-path ins _ >
      fin-rec ins (avoid-fin ins ∘ (enc-st (ip->st perm)))
    ==< cong (\x -> fin-rec ins (avoid-fin ins ∘ x)) (iperm-swap-tree-path perm) >
      fin-rec ins (avoid-fin ins ∘ (encode-iperm' perm))
    ==<>
      encode-iperm' (ins :: perm)
    end
