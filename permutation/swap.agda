{-# OPTIONS --cubical --safe --exact-split #-}

module permutation.swap where

open import base
open import equality
open import equivalence
open import fin
open import functions
open import funext
open import nat
open import permutation.swap-tree
open import permutation.insert
open import sigma

data Swap : Nat -> Type₀ where
  swap      : {n : Nat} -> Swap (suc (suc n))
  swap-skip : {n : Nat} -> Swap n -> Swap (suc n)

SwapPerm' : Nat -> Nat -> Type₀
SwapPerm' n l = Fin l -> Swap n

SwapPerm : Nat -> Type₀
SwapPerm n = Σ Nat (SwapPerm' n)


encode-swap : {n : Nat} -> Swap n -> Fin n -> Fin n
encode-swap swap           (zero          , lt) = (suc zero) , suc-≤ (suc-≤ zero-≤)
encode-swap swap           ((suc zero)    , lt) = zero , suc-≤ zero-≤
encode-swap swap           ((suc (suc x)) , lt) = (suc (suc x)) , lt
encode-swap (swap-skip sw) (zero          , lt) = zero , lt
encode-swap (swap-skip sw) ((suc x)       , lt) = suc-fin (encode-swap sw (x , pred-≤ lt))

encode-sperm' : {n : Nat} -> (l : Nat) -> SwapPerm' n l -> Fin n -> Fin n
encode-sperm' zero    _     x = x
encode-sperm' (suc l) swaps = encode-swap (swaps zero-fin) ∘ (encode-sperm' l (swaps ∘ suc-fin))

encode-sperm : {n : Nat} -> SwapPerm n -> Fin n -> Fin n
encode-sperm (l , swaps) = encode-sperm' l swaps

private
  one-fin : {n : Nat} -> Fin (suc (suc n))
  one-fin = suc-fin zero-fin


abstract
  encode-swap-injective : {n : Nat} -> (sw : Swap n) -> Injective (encode-swap sw)
  encode-swap-injective swap           {zero          , lt} {zero          , lt2} p =
    ΣProp-path isProp≤ refl
  encode-swap-injective swap           {zero          , lt} {(suc zero)    , lt2} p =
    zero-suc-absurd (cong fst (sym p))
  encode-swap-injective swap           {zero          , lt} {(suc (suc _)) , lt2} p =
    zero-suc-absurd (suc-injective (cong fst p))
  encode-swap-injective swap           {(suc zero)    , lt} {zero          , lt2} p =
    zero-suc-absurd (cong fst p)
  encode-swap-injective swap           {(suc zero)    , lt} {(suc zero)    , lt2} p =
    ΣProp-path isProp≤ refl
  encode-swap-injective swap           {(suc zero)    , lt} {(suc (suc _)) , lt2} p =
    zero-suc-absurd (cong fst p)
  encode-swap-injective swap           {(suc (suc _)) , lt} {zero          , lt2} p =
    zero-suc-absurd (suc-injective (cong fst (sym p)))
  encode-swap-injective swap           {(suc (suc _)) , lt} {(suc zero)    , lt2} p =
    zero-suc-absurd (cong fst (sym p))
  encode-swap-injective swap           {(suc (suc _)) , lt} {(suc (suc _)) , lt2} p =
    p
  encode-swap-injective (swap-skip sw) {zero          , lt} {zero          , lt2} p =
    ΣProp-path isProp≤ refl
  encode-swap-injective (swap-skip sw) {zero          , lt} {(suc _)       , lt2} p =
    zero-suc-absurd (cong fst p)
  encode-swap-injective (swap-skip sw) {(suc _)       , lt} {zero          , lt2} p =
    zero-suc-absurd (cong fst (sym p))
  encode-swap-injective (swap-skip sw) {(suc i)       , lt} {(suc j)       , lt2} p =
    ΣProp-path isProp≤
      (cong (suc ∘ fst) (encode-swap-injective sw {i , pred-≤ lt} {j , pred-≤ lt2} (suc-fin-injective p)))

  private
    -- SwapPerm manipulation functions
    empty-sperm : {n : Nat} -> SwapPerm n
    empty-sperm = 0 , (bot-elim ∘ ¬fin-zero)
    single-sperm : {n : Nat} -> Swap n -> SwapPerm n
    single-sperm s = 1 , \_ -> s

    sperm-add-elem : {n : Nat} -> SwapPerm n -> SwapPerm (suc n)
    sperm-add-elem (l , swaps) = l , swap-skip ∘ swaps

    append-sperm' : {n l1 l2 : Nat} -> SwapPerm' n l1 -> SwapPerm' n l2 -> SwapPerm' n (l1 +' l2)
    append-sperm' {l1 = zero}   sw1 sw2 = sw2
    append-sperm' {l1 = suc l1} sw1 sw2 = fin-rec (sw1 zero-fin) (append-sperm' (sw1 ∘ suc-fin) sw2)

    append-sperm : {n : Nat} -> SwapPerm n -> SwapPerm n -> SwapPerm n
    append-sperm (l1 , sw1) (l2 , sw2) = l1 +' l2 , append-sperm' sw1 sw2

    encode-sperm'-append : {n : Nat} -> (l1 : Nat) -> (p1 : SwapPerm' n l1) -> (p2 : SwapPerm n)
                           -> encode-sperm (append-sperm (l1 , p1) p2)
                              == encode-sperm (l1 , p1) ∘ encode-sperm p2
    encode-sperm'-append     0       _  fp2 = refl
    encode-sperm'-append {n} (suc i) p1 fp2@(j , p2) = path1 >=> path2
      where
      fp1 : SwapPerm n
      fp1 = (suc i) , p1
      p1' = p1 ∘ suc-fin
      fp1' : SwapPerm n
      fp1' = i , p1'
      sw = (p1 zero-fin)

      rec : encode-sperm (append-sperm fp1' fp2) == encode-sperm fp1' ∘ encode-sperm fp2
      rec = encode-sperm'-append i p1' fp2

      path1 : encode-sperm (append-sperm fp1 fp2)
              == (encode-swap sw) ∘ (encode-sperm (append-sperm fp1' fp2))
      path1 k = encode-swap sw ∘
               encode-sperm (_ , fin-rec-suc sw (append-sperm' p1' p2) k)

      path2 : encode-swap sw ∘ (encode-sperm (append-sperm fp1' fp2))
              == encode-swap sw ∘ (encode-sperm fp1' ∘ encode-sperm fp2)
      path2 = cong (encode-swap (p1 zero-fin) ∘_) rec

    encode-sperm-append : {n : Nat} -> (p1 p2 : SwapPerm n)
                          -> encode-sperm (append-sperm p1 p2)
                             == encode-sperm p1 ∘ encode-sperm p2
    encode-sperm-append (l , p1) p2 = encode-sperm'-append l p1 p2

    encode-swap-swap-skip-zero : {n : Nat} -> (sw : Swap n)
                                 -> encode-swap (swap-skip sw) zero-fin
                                    == zero-fin
    encode-swap-swap-skip-zero sw = refl


    encode-swap-swap-skip-suc : {n : Nat} -> (sw : Swap n) -> (i : (Fin n))
                                -> encode-swap (swap-skip sw) (suc-fin i)
                                   == fin-rec zero-fin (suc-fin ∘ encode-swap sw) (suc-fin i)
    encode-swap-swap-skip-suc sw i =
      cong (\x -> suc-fin (encode-swap sw x)) (ΣProp-path isProp≤ refl)
      >=> sym (fin-rec-suc-point zero-fin (suc-fin ∘ encode-swap sw) i)

    encode-swap-swap-skip' : {n : Nat} -> (sw : Swap n) -> (i : Fin (suc n))
                            -> encode-swap (swap-skip sw) i
                               == (fin-rec zero-fin (suc-fin ∘ encode-swap sw)) i
    encode-swap-swap-skip' sw =
      fin-elim (encode-swap-swap-skip-zero sw)
               (encode-swap-swap-skip-suc sw)

  encode-swap-swap-skip : {n : Nat} -> (sw : Swap n)
                          -> encode-swap (swap-skip sw)
                             == (fin-rec zero-fin (suc-fin ∘ encode-swap sw))
  encode-swap-swap-skip sw = funExt (encode-swap-swap-skip' sw)

  private

    fin-rec-skip-zero : {n : Nat} (f g : (Fin n -> Fin n))
                        -> fin-rec zero-fin (suc-fin ∘ f) (fin-rec zero-fin (suc-fin ∘ g) zero-fin)
                           == (fin-rec zero-fin (suc-fin ∘ f ∘ g) zero-fin)
    fin-rec-skip-zero f g = refl

    fin-rec-skip-suc : {n : Nat} (f g : (Fin n -> Fin n)) -> (i : Fin n)
                       -> fin-rec zero-fin (suc-fin ∘ f) (fin-rec zero-fin (suc-fin ∘ g) (suc-fin i))
                          == (fin-rec zero-fin (suc-fin ∘ f ∘ g) (suc-fin i))
    fin-rec-skip-suc f g i =
      begin
        fin-rec zero-fin (suc-fin ∘ f) (fin-rec zero-fin (suc-fin ∘ g) (suc-fin i))
      ==< cong (fin-rec zero-fin (suc-fin ∘ f)) (fin-rec-suc-point zero-fin (suc-fin ∘ g) i) >
        fin-rec zero-fin (suc-fin ∘ f) (suc-fin (g i))
      ==< fin-rec-suc-point zero-fin (suc-fin ∘ f) (g i) >
        (suc-fin (f (g i)))
      ==< sym (fin-rec-suc-point zero-fin (suc-fin ∘ f ∘ g) i) >
        (fin-rec zero-fin (suc-fin ∘ f ∘ g) (suc-fin i))
      end

    fin-rec-skip' : {n : Nat} (f g : (Fin n -> Fin n)) -> (i : Fin (suc n))
                   -> fin-rec zero-fin (suc-fin ∘ f) (fin-rec zero-fin (suc-fin ∘ g) i)
                      == fin-rec zero-fin (suc-fin ∘ f ∘ g) i
    fin-rec-skip' f g = fin-elim (fin-rec-skip-zero f g) (fin-rec-skip-suc f g)

    fin-rec-skip : {n : Nat} (f g : (Fin n -> Fin n))
                   -> (fin-rec zero-fin (suc-fin ∘ f)) ∘ (fin-rec zero-fin (suc-fin ∘ g))
                      == (fin-rec zero-fin (suc-fin ∘ f ∘ g))
    fin-rec-skip f g = funExt (fin-rec-skip' f g)

    encode-sperm'-swap-skip : {n : Nat} -> (l : Nat) -> (sp : SwapPerm' n l)
                            -> encode-sperm' l (swap-skip ∘ sp)
                               == (fin-rec zero-fin (suc-fin ∘ encode-sperm' l sp))
    encode-sperm'-swap-skip {n} zero sp = sym (funExt path)
      where
      path : (i : Fin (suc n)) -> (fin-rec zero-fin suc-fin i) == i
      path (0       , lt) = ΣProp-path isProp≤ refl
      path ((suc i) , lt) = ΣProp-path isProp≤ refl
    encode-sperm'-swap-skip (suc l) sp = ans
      where
      rec : encode-sperm' l (swap-skip ∘ sp ∘ suc-fin)
            == (fin-rec zero-fin (suc-fin ∘ encode-sperm' l (sp ∘ suc-fin)))
      rec = encode-sperm'-swap-skip l (sp ∘ suc-fin)

      ans : encode-sperm' (suc l) (swap-skip ∘ sp)
            == (fin-rec zero-fin (suc-fin ∘ encode-sperm' (suc l) sp))
      ans =
        begin
          encode-sperm' (suc l) (swap-skip ∘ sp)
        ==<>
          encode-swap (swap-skip (sp zero-fin)) ∘ encode-sperm' l (swap-skip ∘ sp ∘ suc-fin)
        ==< (\k -> encode-swap-swap-skip (sp zero-fin) k ∘ rec k) >
          (fin-rec zero-fin (suc-fin ∘ encode-swap (sp zero-fin)))
          ∘ (fin-rec zero-fin (suc-fin ∘ encode-sperm' l (sp ∘ suc-fin)))
        ==< fin-rec-skip (encode-swap (sp zero-fin)) (encode-sperm' l (sp ∘ suc-fin)) >
          fin-rec zero-fin (suc-fin ∘ (encode-swap (sp zero-fin) ∘ encode-sperm' l (sp ∘ suc-fin)))
        ==<>
          fin-rec zero-fin (suc-fin ∘ encode-sperm' (suc l) sp)
        end

    encode-sperm-add-elem : {n : Nat} -> (p : SwapPerm n)
                            -> encode-sperm (sperm-add-elem p)
                               == fin-rec zero-fin (suc-fin ∘ encode-sperm p)
    encode-sperm-add-elem (l , p) = encode-sperm'-swap-skip l p

    encode-single-swap' : {n : Nat} -> (x : Fin (suc (suc n)))
                          -> encode-sperm (single-sperm swap) x
                             == fin-rec one-fin (fin-rec zero-fin (\x -> suc-fin (suc-fin x))) x
    encode-single-swap' (zero          , lt) = ΣProp-path isProp≤ refl
    encode-single-swap' ((suc zero)    , lt) = ΣProp-path isProp≤ refl
    encode-single-swap' ((suc (suc _)) , lt) = ΣProp-path isProp≤ refl

    encode-single-swap :
      {n : Nat} -> Path (Fin (suc (suc n)) -> Fin (suc (suc n)))
                        (encode-sperm (single-sperm swap))
                        (fin-rec one-fin (fin-rec zero-fin (\x -> suc-fin (suc-fin x))))
    encode-single-swap = funExt encode-single-swap'

    swap-tree->sperm : {n : Nat} -> SwapTree n -> SwapPerm n
    swap-tree->sperm id-swap-tree = empty-sperm
    swap-tree->sperm swap-swap-tree = single-sperm swap
    swap-tree->sperm (compose-swap-tree st1 st2) =
      append-sperm (swap-tree->sperm st1) (swap-tree->sperm st2)
    swap-tree->sperm (ignore-swap-tree st) = sperm-add-elem (swap-tree->sperm st)

    swap-tree-sperm-path : {n : Nat} -> (s : SwapTree n)
                           -> (encode-sperm (swap-tree->sperm s)) == (encode-swap-tree s)
    swap-tree-sperm-path id-swap-tree = refl
    swap-tree-sperm-path (compose-swap-tree st1 st2) =
      encode-sperm-append (swap-tree->sperm st1) (swap-tree->sperm st2)
      >=> cong2 (\x y -> x ∘ y) (swap-tree-sperm-path st1) (swap-tree-sperm-path st2)
    swap-tree-sperm-path (ignore-swap-tree st) =
      encode-sperm-add-elem (swap-tree->sperm st)
      >=> (cong (\x -> fin-rec zero-fin (suc-fin ∘ x)) (swap-tree-sperm-path st))
    swap-tree-sperm-path swap-swap-tree = encode-single-swap

  fininj-sperm-path : {n : Nat} -> (f : Σ (Fin n -> Fin n) Injective)
                     -> Σ[ s ∈ SwapPerm n ] (encode-sperm s == fst f)
  fininj-sperm-path f =
    (swap-tree->sperm (iperm->swap-tree (decode-iperm f))) ,
    swap-tree-sperm-path (iperm->swap-tree (decode-iperm f))
    >=> iperm-swap-tree-path (decode-iperm f)
    >=> encode'-decode-iperm f
