{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module unordered-list.count-extensionality {ℓ : Level} {A : Type ℓ} {{disc'A : Discrete' A}} where

open import equality
open import hlevel
open import nat
open import nat.order
open import order
open import order.instances.nat
open import unordered-list.base
open import unordered-list.operations
open import unordered-list.discrete


private
  discA = Discrete'.f disc'A

  _≼_ : UList A -> UList A -> Type _
  as ≼ bs = (x : A) -> (count x as) ≤ (count x bs)

  ≼[]->[] : (as : UList A) -> as ≼ [] -> as == []
  ≼[]->[] as f = all-count-zero->[] as (\ x -> antisym-≤ (f x) (zero-≤))
    where
    all-count-zero->[] : (as : UList A) -> ((x : A) -> count x as == 0) -> as == []
    all-count-zero->[] as = UListElim.prop PisProp (\_ -> refl) _::*_ as
      where
      P : (as : UList A) -> Type _
      P as = (((x : A) -> count x as == 0) -> as == [])

      PisProp : {as : UList A} -> isProp (P as)
      PisProp {as} = isPropΠ (\ _ -> (trunc _ _))

      _::*_ : (a : A) {as : UList A} (f : P as) -> P (a :: as)
      _::*_ a {as} _ f = bot-elim (zero-suc-absurd (sym zero-proof >=> suc-proof))
        where
        zero-proof : (count a (a :: as)) == 0
        zero-proof = f a
        suc-proof : (count a (a :: as)) == (suc (count a as))
        suc-proof = (count-== as refl)

  trans-≼ : {as bs cs : UList A} -> as ≼ bs -> bs ≼ cs -> as ≼ cs
  trans-≼ f g y = trans-≤ (f y) (g y)

  refl-≼ : {as : UList A} -> as ≼ as
  refl-≼ a = refl-≤

  remove1-≼ : {as bs : UList A} -> (b : A) -> as ≼ bs -> (remove1 b as) ≼ (remove1 b bs)
  remove1-≼ {as} {bs} b lt x with (discA x b)
  ... | (yes x==b) = transport (\i -> (remove1-count-pred as x==b (~ i)) ≤
                                      (remove1-count-pred bs x==b (~ i)))
                               (pred-≤ (lt x))
  ... | (no x!=b)  = transport (\i -> (remove1-count-ignore as x!=b (~ i)) ≤
                                      (remove1-count-ignore bs x!=b (~ i)))
                               (lt x)

  data StrongRec : UList A -> Type (levelOf A) where
    sr-empty : StrongRec []
    sr-cons : (a : A) -> {as : UList A} -> (∀ {bs} -> bs ≼ as -> StrongRec bs) -> StrongRec (a :: as)
    trunc : {as : UList A} -> isProp (StrongRec as)

  apply-strong-rec : {as bs : UList A} -> StrongRec as -> bs ≼ as -> StrongRec bs
  apply-strong-rec {bs = bs} sr-empty p =
    transport (\i -> StrongRec (≼[]->[] bs p (~ i))) sr-empty
  apply-strong-rec {as = x::as} {bs = bs} (sr-cons x {as} f) p = split (count x bs) refl
    where
    zero-case : (count x bs == 0) -> StrongRec bs
    zero-case count-zero = f bs≼as
      where
      bs≼as : bs ≼ as
      bs≼as y with (discA x y)
      ...        | (yes x==y) = transport (\i -> (count-zero-y (~ i) ≤ (count y as))) zero-≤
        where
        count-zero-y : (count y bs == 0)
        count-zero-y = transport (\ i -> (count (x==y i) bs) == 0) count-zero
      ...        | (no x!=y) = transport (\i -> count y bs ≤ (count-eq i)) (p y)
        where
        count-eq : (count y (x :: as)) == count y as
        count-eq = (count-!= as (\p -> x!=y (sym p)))


    non-zero-case : (n : Nat) -> (count x bs == (suc n)) -> StrongRec bs
    non-zero-case n count-n =
        transport (\i -> StrongRec (bs'-path i)) (sr-cons x f')
      where
      bs' : UList A
      bs' = remove1 x bs
      bs'-path : x :: bs' == bs
      bs'-path = remove1-count-suc count-n

      bs'≼as : bs' ≼ as
      bs'≼as y with (discA x y)
      ...         | (yes x==y) = proof-y
        where
        count-as-path : count x (x :: as) == suc (count x as)
        count-as-path = count-== as refl
        count-bs-path : count x bs == suc (count x bs')
        count-bs-path = (\i -> count x (bs'-path (~ i))) >=> count-== bs' refl
        proof : count x bs' ≤ count x as
        proof = pred-≤ (transport (\i -> (count-bs-path i) ≤ (count-as-path i)) (p x))
        proof-y : count y bs' ≤ count y as
        proof-y = transport (\i -> (count (x==y i) bs') ≤ count (x==y i) as) proof
      ...         | (no x!=y) = proof
        where
        count-as-path : (count y (x :: as)) == count y as
        count-as-path = (count-!= as (\p -> x!=y (sym p)))
        count-bs-path : (count y bs) == count y bs'
        count-bs-path =
          (\i -> count y (bs'-path (~ i))) >=>
          (count-!= bs' (\p -> x!=y (sym p)))
        proof : count y bs' ≤ count y as
        proof = transport (\i -> (count-bs-path i) ≤ (count-as-path i)) (p y)


      f' : ∀ {cs} -> cs ≼ bs' -> StrongRec cs
      f' {cs} cs≼bs' = f (trans-≼ {cs} {bs'} {as} cs≼bs' bs'≼as)

    split : (n : Nat) -> (count x bs == n) -> StrongRec bs
    split zero p = zero-case p
    split (suc n) p = non-zero-case n p
  apply-strong-rec (trunc p q i) lt =
    (trunc (apply-strong-rec p lt) (apply-strong-rec q lt) i)



  module PropElim≼ {B : UList A -> Type ℓ}
    (BProp : {as : UList A} -> isProp (B as))
    ([]* : B [])
    (::* : (a : A) {as : UList A}
           -> ({bs : UList A} -> (bs ≼ as) -> B bs)
           -> B (a :: as))
    where
    private
      build-rec : (as : UList A) -> StrongRec as
      build-rec as = UListElim.full (isProp->isSet StrongRec.trunc) []s _::s_ swap-s as
        where
        []s = sr-empty

        _::s_ : (a : A) {as : UList A} -> StrongRec as -> StrongRec (a :: as)
        a ::s rec = sr-cons a (apply-strong-rec rec)

        swap-s : (a1 a2 : A) -> {as : UList A} -> (sr : StrongRec as)
                 -> PathP (\i -> StrongRec (swap a1 a2 as i))
                          (a1 ::s (a2 ::s sr))
                          (a2 ::s (a1 ::s sr))
        swap-s a1 a2 sr = isProp->PathP (\i -> trunc)

      use-rec : {as : UList A} -> StrongRec as -> B as
      use-rec sr-empty      = []*
      use-rec (sr-cons a f) = (::* a (\x -> use-rec (f x)))
      use-rec (trunc p q i) = BProp (use-rec p) (use-rec q) i

    f : (as : UList A) -> B as
    f as = use-rec (build-rec as)

  -- Utility for helping prove as ≼ bs -> P as bs.

  module PropElim2≼ {P : UList A -> UList A -> Type ℓ}
    (PProp : (as : UList A) (bs : UList A) -> isProp (P as bs))
    ([]-left : (bs : UList A) -> P [] bs)
    (::-both : (a : A) (as : UList A) (bs : UList A)
               -> as ≼ bs
               -> ({cs : UList A} {ds : UList A}
                   -> (cs ≼ as)
                   -> (cs ≼ ds)
                   -> P cs ds)
               -> P (a :: as) (a :: bs))
    where

    InnerP : UList A -> Type _
    InnerP as = (bs : UList A) -> as ≼ bs -> P as bs

    InnerPisProp : {as : UList A} -> isProp (InnerP as)
    InnerPisProp {as} = isPropΠ2 (\ bs _ -> PProp as bs)

    f : (as : UList A) -> (bs : UList A) -> as ≼ bs -> P as bs
    f = PropElim≼.f InnerPisProp []* ::*
      where
      []* : InnerP []
      []* bs lt = []-left bs

      ::* : (a : A) {as : UList A}
            -> ({cs : UList A} -> (cs ≼ as) -> InnerP cs)
            -> InnerP (a :: as)
      ::* a {as} f bs a::as≼bs = proof
        where
        bs' : UList A
        bs' = remove1 a bs

        bs-count : suc (count a as) ≤' count a bs
        bs-count = (transport (path >=> ≤==≤') (a::as≼bs a))
          where
          path : (count a (a :: as) ≤ count a bs) == (suc (count a as) ≤ (count a bs))
          path i = (count-== {x = a} as refl i) ≤ count a bs

        bs-path : a :: bs' == bs
        bs-path = remove1-count-suc (sym (bs-count .snd))

        as-path : remove1 a (a :: as) == as
        as-path = remove1-== as refl

        lt-removed' : (remove1 a (a :: as)) ≼ bs'
        lt-removed' = remove1-≼ {a :: as} {bs} a a::as≼bs

        lt-removed : as ≼ bs'
        lt-removed = (transport (\i -> (as-path i) ≼ bs') lt-removed')

        g : {cs : UList A} {ds : UList A} -> cs ≼ as -> cs ≼ ds -> P cs ds
        g {cs} {ds} lt-as lt-ds = f lt-as ds lt-ds

        proof' : P (a :: as) (a :: bs')
        proof' = ::-both a as bs' lt-removed g

        proof : P (a :: as) bs
        proof = transport (\i -> P (a :: as) (bs-path i)) proof'


  Subset : (as bs : UList A) -> Type _
  Subset as bs = Σ[ x ∈ (UList A) ] (x ++ as) == bs

  ::-injective : (a : A) {xs ys : UList A} -> (a :: xs) == (a :: ys) -> xs == ys
  ::-injective a {xs} {ys} p = (sym (remove1-== xs refl)) >=>
                               (cong (remove1 a) p) >=>
                               (remove1-== ys refl)

  ++-injective : (as : UList A) {xs ys : UList A} -> (as ++ xs) == (as ++ ys) -> xs == ys
  ++-injective as {xs} {ys} p = UListElim.prop (\{as} -> PisProp {as}) []* _::*_ as p
    where
    P : UList A -> Type _
    P as = (as ++ xs) == (as ++ ys) -> xs == ys

    PisProp : {as : UList A} -> isProp (P as)
    PisProp = isPropΠ (\_ -> (trunc _ _))

    []* : P []
    []* p = p

    _::*_ : (a : A) {as : UList A} (f : P as) -> P (a :: as)
    (a ::* f) p = (f (::-injective a p))

  isPropSubset : {as bs : UList A} -> isProp (Subset as bs)
  isPropSubset {as} {bs} (x1 , p1) (x2 , p2) = (\ i -> (xp i , pp i))
    where
    xp : x1 == x2
    xp = ++-injective as (++-commute as x1 >=> p1 >=> sym p2 >=> ++-commute x2 as)
    pp : PathP _ p1 p2
    pp = isProp->PathP (\i -> (trunc _ _))


  subset-::-both : {as bs : UList A} -> (a : A) -> (Subset as bs) -> Subset (a :: as) (a :: bs)
  subset-::-both {as} {bs} b (x , pr) = (x , pr2)
    where
    pr2 : x ++ (b :: as) == b :: bs
    pr2 = ++-commute x (b :: as) >=> (cong (b UList.::_) (++-commute as x >=> pr))

  ≼->Subset : {as bs : UList A} -> as ≼ bs -> Subset as bs
  ≼->Subset {as} {bs} = PropElim2≼.f (\ _ _ -> isPropSubset) []* ::* as bs
    where

    []* : (bs : UList A) -> Subset [] bs
    []* bs = (bs , (++-right-[] bs))

    ::* : (a : A) (as : UList A) (bs : UList A)
          -> as ≼ bs
          -> ({cs : UList A} {ds : UList A}
              -> (cs ≼ as)
              -> (cs ≼ ds)
              -> Subset cs ds)
          -> Subset (a :: as) (a :: bs)
    ::* a as bs as≼bs f = subset-::-both a (f (refl-≼ {as}) as≼bs)

  antisym-Subset : {as bs : UList A} -> Subset as bs -> Subset bs as -> as == bs
  antisym-Subset {as} {bs} s1 s2 = transport (\ i -> (xs==[] i) ++ as == bs) xs-p
    where
      xs = fst s1
      ys = fst s2

      xs-p = snd s1
      ys-p = snd s2

      p : (xs ++ ys) ++ bs == bs
      p = ++-assoc xs ys bs >=> transport (\ i -> (xs ++ (ys-p (~ i)) == bs)) xs-p

      xs==[] : xs == []
      xs==[] = as++bs==[]->as==[] (++-left-id->[] p)

countExtUList : ∀ (as bs : UList A) -> (∀ a -> count a as == count a bs) -> as == bs
countExtUList as bs f = antisym-Subset (≼->Subset as≼bs) (≼->Subset bs≼as)
  where
  as≼bs : as ≼ bs
  as≼bs x = transport (\i -> count x as ≤ (f x i)) refl-≤
  bs≼as : bs ≼ as
  bs≼as x = transport (\i -> count x bs ≤ (f x (~ i))) refl-≤
