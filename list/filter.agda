{-# OPTIONS --cubical --safe --exact-split #-}

module list.filter where

open import base
open import relation
open import equality
open import functions
open import list
open import monoid
open import nat

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {ℓ : Level} {P : A -> Type ℓ} (f : (a : A) -> Dec (P a)) where

  private
    split-rec : (a : A) -> List A × List A -> List A × List A
    split-rec a (as1 , as2) = handle (f a)
      where
      handle : Dec (P a) -> List A × List A
      handle (yes _) = a :: as1 , as2
      handle (no  _) = as1 , a :: as2

  split : List A -> (List A × List A)
  split [] = [] , []
  split (a :: as) = split-rec a (split as)

  private
    split-rec-fst-keeps : {a : A} (s : List A × List A) (p : P a)
                      -> fst (split-rec a s) == a :: (fst s)
    split-rec-fst-keeps {a} as p with (f a)
    ... | yes _ = refl
    ... | no ¬p = bot-elim (¬p p)

    split-rec-fst-drops : {a : A} (s : List A × List A) (p : ¬(P a))
                      -> fst (split-rec a s) == (fst s)
    split-rec-fst-drops {a} as ¬p with (f a)
    ... | yes p = bot-elim (¬p p)
    ... | no  _ = refl

    split-rec-snd-keeps : {a : A} (s : List A × List A) (p : ¬(P a))
                      -> snd (split-rec a s) == a :: (snd s)
    split-rec-snd-keeps {a} as ¬p with (f a)
    ... | yes p = bot-elim (¬p p)
    ... | no  _ = refl

    split-rec-snd-drops : {a : A} (s : List A × List A) (p : P a)
                      -> snd (split-rec a s) == (snd s)
    split-rec-snd-drops {a} as p with (f a)
    ... | yes _ = refl
    ... | no ¬p = bot-elim (¬p p)

  split-fst-keeps : {a : A} (as : List A) (p : P a) -> fst (split (a :: as)) == a :: (fst (split as))
  split-fst-keeps as p = split-rec-fst-keeps (split as) p

  split-fst-drops : {a : A} (as : List A) (p : ¬(P a)) -> fst (split (a :: as)) == (fst (split as))
  split-fst-drops as p = split-rec-fst-drops (split as) p

  split-snd-keeps : {a : A} (as : List A) (p : ¬(P a)) -> snd (split (a :: as)) == a :: (snd (split as))
  split-snd-keeps as p = split-rec-snd-keeps (split as) p

  split-snd-drops : {a : A} (as : List A) (p : P a) -> snd (split (a :: as)) == (snd (split as))
  split-snd-drops as p = split-rec-snd-drops (split as) p


  filter : List A -> List A
  filter as = fst (split as)

  filter-keeps : {a : A} (as : List A) (p : P a) -> filter (a :: as) == a :: filter as
  filter-keeps as p = split-fst-keeps as p

  filter-drops : {a : A} (as : List A) (p : ¬(P a)) -> filter (a :: as) == filter as
  filter-drops as p = split-fst-drops as p

--  filter-keeps-single : {a : A} (p : P a) -> filter [ a ] == [ a ]
--  filter-keeps-single = filter-keeps []
--
--  filter-drops-single : {a : A} (p : (¬ (P a)) -> filter [ a ] == [ a ]
--  filter-drops-single = filter-keeps []


  filter' : List A -> List A
  filter' as = snd (split as)

  filter'-keeps : {a : A} (as : List A) (p : ¬(P a)) -> filter' (a :: as) == a :: filter' as
  filter'-keeps as p = split-snd-keeps as p

  filter'-drops : {a : A} (as : List A) (p : P a) -> filter' (a :: as) == filter' as
  filter'-drops as p = split-snd-drops as p

  filter-++ : (as1 as2 : List A) -> filter (as1 ++ as2) == filter as1 ++ filter as2
  filter-++ []         as2 = refl
  filter-++ (a :: as1) as2 = handle (f a)
    where
    handle : (Dec (P a)) -> filter (a :: as1 ++ as2) == filter (a :: as1) ++ filter as2
    handle (yes p) =
      filter-keeps (as1 ++ as2) p
      >=> (\i -> a :: (filter-++ as1 as2 i))
      >=> (\i -> (filter-keeps as1 p (~ i)) ++ (filter as2))
    handle (no ¬p) =
      filter-drops (as1 ++ as2) ¬p
      >=> (filter-++ as1 as2)
      >=> (\i -> (filter-drops as1 ¬p (~ i)) ++ (filter as2))

  filter'-++ : (as1 as2 : List A) -> filter' (as1 ++ as2) == filter' as1 ++ filter' as2
  filter'-++ []         as2 = refl
  filter'-++ (a :: as1) as2 = handle (f a)
    where
    handle : (Dec (P a)) -> filter' (a :: as1 ++ as2) == filter' (a :: as1) ++ filter' as2
    handle (no ¬p) =
      filter'-keeps (as1 ++ as2) ¬p
      >=> (\i -> a :: (filter'-++ as1 as2 i))
      >=> (\i -> (filter'-keeps as1 ¬p (~ i)) ++ (filter' as2))
    handle (yes p) =
      filter'-drops (as1 ++ as2) p
      >=> (filter'-++ as1 as2)
      >=> (\i -> (filter'-drops as1 p (~ i)) ++ (filter' as2))

  filterʰ : Monoidʰ {D₁ = List A} filter
  filterʰ = record
    { preserves-ε = refl
    ; preserves-∙ = filter-++
    }

  filter'ʰ : Monoidʰ {D₁ = List A} filter'
  filter'ʰ = record
    { preserves-ε = refl
    ; preserves-∙ = filter'-++
    }

  private

    filter-contains-keep : {x : A} {a : A} (as : List A) -> P a ->
                            contains x (filter (a :: as)) -> contains x (a :: (filter as))
    filter-contains-keep {x} {a} as pa c =
      transport (\i -> contains x (filter-keeps as pa i)) c
    filter'-contains-keep : {x : A} {a : A} (as : List A) -> ¬(P a) ->
                            contains x (filter' (a :: as)) -> contains x (a :: (filter' as))
    filter'-contains-keep {x} {a} as pa c =
      transport (\i -> contains x (filter'-keeps as pa i)) c
    filter-contains-drop : {x : A} {a : A} (as : List A) -> ¬(P a) ->
                            contains x (filter (a :: as)) -> contains x (filter as)
    filter-contains-drop {x} {a} as pa c =
      transport (\i -> contains x (filter-drops as pa i)) c
    filter'-contains-drop : {x : A} {a : A} (as : List A) -> P a ->
                            contains x (filter' (a :: as)) -> contains x (filter'  as)
    filter'-contains-drop {x} {a} as pa c =
      transport (\i -> contains x (filter'-drops as pa i)) c

    filter-contains-cons : {x : A} {a : A} (as : List A) ->
                           contains x (filter (a :: as)) -> contains x (a :: (filter as))
    filter-contains-cons {x = x} {a = a} as c = handle (f a)
      where
      handle : Dec (P a) -> contains x (a :: filter as)
      handle (yes p) = filter-contains-keep as p c
      handle (no p) = cons-contains a (filter-contains-drop as p c)

    filter'-contains-cons : {x : A} {a : A} (as : List A) ->
                            contains x (filter' (a :: as)) -> contains x (a :: (filter' as))
    filter'-contains-cons {x = x} {a = a} as c = handle (f a)
      where
      handle : Dec (P a) -> contains x (a :: filter' as)
      handle (yes p) = cons-contains a (filter'-contains-drop as p c)
      handle (no p) = filter'-contains-keep as p c




  split-contains : {x : A} (as : List A) -> contains x as
                   -> (contains x (filter as)) ⊎ (contains x (filter' as))
  split-contains {x} (a :: as) (zero , path) = handle (f a)
    where
    handle : (Dec (P a)) -> (contains x (filter  (a :: as))) ⊎
                            (contains x (filter' (a :: as)))
    handle (yes p) = inj-l (transport (\i -> contains x (filter-keeps as p (~ i)))
                                      (0 , path))
    handle (no  p) = inj-r (transport (\i -> contains x (filter'-keeps as p (~ i)))
                                      (0 , path))
  split-contains {x} (a :: as) (suc n , path) = handle (f a) (split-contains as (n , path))
    where
    filter-contains-keep' : {x : A} {a : A} (as : List A) -> P a ->
                            contains x (filter as) -> contains x (filter (a :: as))
    filter-contains-keep' {x} {a} as pa c =
      transport (\i -> contains x (filter-keeps as pa (~ i))) (cons-contains a c)
    filter'-contains-keep' : {x : A} {a : A} (as : List A) -> ¬ (P a) ->
                            contains x (filter' as) -> contains x (filter' (a :: as))
    filter'-contains-keep' {x} {a} as pa c =
      transport (\i -> contains x (filter'-keeps as pa (~ i))) (cons-contains a c)
    filter-contains-drop' : {x : A} {a : A} (as : List A) -> ¬ (P a) ->
                            contains x (filter as) -> contains x (filter (a :: as))
    filter-contains-drop' {x} {a} as pa c =
      transport (\i -> contains x (filter-drops as pa (~ i))) c
    filter'-contains-drop' : {x : A} {a : A} (as : List A) -> P a ->
                            contains x (filter' as) -> contains x (filter' (a :: as))
    filter'-contains-drop' {x} {a} as pa c =
      transport (\i -> contains x (filter'-drops as pa (~ i))) c

    handle : Dec (P a)
             -> (contains x (filter as)) ⊎ (contains x (filter' as))
             -> (contains x (filter  (a :: as))) ⊎ (contains x (filter' (a :: as)))
    handle (yes p) (inj-l c) = inj-l (filter-contains-keep'  as p c)
    handle (yes p) (inj-r c) = inj-r (filter'-contains-drop' as p c)
    handle (no  p) (inj-l c) = inj-l (filter-contains-drop'  as p c)
    handle (no  p) (inj-r c) = inj-r (filter'-contains-keep' as p c)

  filter-contains : {x : A} (as : List A) -> (contains x (filter as)) -> contains x as
  filter-contains {x = x} (a :: as) c = handle (f a)
    where
    handle : Dec (P a) -> contains x (a :: as)
    handle (no ¬p) =
      cons-contains a (filter-contains as (filter-contains-drop as ¬p c))
    handle (yes p) = handle2 (filter-contains-keep as p c)
      where
      handle2 : contains x (a :: (filter as)) -> contains x (a :: as)
      handle2 (zero  , p) = (zero , p)
      handle2 (suc n , p) = cons-contains a (filter-contains as (n , p))


  filter-idempotent : (as : List A) -> filter (filter as) == filter as
  filter-idempotent [] = refl
  filter-idempotent (a :: as) = handle (f a) (filter-idempotent as)
    where
    handle : (Dec (P a))
             -> filter (filter as) == filter as
             -> filter (filter (a :: as)) == filter (a :: as)
    handle (yes p) path =
      cong filter (filter-keeps as p)
      >=> filter-keeps (filter as) p
      >=> cong (a ::_) path
      >=> sym (filter-keeps as p)
    handle (no ¬p) path =
      cong filter (filter-drops as ¬p)
      >=> path
      >=> sym (filter-drops as ¬p)

  filter'-idempotent : (as : List A) -> filter' (filter' as) == filter' as
  filter'-idempotent [] = refl
  filter'-idempotent (a :: as) = handle (f a) (filter'-idempotent as)
    where
    handle : (Dec (P a))
             -> filter' (filter' as) == filter' as
             -> filter' (filter' (a :: as)) == filter' (a :: as)
    handle (no ¬p) path =
      cong filter' (filter'-keeps as ¬p)
      >=> filter'-keeps (filter' as) ¬p
      >=> cong (a ::_) path
      >=> sym (filter'-keeps as ¬p)
    handle (yes p) path =
      cong filter' (filter'-drops as p)
      >=> path
      >=> sym (filter'-drops as p)

  filter-length≤ : (as : List A) -> length (filter as) ≤ length as
  filter-length≤ [] = zero-≤
  filter-length≤ (a :: as) = handle (f a) (filter-length≤ as)
    where
    handle : (Dec (P a))
             -> length (filter as) ≤ length as
             -> length (filter (a :: as)) ≤ length (a :: as)
    handle (yes p) (i , path) = (i , (\k -> i +' length (filter-keeps as p k))
                                     >=> +'-right-suc
                                     >=> cong suc path)
    handle (no ¬p) (i , path) = (suc i , (\k -> suc i +' length (filter-drops as ¬p k))
                                         >=> cong suc path)

  filter'-length≤ : (as : List A) -> length (filter' as) ≤ length as
  filter'-length≤ [] = zero-≤
  filter'-length≤ (a :: as) = handle (f a) (filter'-length≤ as)
    where
    handle : (Dec (P a))
             -> length (filter' as) ≤ length as
             -> length (filter' (a :: as)) ≤ length (a :: as)
    handle (no ¬p) (i , path) = (i , (\k -> i +' length (filter'-keeps as ¬p k))
                                     >=> +'-right-suc
                                     >=> cong suc path)
    handle (yes p) (i , path) = (suc i , (\k -> suc i +' length (filter'-drops as p k))
                                         >=> cong suc path)

  filter-contains-only : (as : List A) -> ContainsOnly P (filter as)
  filter-contains-only (a :: as) {a = x} c = handle (f a) (filter-contains-cons as c)
    where
    handle : (Dec (P a)) -> contains x (a :: (filter as)) -> P x
    handle (yes pa) (suc n , p) = filter-contains-only as (n , p)
    handle (yes pa) (zero , p) = transport (\i -> P (p (~ i))) pa
    handle (no ¬pa) _ = filter-contains-only as (filter-contains-drop as ¬pa c)


  filter'-contains-only : (as : List A) -> ContainsOnly (Comp P) (filter' as)
  filter'-contains-only (a :: as) {a = x} c = handle (f a) (filter'-contains-cons as c)
    where
    handle : (Dec (P a)) -> contains x (a :: (filter' as)) -> ¬ (P x)
    handle (no ¬pa) (suc n , p) = filter'-contains-only as (n , p)
    handle (no ¬pa) (zero , p) px = ¬pa (transport (\i -> P (p i)) px)
    handle (yes pa) _ = filter'-contains-only as (filter'-contains-drop as pa c)

  filter-contains-all : (as : List A)
                        -> ContainsAll P as
                        -> ContainsAll P (filter as)
  filter-contains-all as g {a = x} px = handle (split-contains as (g px))
    where
    handle : (contains x (filter as)) ⊎ (contains x (filter' as)) -> contains x (filter as)
    handle (inj-l in-f ) = in-f
    handle (inj-r in-f') = bot-elim (filter'-contains-only as in-f' px)

  filter-no-duplicates : (as : List A) -> NoDuplicates as -> NoDuplicates (filter as)
  filter-no-duplicates [] nd = nd
  filter-no-duplicates (a :: as) (¬c , nd) = handle (f a)
    where
    handle : Dec (P a) -> NoDuplicates (filter (a :: as))
    handle (yes p) = transport (\i -> NoDuplicates (filter-keeps as p (~ i)))
                               (¬c' , (filter-no-duplicates as nd))
      where
      ¬c' : ¬ (contains a (filter as))
      ¬c' c = ¬c (filter-contains as c)

    handle (no ¬p) = transport (\i -> NoDuplicates (filter-drops as ¬p (~ i)))
                               (filter-no-duplicates as nd)
