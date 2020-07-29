{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import relation

module list.sorted {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} (_≤_ : Rel A ℓ₂)  where

open import equality
open import functions
open import hlevel
open import list hiding (insert)
open import list.unordered
open import sum

Sorted : Pred (List A) (ℓ-max ℓ₁ ℓ₂)
Sorted [] = Lift (ℓ-max ℓ₁ ℓ₂) Top
Sorted (a :: as) = ContainsOnly (a ≤_) as × Sorted as

sorted-[] : Sorted []
sorted-[] = lift tt

sorted-singleton : (a : A) -> Sorted [ a ]
sorted-singleton a = (\()) , sorted-[]

module algo (trans≤ : Transitive _≤_) (connex≤ : Connex _≤_) where

  private
    sorted-cons : (a1 a2 : A) -> (as : List A) -> (a1 ≤ a2) -> (Sorted (a2 :: as))
                  -> Sorted (a1 :: a2 :: as)
    sorted-cons a1 a2 as lt (co-a2 , s-as) = co-a1 , co-a2 , s-as
      where
      co-a1 : ContainsOnly (a1 ≤_) (a2 :: as)
      co-a1 {b} (zero  , path) = transport (\i -> a1 ≤ ( path (~ i))) lt
      co-a1 {b} (suc n , path) = trans≤ lt (co-a2 (n , path))

  insert : (a : A) -> List A -> List A
  insert-⊎ : {a a2 : A} -> (a ≤ a2 ⊎ a2 ≤ a) -> List A -> List A
  insert a [] = [ a ]
  insert a (a2 :: as) = insert-⊎ (connex≤ a a2) as
  insert-⊎ {a} {a2} (inj-l a≤a2) as = a :: a2 :: as
  insert-⊎ {a} {a2} (inj-r a2≤a) as = a2 :: (insert a as)

  insert-⊎-left : {a a2 : A} {s : (a ≤ a2 ⊎ a2 ≤ a)}
                  -> Left s
                  -> (as : List A)
                  -> insert-⊎ s as == a :: a2 :: as
  insert-⊎-left {s = inj-l _} _ as = refl

  insert-⊎-right : {a a2 : A} {s : (a ≤ a2 ⊎ a2 ≤ a)}
                   -> Right s
                   -> (as : List A)
                   -> insert-⊎ s as == a2 :: (insert a as)
  insert-⊎-right {s = inj-r _} _ as = refl


  insert-connex-left : (a a2 : A) (as : List A) -> (Left (connex≤ a a2))
                       -> insert a (a2 :: as) == a :: a2 :: as
  insert-connex-left a1 a2 as l = insert-⊎-left l as

  insert-connex-right : (a a2 : A) (as : List A) -> (Right (connex≤ a a2))
                        -> insert a (a2 :: as) == a2 :: (insert a as)
  insert-connex-right a1 a2 as l = insert-⊎-right l as



  insert-permutation : (a : A) -> (as : List A) -> Permutation A (insert a as) (a :: as)
  insert-permutation a [] = permutation-same [ a ]
  insert-permutation a (a2 :: as) with (connex≤ a a2)
  ... | (inj-l a≤a2) = permutation-same (a :: a2 :: as)
  ... | (inj-r a2≤a) =
    permutation-compose
      (permutation-cons a2 (insert-permutation a as))
      (permutation-swap a2 a as)


  insert-sorted : (a : A) -> {as : List A} -> (Sorted as) -> (Sorted (insert a as))
  insert-sorted a {[]}       _    = sorted-singleton a
  insert-sorted a {a2 :: as} (co-a2-as , s-as) with (connex≤ a a2)
  ... | (inj-l a≤a2) = sorted-cons a a2 as a≤a2 (co-a2-as , s-as)
  ... | (inj-r a2≤a) = (co-a2 , (insert-sorted a s-as))
    where
    co-a2' : ContainsOnly (a2 ≤_) (a :: as)
    co-a2' (zero  , path) = transport (\i -> a2 ≤ (path (~ i))) a2≤a
    co-a2' (suc n , path) = co-a2-as (n , path)

    co-a2 : ContainsOnly (a2 ≤_) (insert a as)
    co-a2 = co-a2' ∘ (permutation-contains (insert-permutation a as))

  sort : List A -> List A
  sort []        = []
  sort (a :: as) = (insert a (sort as))

  sort-permutation : (as : List A) -> (Permutation A (sort as) as)
  sort-permutation [] = permutation-empty
  sort-permutation (a :: as) =
    permutation-compose
      (insert-permutation a (sort as))
      (permutation-cons a (sort-permutation as))

  sort-sorted : (as : List A) -> (Sorted (sort as))
  sort-sorted [] = sorted-[]
  sort-sorted (a :: as) = (insert-sorted a (sort-sorted as))

  module order (antisym≤ : Antisymmetric _≤_) where
    sorted-≤list-:: : {a1 a2 : A} {as : List A}
                      -> a1 ≤ a2
                      -> Sorted (a2 :: as)
                      -> ContainsOnly (a1 ≤_) (a2 :: as)
    sorted-≤list-:: {a1 = a1} lt _       (0     , p) = transport (\i -> a1 ≤ (p (~ i))) lt
    sorted-≤list-::           lt (f , s) (suc n , p) = trans≤ lt (f (n , p))


    insert-list≤->== : {a : A} {as : List A} -> ContainsOnly (a ≤_) as -> insert a as == a :: as
    insert-list≤->== {a} {[]} f = refl
    insert-list≤->== {a} {a2 :: as} f = handle (connex≤ a a2) refl
      where
      handle : (x : (a ≤ a2 ⊎ a2 ≤ a)) -> x == (connex≤ a a2)
               -> insert a (a2 :: as) == a :: a2 :: as
      handle (inj-l _) p = insert-connex-left a a2 as (transport (\i -> Left (p i)) tt)
      handle (inj-r a2≤a) p =
        insert-connex-right a a2 as (transport (\i -> Right (p i)) tt)
        >=> rec-path >=> flip-as
        where
        a==a2 : a == a2
        a==a2 = antisym≤ (f (0 , refl)) a2≤a

        f' : ContainsOnly (a ≤_) as
        f' = f ∘ (cons-contains a2)

        rec-path : a2 :: (insert a as) == a2 :: a :: as
        rec-path = cong (a2 ::_) (insert-list≤->== f')

        flip-as : a2 :: a :: as == a :: a2 :: as
        flip-as i = (a==a2 (~ i)) :: (a==a2 i) :: as

    sorted-== : {as : List A} -> Sorted as -> sort as == as
    sorted-== {[]}      _      = refl
    sorted-== {a :: as} (c , s) =
      begin
        insert a (sort as)
      ==< cong (insert a) (sorted-== s) >
        insert a as
      ==< insert-list≤->== c >
        a :: as
      end




    double-insert-path : (a1 a2 : A) -> (as : List A)
                         -> insert a1 (insert a2 as) == (insert a2 (insert a1 as))

    triple-insert-path : (a1 a2 a3 : A) -> (as : List A) -> a1 ≤ a2
                         -> insert a1 (insert a2 (a3 :: as)) == (insert a2 (insert a1 (a3 :: as)))
    triple-insert-path a1 a2 a3 as a1≤a2 =
      handle (connex≤ a2 a3) refl (connex≤ a1 a3) refl (connex≤ a1 a2) refl (connex≤ a2 a1) refl
      where
      handle : (x : (a2 ≤ a3 ⊎ a3 ≤ a2)) -> x == (connex≤ a2 a3) ->
               (y : (a1 ≤ a3 ⊎ a3 ≤ a1)) -> y == (connex≤ a1 a3) ->
               (z : (a1 ≤ a2 ⊎ a2 ≤ a1)) -> z == (connex≤ a1 a2) ->
               (z2 : (a2 ≤ a1 ⊎ a1 ≤ a2)) -> z2 == (connex≤ a2 a1) ->
               insert a1 (insert a2 (a3 :: as)) == insert a2 (insert a1 (a3 :: as))
      handle _ _ _ _ (inj-r a2≤a1) _ _ _ =
        \i -> insert (p i) (insert (p (~ i)) (a3 :: as))
        where
        p : a1 == a2
        p = antisym≤ a1≤a2 a2≤a1
      handle _ _ _ _ (inj-l _) _ (inj-l a2≤a1) _ =
        \i -> insert (p i) (insert (p (~ i)) (a3 :: as))
        where
        p : a1 == a2
        p = antisym≤ a1≤a2 a2≤a1

      handle (inj-l a2≤a3) p23 (inj-l a1≤a3) p13 (inj-l _) p12 (inj-r _) p21 =
        begin
          insert a1 (insert a2 (a3 :: as))
        ==< (cong (insert a1) (insert-connex-left a2 a3 as (transport (\i -> Left (p23 i)) tt))) >
          insert a1 (a2 :: a3 :: as)
        ==< (insert-connex-left a1 a2 (a3 :: as) (transport (\i -> Left (p12 i)) tt)) >
          a1 :: a2 :: a3 :: as
        ==< (cong (a1 ::_) (sym (insert-connex-left a2 a3 as (transport (\i -> Left (p23 i)) tt)))) >
          a1 :: (insert a2 (a3 :: as))
        ==< (sym (insert-connex-right a2 a1 (a3 :: as) (transport (\i -> Right (p21 i)) tt))) >
          insert a2 (a1 :: a3 :: as)
        ==< (cong (insert a2) (sym (insert-connex-left a1 a3 as (transport (\i -> Left (p13 i)) tt)))) >
          insert a2 (insert a1 (a3 :: as))
        end

      handle (inj-l a2≤a3) _ (inj-r a3≤a1) _ (inj-l _) _ (inj-r _) _ =
        \i -> insert (p i) (insert (p (~ i)) (a3 :: as))
        where
        p : a1 == a2
        p = antisym≤ a1≤a2 (trans≤ a2≤a3 a3≤a1)
      handle (inj-r a3≤a2) p23 (inj-l a1≤a3) p13 (inj-l _) p12 (inj-r _) p21 =
        begin
          insert a1 (insert a2 (a3 :: as))
        ==< (cong (insert a1) (insert-connex-right a2 a3 as (transport (\i -> Right (p23 i)) tt))) >
          insert a1 (a3 :: (insert a2 as))
        ==< (insert-connex-left a1 a3 (insert a2 as) (transport (\i -> Left (p13 i)) tt)) >
          a1 :: a3 :: (insert a2 as)
        ==< cong (a1 ::_) (sym (insert-connex-right a2 a3 as (transport (\i -> Right (p23 i)) tt))) >
          a1 :: insert a2 (a3 :: as)
        ==< (sym (insert-connex-right a2 a1 (a3 :: as) (transport (\i -> Right (p21 i)) tt))) >
          insert a2 (a1 :: a3 :: as)
        ==< cong (insert a2) (sym (insert-connex-left a1 a3 as (transport (\i -> Left (p13 i)) tt))) >
          insert a2 (insert a1 (a3 :: as))
        end
      handle (inj-r a3≤a2) p23 (inj-r a3≤a1) p13 (inj-l _) p12 (inj-r _) p21 =
        begin
          insert a1 (insert a2 (a3 :: as))
        ==< (cong (insert a1) (insert-connex-right a2 a3 as (transport (\i -> Right (p23 i)) tt))) >
          insert a1 (a3 :: (insert a2 as))
        ==< (insert-connex-right a1 a3 (insert a2 as) (transport (\i -> Right (p13 i)) tt)) >
          a3 :: (insert a1 (insert a2 as))
        ==< cong (a3 ::_) (double-insert-path a1 a2 as) >
          a3 :: (insert a2 (insert a1 as))
        ==< sym (insert-connex-right a2 a3 (insert a1 as) (transport (\i -> Right (p23 i)) tt)) >
          insert a2 (a3 :: (insert a1 as))
        ==< cong (insert a2) (sym (insert-connex-right a1 a3 as (transport (\i -> Right (p13 i)) tt))) >
          insert a2 (insert a1 (a3 :: as))
        end

    double-insert-path a1 a2 [] = handle (connex≤ a1 a2) refl (connex≤ a2 a1) refl
      where
      handle : (x : (a1 ≤ a2 ⊎ a2 ≤ a1)) -> x == (connex≤ a1 a2) ->
               (y : (a2 ≤ a1 ⊎ a1 ≤ a2)) -> y == (connex≤ a2 a1) ->
               insert a1 (insert a2 []) == insert a2 (insert a1 [])
      handle (inj-l a1≤a2) _ (inj-l a2≤a1) _ = \i -> insert (p i) (insert (p (~ i)) [])
        where
        p : a1 == a2
        p = antisym≤ a1≤a2 a2≤a1
      handle (inj-r a2≤a1) _ (inj-r a1≤a2) _ = \i -> insert (p i) (insert (p (~ i)) [])
        where
        p : a1 == a2
        p = antisym≤ a1≤a2 a2≤a1
      handle (inj-l a1≤a2) p1 (inj-r a1≤a2') p2 =
        insert-connex-left a1 a2 [] (transport (\i -> Left (p1 i)) tt)
        >=> sym (insert-connex-right a2 a1 [] (transport (\i -> Right (p2 i)) tt))
      handle (inj-r a2≤a1) p1 (inj-l a2≤a1') p2 =
        insert-connex-right a1 a2 [] (transport (\i -> Right (p1 i)) tt)
        >=> sym (insert-connex-left a2 a1 [] (transport (\i -> Left (p2 i)) tt))

    double-insert-path a1 a2 (a3 :: as) = handle (connex≤ a1 a2)
      where
      handle : (a1 ≤ a2 ⊎ a2 ≤ a1) ->
               insert a1 (insert a2 (a3 :: as)) == insert a2 (insert a1 (a3 :: as))
      handle (inj-l a1≤a2) = triple-insert-path a1 a2 a3 as a1≤a2
      handle (inj-r a2≤a1) = sym (triple-insert-path a2 a1 a3 as a2≤a1)

    private
      isSetListA : isSet (List A)
      isSetListA = Discrete->isSet discreteList
        where
        open import list.discrete

        discA : Discrete A
        discA a1 a2 = handle (connex≤ a1 a2) refl (connex≤ a2 a1) refl
          where
          handle : (x : (a1 ≤ a2 ⊎ a2 ≤ a1)) -> x == (connex≤ a1 a2) ->
                   (y : (a2 ≤ a1 ⊎ a1 ≤ a2)) -> y == (connex≤ a2 a1) ->
                   Dec (a1 == a2)
          handle (inj-l a1≤a2) _ (inj-l a2≤a1) _ = yes (antisym≤ a1≤a2 a2≤a1)
          handle (inj-r a2≤a1) _ (inj-r a1≤a2) _ = yes (antisym≤ a1≤a2 a2≤a1)
          handle x@(inj-l _)   p12 y@(inj-r _)   p21 = no a1!=a2
            where
            a1!=a2 : ¬ (a1 == a2)
            a1!=a2 ap = transport (l-pathx >=> l-path >=> sym (l-pathy)) tt
              where
              c-path : PathP (\i -> ((ap i) ≤ (ap (~ i)) ⊎ (ap (~ i)) ≤ (ap i)))
                             (connex≤ a1 a2) (connex≤ a2 a1)
              c-path i = connex≤ (ap i) (ap (~ i))

              l-path : (Left (connex≤ a1 a2)) == (Left (connex≤ a2 a1))
              l-path i = Left (c-path i)

              l-pathx : (Left x) == (Left (connex≤ a1 a2))
              l-pathx = cong Left p12
              l-pathy : (Left y) == (Left (connex≤ a2 a1))
              l-pathy = cong Left p21

          handle x@(inj-r _)   p12 y@(inj-l _)   p21 = no a1!=a2
            where
            a1!=a2 : ¬ (a1 == a2)
            a1!=a2 ap = transport (r-pathx >=> r-path >=> sym (r-pathy)) tt
              where
              c-path : PathP (\i -> ((ap i) ≤ (ap (~ i)) ⊎ (ap (~ i)) ≤ (ap i)))
                             (connex≤ a1 a2) (connex≤ a2 a1)
              c-path i = connex≤ (ap i) (ap (~ i))

              r-path : (Right (connex≤ a1 a2)) == (Right (connex≤ a2 a1))
              r-path i = Right (c-path i)

              r-pathx : (Right x) == (Right (connex≤ a1 a2))
              r-pathx = cong Right p12
              r-pathy : (Right y) == (Right (connex≤ a2 a1))
              r-pathy = cong Right p21

        instance
          disc'A : Discrete' A
          disc'A = record { f = discA }


    import unordered-list as ul
    order : ul.UList A -> List A
    order = ul.UListElim.rec isSetListA [] insert double-insert-path


    order-path : (a : A) (as : ul.UList A) -> order (a ul.:: as) == insert a (order as)
    order-path a as = refl

    order-unorder-== : (as : List A) -> (order (unorder as)) == sort as
    order-unorder-== [] = refl
    order-unorder-== (a :: as) = cong (insert a) (order-unorder-== as)

    unorder-order-== : (as : ul.UList A) -> (unorder (order as)) == as
    unorder-order-== = ul.UListElim.prop (ul.trunc _ _) refl ::*
      where
      ::* : (a : A) {as : ul.UList A}
            -> (unorder (order as)) == as
            -> (unorder (order (a ul.:: as))) == a ul.:: as
      ::* a {as} p =
        (unorder-permutation (insert-permutation a (order as)))
        >=> cong (a ul.::_) p
