{-# OPTIONS --cubical --safe --exact-split #-}

open import base

module list.sorted {ℓ₁ ℓ₂ : Level} {A : Type ℓ₁} (_≤_ : Rel A ℓ₂)  where

open import decision
open import discrete
open import equality
open import functions
open import hlevel
open import list hiding (insert) renaming (Sorted to Sorted' ; SemiSorted to SemiSorted')
open import list.unordered
open import relation
open import sum
open import truncation

open EqReasoning

private
  Sorted = Sorted' _≤_
  SemiSorted = SemiSorted' _≤_


sorted-[] : Sorted []
sorted-[] = lift tt

sorted-singleton : (a : A) -> Sorted [ a ]
sorted-singleton a = (\()) , sorted-[]

semi-sorted-[] : SemiSorted []
semi-sorted-[] = lift tt

semi-sorted-singleton : (a : A) -> SemiSorted [ a ]
semi-sorted-singleton a = (\()) , semi-sorted-[]

module dec-algo (trans≤ : Transitive _≤_) (dec≤ : Decidable2 _≤_) where

  private
    sorted-cons : (a1 a2 : A) -> (as : List A) -> (a1 ≤ a2) -> (Sorted (a2 :: as))
                  -> Sorted (a1 :: a2 :: as)
    sorted-cons a1 a2 as lt (co-a2 , s-as) = co-a1 , co-a2 , s-as
      where
      co-a1 : ContainsOnly (a1 ≤_) (a2 :: as)
      co-a1 {b} (zero  , path) = transport (\i -> a1 ≤ ( path (~ i))) lt
      co-a1 {b} (suc n , path) = trans≤ lt (co-a2 (n , path))

    semi-sorted-cons≤ : (a1 a2 : A) -> (as : List A) -> (a1 ≤ a2) -> (SemiSorted (a2 :: as))
                       -> SemiSorted (a1 :: a2 :: as)
    semi-sorted-cons≤ a1 a2 as lt (co-a2 , s-as) = co-a1 , co-a2 , s-as
      where
      co-a1 : ContainsOnly ((a1 ≤_) ∪ (a1 ==_)) (a2 :: as)
      co-a1 {b} (zero  , path) = inj-l (transport (\i -> a1 ≤ ( path (~ i))) lt)
      co-a1 {b} (suc n , path) = handle (co-a2 (n , path))
        where
        handle : (a2 ≤ b) ⊎ (a2 == b) -> (a1 ≤ b) ⊎ (a1 == b)
        handle (inj-l a2≤b)  = inj-l (trans≤ lt a2≤b)
        handle (inj-r a2==b) = inj-l (transport (\i -> a1 ≤ (a2==b i)) lt)

    semi-sorted-cons== : (a1 a2 : A) -> (as : List A) -> (a1 == a2) -> (SemiSorted (a2 :: as))
                       -> SemiSorted (a1 :: a2 :: as)
    semi-sorted-cons== a1 a2 as a1==a2 (co-a2 , s-as) = co-a1 , co-a2 , s-as
      where
      co-a1 : ContainsOnly ((a1 ≤_) ∪ (a1 ==_)) (a2 :: as)
      co-a1 {b} (zero  , path) = inj-r (a1==a2 >=> sym path)
      co-a1 {b} (suc n , path) =
        transport (\i -> ((a1==a2 (~ i)) ≤ b) ⊎ ((a1==a2 (~ i)) == b)) (co-a2 (n , path))


  insert : (a : A) -> List A -> List A
  insert-dec : {a a2 : A} -> (Dec (a ≤ a2)) -> List A -> List A
  insert a [] = [ a ]
  insert a (a2 :: as) = insert-dec (dec≤ a a2) as
  insert-dec {a} {a2} (yes a≤a2) as = a :: a2 :: as
  insert-dec {a} {a2} (no a2≤a) as = a2 :: (insert a as)

  insert-dec-≤ : {a a2 : A} {as : List A} (d : Dec (a ≤ a2)) -> a ≤ a2
                 -> insert-dec d as == a :: a2 :: as
  insert-dec-≤ (yes _)  _  = refl
  insert-dec-≤ (no ¬lt) lt = bot-elim (¬lt lt)

  insert-dec-¬≤ : {a a2 : A} {as : List A} (d : Dec (a ≤ a2)) -> ¬(a ≤ a2)
                 -> insert-dec d as == a2 :: (insert a as)
  insert-dec-¬≤ (yes lt) ¬lt = bot-elim (¬lt lt)
  insert-dec-¬≤ (no _)   _   = refl

  insert-≤ : (a a2 : A) (as : List A) -> a ≤ a2 -> insert a (a2 :: as) == a :: a2 :: as
  insert-≤ a a2 as lt = insert-dec-≤ (dec≤ a a2) lt

  insert-¬≤ : (a a2 : A) (as : List A) -> ¬(a ≤ a2) -> insert a (a2 :: as) == a2 :: (insert a as)
  insert-¬≤ a a2 as ¬lt = insert-dec-¬≤ (dec≤ a a2) ¬lt



  insert-permutation : (a : A) -> (as : List A) -> Permutation A (insert a as) (a :: as)
  insert-permutation a [] = permutation-same [ a ]
  insert-permutation a (a2 :: as) with (dec≤ a a2)
  ... | (yes _) = permutation-same (a :: a2 :: as)
  ... | (no  _) =
    permutation-compose
      (permutation-cons a2 (insert-permutation a as))
      (permutation-swap a2 a as)

  sort : List A -> List A
  sort []        = []
  sort (a :: as) = (insert a (sort as))

  sort-permutation : (as : List A) -> (Permutation A (sort as) as)
  sort-permutation [] = permutation-empty
  sort-permutation (a :: as) =
    permutation-compose
      (insert-permutation a (sort as))
      (permutation-cons a (sort-permutation as))

  module weak-tri (weak-tri≤ : WeakTrichotomous _≤_) where
    insert-semi-sorted' :
      (a : A) -> {as : List A} ->
      (SemiSorted (a :: as)) ->
      insert a as == a :: as
    insert-semi-sorted' a {[]} _ = refl
    insert-semi-sorted' a {a2 :: as} (f , ss) = handle (f (0 , refl))
      where
      handle : (a ≤ a2 ⊎ a == a2) -> insert a (a2 :: as) == a :: a2 :: as
      handle (inj-l a≤a2) = insert-≤ a a2 as a≤a2
      handle (inj-r a==a2) = insert-==
        where
        rec : insert a as == a2 :: as
        rec = (\i -> insert (a==a2 i) as) >=> (insert-semi-sorted' a2 ss)

        insert-== : insert a (a2 :: as) == a :: a2 :: as
        insert-== = handle2 (dec≤ a a2)
          where
          handle2 : Dec (a ≤ a2) -> insert a (a2 :: as) == a :: a2 :: as
          handle2 (yes a≤a2) = insert-≤ a a2 as a≤a2
          handle2 (no ¬a≤a2) =
            insert-¬≤ a a2 as ¬a≤a2
            >=> (\i -> (a==a2 (~ i)) :: (rec i))


    insert-semi-sorted : (a : A) -> {as : List A} -> (SemiSorted as) -> (SemiSorted (insert a as))
    insert-semi-sorted a {[]}       _    = semi-sorted-singleton a
    insert-semi-sorted a {a2 :: as} ss@(co-a2-as , s-as) with (weak-tri≤ a a2)
    ... | (weak-tri< a≤a2 _ _)  =
      transport (\i -> SemiSorted (insert-≤ a a2 as a≤a2 (~ i)))
                (semi-sorted-cons≤ a a2 as a≤a2 ss)
    ... | (weak-tri= a==a2)     =
      transport (\i -> SemiSorted (insert-== (~ i)))
                (semi-sorted-cons== a a2 as a==a2 ss)
      where

      insert-==' : insert a2 as == a2 :: as
      insert-==' = insert-semi-sorted' a2 ss

      insert-=='' : insert a as == a2 :: as
      insert-=='' = (\i -> insert (a==a2 i) as) >=> insert-=='

      insert-== : insert a (a2 :: as) == a :: a2 :: as
      insert-== = handle (dec≤ a a2)
        where
        handle : Dec (a ≤ a2) -> insert a (a2 :: as) == a :: a2 :: as
        handle (yes a≤a2) = insert-≤ a a2 as a≤a2
        handle (no ¬a≤a2) =
          insert-¬≤ a a2 as ¬a≤a2
          >=> (\i -> (a==a2 (~ i)) :: (insert-=='' i))


    ... | (weak-tri> ¬a≤a2 _ a2≤a) =
      transport (\i -> SemiSorted (insert-¬≤ a a2 as ¬a≤a2 (~ i)))
                (co-a2 , (insert-semi-sorted a s-as))
      where
      co-a2' : ContainsOnly ((a2 ≤_) ∪ (a2 ==_)) (a :: as)
      co-a2' (zero  , path) = (inj-l (transport (\i -> a2 ≤ (path (~ i))) a2≤a))
      co-a2' (suc n , path) = co-a2-as (n , path)

      co-a2 : ContainsOnly ((a2 ≤_) ∪ (a2 ==_)) (insert a as)
      co-a2 = co-a2' ∘ (permutation-contains (insert-permutation a as))


    sort-semi-sorted : (as : List A) -> (SemiSorted (sort as))
    sort-semi-sorted [] = semi-sorted-[]
    sort-semi-sorted (a :: as) = (insert-semi-sorted a (sort-semi-sorted as))


  module connex (connex≤ : Connex' _≤_) where

    private
      flip : {a a2 : A} -> ¬ (a ≤ a2) -> (a2 ≤ a)
      flip {a} {a2} ¬a≤a2 = handle (connex≤ a a2)
        where
        handle : (a ≤ a2 ⊎ a2 ≤ a) -> a2 ≤ a
        handle (inj-l a≤a2) = bot-elim (¬a≤a2 a≤a2)
        handle (inj-r a2≤a) = a2≤a

    insert-sorted : (a : A) -> {as : List A} -> (Sorted as) -> (Sorted (insert a as))
    insert-sorted a {[]}       _    = sorted-singleton a
    insert-sorted a {a2 :: as} (co-a2-as , s-as) with (dec≤ a a2)
    ... | (yes a≤a2) = sorted-cons a a2 as a≤a2 (co-a2-as , s-as)
    ... | (no  ¬a≤a2) = (co-a2 , (insert-sorted a s-as))
      where
      co-a2' : ContainsOnly (a2 ≤_) (a :: as)
      co-a2' (zero  , path) = transport (\i -> a2 ≤ (path (~ i))) (flip ¬a≤a2)
      co-a2' (suc n , path) = co-a2-as (n , path)

      co-a2 : ContainsOnly (a2 ≤_) (insert a as)
      co-a2 = co-a2' ∘ (permutation-contains (insert-permutation a as))

    sort-sorted : (as : List A) -> (Sorted (sort as))
    sort-sorted [] = sorted-[]
    sort-sorted (a :: as) = (insert-sorted a (sort-sorted as))

    module antisym (antisym≤ : Antisymmetric _≤_) where
      insert-list≤->== : {a : A} {as : List A} -> ContainsOnly (a ≤_) as -> insert a as == a :: as
      insert-list≤->== {a} {[]} f = refl
      insert-list≤->== {a} {a2 :: as} f = handle (dec≤ a a2)
        where
        handle : (d : (Dec (a ≤ a2))) -> insert a (a2 :: as) == a :: a2 :: as
        handle (yes a≤a2) = insert-≤ a a2 as a≤a2
        handle (no ¬a≤a2) =
          insert-¬≤ a a2 as ¬a≤a2 >=> rec-path >=> flip-as
          where
          a2≤a : a2 ≤ a
          a2≤a = flip ¬a≤a2

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
        handle (dec≤ a2 a3) (dec≤ a1 a3) (dec≤ a2 a1)
        where
        handle : (x : Dec (a2 ≤ a3)) -> (y : Dec (a1 ≤ a3)) -> (z : Dec (a2 ≤ a1)) ->
                 insert a1 (insert a2 (a3 :: as)) == insert a2 (insert a1 (a3 :: as))
        handle _           _           (yes a2≤a1) =
          \i -> insert (p i) (insert (p (~ i)) (a3 :: as))
          where
          p : a1 == a2
          p = antisym≤ a1≤a2 a2≤a1

        handle (yes a2≤a3) (yes a1≤a3) (no ¬a2≤a1) =
          begin
            insert a1 (insert a2 (a3 :: as))
          ==< (cong (insert a1) (insert-≤ a2 a3 as a2≤a3)) >
            insert a1 (a2 :: a3 :: as)
          ==< (insert-≤ a1 a2 (a3 :: as) a1≤a2) >
            a1 :: a2 :: a3 :: as
          ==< (cong (a1 ::_) (sym (insert-≤ a2 a3 as a2≤a3))) >
            a1 :: (insert a2 (a3 :: as))
          ==< (sym (insert-¬≤ a2 a1 (a3 :: as) ¬a2≤a1)) >
            insert a2 (a1 :: a3 :: as)
          ==< (cong (insert a2) (sym (insert-≤ a1 a3 as a1≤a3))) >
            insert a2 (insert a1 (a3 :: as))
          end
        handle (yes a2≤a3) (no ¬a1≤a3) (no _) =
          \i -> insert (p i) (insert (p (~ i)) (a3 :: as))
          where
          p : a1 == a2
          p = antisym≤ a1≤a2 (trans≤ a2≤a3 (flip ¬a1≤a3))
        handle (no ¬a2≤a3) (yes a1≤a3) (no ¬a2≤a1) =
          begin
            insert a1 (insert a2 (a3 :: as))
          ==< (cong (insert a1) (insert-¬≤ a2 a3 as ¬a2≤a3)) >
            insert a1 (a3 :: (insert a2 as))
          ==< (insert-≤ a1 a3 (insert a2 as) a1≤a3) >
            a1 :: a3 :: (insert a2 as)
          ==< cong (a1 ::_) (sym (insert-¬≤ a2 a3 as ¬a2≤a3)) >
            a1 :: insert a2 (a3 :: as)
          ==< (sym (insert-¬≤ a2 a1 (a3 :: as) ¬a2≤a1)) >
            insert a2 (a1 :: a3 :: as)
          ==< cong (insert a2) (sym (insert-≤ a1 a3 as a1≤a3)) >
            insert a2 (insert a1 (a3 :: as))
          end
        handle (no ¬a2≤a3) (no ¬a1≤a3) (no ¬a2≤a1) =
          begin
            insert a1 (insert a2 (a3 :: as))
          ==< (cong (insert a1) (insert-¬≤ a2 a3 as ¬a2≤a3)) >
            insert a1 (a3 :: (insert a2 as))
          ==< (insert-¬≤ a1 a3 (insert a2 as) ¬a1≤a3) >
            a3 :: (insert a1 (insert a2 as))
          ==< cong (a3 ::_) (double-insert-path a1 a2 as) >
            a3 :: (insert a2 (insert a1 as))
          ==< sym (insert-¬≤ a2 a3 (insert a1 as) ¬a2≤a3) >
            insert a2 (a3 :: (insert a1 as))
          ==< cong (insert a2) (sym (insert-¬≤ a1 a3 as ¬a1≤a3)) >
            insert a2 (insert a1 (a3 :: as))
          end

      double-insert-path a1 a2 [] = handle (dec≤ a1 a2) (dec≤ a2 a1)
        where
        handle : (x : Dec (a1 ≤ a2)) -> (y : Dec (a2 ≤ a1)) ->
                 insert a1 (insert a2 []) == insert a2 (insert a1 [])
        handle (yes a1≤a2) (yes a2≤a1) = \i -> insert (p i) (insert (p (~ i)) [])
          where
          p : a1 == a2
          p = antisym≤ a1≤a2 a2≤a1
        handle (yes a1≤a2) (no ¬a2≤a1) =
          insert-≤ a1 a2 [] a1≤a2 >=> sym (insert-¬≤ a2 a1 [] ¬a2≤a1)
        handle (no ¬a1≤a2) (yes a2≤a1) =
          insert-¬≤ a1 a2 [] ¬a1≤a2 >=> sym (insert-≤ a2 a1 [] a2≤a1)
        handle (no ¬a1≤a2) (no ¬a2≤a1) = bot-elim (handle2 (connex≤ a1 a2))
          where
          handle2 : ¬ (a1 ≤ a2 ⊎ a2 ≤ a1)
          handle2 (inj-l a1≤a2) = ¬a1≤a2 a1≤a2
          handle2 (inj-r a2≤a1) = ¬a2≤a1 a2≤a1

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

module total (dec≤ : Decidable2 _≤_) (ord≤ : TotalOrder _≤_) (connex'≤ : Connex' _≤_) where
  private
    trans≤ = fst ord≤
    connex≤ = fst (snd ord≤)
    antisym≤ = snd (snd ord≤)

  private
    flip : {a a2 : A} -> ¬ (a ≤ a2) -> (a2 ≤ a)
    flip {a} {a2} ¬a≤a2 = handle (connex'≤ a a2)
      where
      handle : (a ≤ a2 ⊎ a2 ≤ a) -> a2 ≤ a
      handle (inj-l a≤a2) = bot-elim (¬a≤a2 a≤a2)
      handle (inj-r a2≤a) = a2≤a


  tri≤ : WeakTrichotomous _≤_
  tri≤ x y = handle (dec≤ x y) (dec≤ y x)
    where
    handle : Dec (x ≤ y) -> Dec (y ≤ x) -> WeakTri (x ≤ y) (x == y) (y ≤ x)
    handle (yes x≤y) (yes y≤x) = weak-tri= (antisym≤ x≤y y≤x)
    handle (yes x≤y) (no ¬y≤x) = weak-tri< x≤y x!=y ¬y≤x
      where
      x!=y : x != y
      x!=y x==y = ¬y≤x (transport (\i -> (x==y i) ≤ (x==y (~ i))) x≤y)
    handle (no ¬x≤y) (yes y≤x) = weak-tri> ¬x≤y x!=y y≤x
      where
      x!=y : x != y
      x!=y x==y = ¬x≤y (transport (\i -> (x==y (~ i)) ≤ (x==y i)) y≤x)
    handle (no ¬x≤y) (no ¬y≤x) = bot-elim (handle2 (connex'≤ x y))
      where
      handle2 : ¬ (x ≤ y ⊎ y ≤ x)
      handle2 (inj-l x≤y) = ¬x≤y x≤y
      handle2 (inj-r y≤x) = ¬y≤x y≤x


  private
    module algo' = dec-algo trans≤ dec≤
  open algo' public

  private
    module connex' = connex connex'≤
  open connex' public

  private
    module antisym' = antisym antisym≤
  open antisym' public
