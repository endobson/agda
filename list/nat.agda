{-# OPTIONS --cubical --safe --exact-split #-}

module list.nat where

open import base
open import decision
open import equality
open import fin
open import list
open import list.filter
open import list.sorted
open import list.unordered
open import list.discrete
open import infinity-monoid
open import nat
open import nat.bounded
open import nat.order
open import order
open import order.instances.nat
open import relation
open import sum
open import truncation

open EqReasoning

private
  variable
    ℓ : Level

allNatsUnder : Nat -> List Nat
allNatsUnder zero    = []
allNatsUnder (suc n) = n :: allNatsUnder n


allNatsUnder< : (n : Nat) -> ContainsAll (_< n) (allNatsUnder n)
allNatsUnder< zero    lt          = bot-elim (zero-≮ lt)
allNatsUnder< (suc n) (zero  , p) = zero , cong pred p
allNatsUnder< (suc n) (suc i , p) =
  cons-contains n (allNatsUnder< n (i , cong pred p))

onlyNatsUnder< : (n : Nat) -> ContainsOnly (_< n) (allNatsUnder n)
onlyNatsUnder< n = transport (\i -> ContainsOnly (_< n) (path refl-≤ i))
                             (filter-contains-only decide-P (allNatsUnder n))
  where

  decide-P : (a : Nat) -> Dec (a < n)
  decide-P a = decide-< a n

  path : {m : Nat} -> (m ≤ n) -> (filter decide-P (allNatsUnder m)) == (allNatsUnder m)
  path {zero} lt = refl
  path {suc m} lt = filter-keeps decide-P (allNatsUnder m) lt >=> cong (m ::_) helper
    where
    helper : (filter decide-P (allNatsUnder m)) == (allNatsUnder m)
    helper = path {m} (pred-≤ (right-suc-≤ lt))

all-nats-no-duplicates : (n : Nat) -> NoDuplicates (allNatsUnder n)
all-nats-no-duplicates zero = lift tt
all-nats-no-duplicates (suc n) = (¬c , all-nats-no-duplicates n)
  where
  ¬c : ¬ (contains n (allNatsUnder n))
  ¬c c = irrefl-< (onlyNatsUnder< n c)

all-nats-sorted : (n : Nat) -> Sorted _>_ (allNatsUnder n)
all-nats-sorted zero    = lift tt
all-nats-sorted (suc n) = (onlyNatsUnder< n , all-nats-sorted n)

allBounded : {P : Pred Nat ℓ} -> (b : isBounded P) -> ContainsAll P (allNatsUnder ⟨ b ⟩)
allBounded {P} (_ , f) p = allNatsUnder< _ (f p)

sorted>->sorted≥ : {as : List Nat} -> Sorted _>_ as -> Sorted _≥_ as
sorted>->sorted≥ {[]}      s = s
sorted>->sorted≥ {a :: as} (co , s) = (\ c -> pred-≤ (right-suc-≤ (co c))) , sorted>->sorted≥ s

sorted>->no-duplicates : {as : List Nat} -> Sorted _>_ as -> NoDuplicates as
sorted>->no-duplicates {[]}      s = s
sorted>->no-duplicates {a :: as} (co , s) = (\ c -> <->!= (co c) refl) , sorted>->no-duplicates s

CanonicalList≥ : (P : Pred Nat ℓ) -> List Nat -> Type ℓ
CanonicalList≥ P as = ContainsExactlyOnce P as × Sorted _≥_ as

canonical-contains-only : {P : Pred Nat ℓ} {as : List Nat} -> CanonicalList≥ P as -> ContainsOnly P as
canonical-contains-all : {P : Pred Nat ℓ} {as : List Nat} -> CanonicalList≥ P as -> ContainsAll P as
canonical-no-duplicates : {P : Pred Nat ℓ} {as : List Nat} -> CanonicalList≥ P as -> NoDuplicates as
canonical-sorted : {P : Pred Nat ℓ} {as : List Nat} -> CanonicalList≥ P as -> Sorted _≥_ as
canonical-contains-only  (((co , ca) , nd) , s) = co
canonical-contains-all   (((co , ca) , nd) , s) = ca
canonical-no-duplicates  (((co , ca) , nd) , s) = nd
canonical-sorted         (((co , ca) , nd) , s) = s

canonical-list-== : {P : Pred Nat ℓ} {as bs : List Nat}
                     -> CanonicalList≥ P as -> CanonicalList≥ P bs
                     -> as == bs
canonical-list-== {P = P} {as} {bs} (ce1-a , sa) (ce1-b , sb) =
  begin
    as
  ==< sym (sorted-== sa) >
    sort as
  ==< sym (order-unorder-== as) >
    order (unorder as)
  ==< cong order (unorder-permutation (contains-exactly-once->permutation ce1-a ce1-b))  >
    order (unorder bs)
  ==< order-unorder-== bs >
    sort bs
  ==< sorted-== sb >
    bs
  end
  where
    dec≥ : Decidable2 _≥_
    dec≥ x y = decide-≤ y x
    ord≥ : TotalOrder _≥_
    ord≥ = total-order-≥
    connex'-≥ : Connex' _≥_
    connex'-≥ x y = ⊎-map weaken-< (\x -> x) (split-< y x)


    open total _≥_ dec≥ ord≥ connex'-≥


private
  exactBoundedDecidable : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
                          -> ContainsExactlyOnce P (filter dec (allNatsUnder ⟨ b ⟩))
  exactBoundedDecidable b dec =
    (filter-contains-only dec (allNatsUnder ⟨ b ⟩) ,
     filter-contains-all dec (allNatsUnder ⟨ b ⟩) (allBounded b)) ,
    filter-no-duplicates dec (allNatsUnder ⟨ b ⟩) (all-nats-no-duplicates ⟨ b ⟩)

  canonicalBoundedDecidable :
    {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
    -> CanonicalList≥ P (filter dec (allNatsUnder ⟨ b ⟩))
  canonicalBoundedDecidable b dec =
    (((filter-contains-only dec (allNatsUnder ⟨ b ⟩) ,
       filter-contains-all dec (allNatsUnder ⟨ b ⟩) (allBounded b)) ,
      filter-no-duplicates dec (allNatsUnder ⟨ b ⟩) (all-nats-no-duplicates ⟨ b ⟩)) ,
     (filter-sorted dec (sorted>->sorted≥ (all-nats-sorted ⟨ b ⟩))))

list-reify : {P : Pred Nat ℓ} (b : isBounded P) (dec : Decidable P)
              -> Σ (List Nat) (CanonicalList≥ P)
list-reify b dec = l , proof
  where
  l = (filter dec (allNatsUnder ⟨ b ⟩))
  proof = canonicalBoundedDecidable b dec


module _ {ℓp ℓq : Level} {P : Pred Nat ℓp} {Q : Pred Nat ℓq} where

  canonical-join : {as bs cs ds : List Nat}
    -> CanonicalList≥ P as
    -> CanonicalList≥ Q bs
    -> CanonicalList≥ (P ∪ Q) cs
    -> CanonicalList≥ (P ∩ Q) ds
    -> Permutation Nat (as ++ bs) (cs ++ ds)
  canonical-join {as} {bs} {cs} {ds} c-as c-bs c-cs c-ds = same-count->permutation f
    where
    count1 : {P : Pred Nat ℓ} {x : Nat} {xs : List Nat}
             -> CanonicalList≥ P xs -> contains x xs -> count x xs == 1
    count1 {x = x} {xs = xs} canonical contains-x =
      antisym-≤ (no-duplicates->count (canonical-no-duplicates canonical) x)
                (contains->count>0 xs contains-x)
    count0 : {P : Pred Nat ℓ} {x : Nat} {xs : List Nat}
             -> CanonicalList≥ P xs -> ¬(contains x xs) -> count x xs == 0
    count0 {xs = xs} _ = ¬contains->count==0 xs

    co-as = canonical-contains-only c-as
    co-bs = canonical-contains-only c-bs
    co-cs = canonical-contains-only c-cs
    co-ds = canonical-contains-only c-ds
    ca-as = canonical-contains-all c-as
    ca-bs = canonical-contains-all c-bs
    ca-cs = canonical-contains-all c-cs
    ca-ds = canonical-contains-all c-ds



    f : (x : Nat) -> count x (as ++ bs) == count x (cs ++ ds)
    f x = handle (decide-contains x as) (decide-contains x bs)
      where
      handle : Dec (contains x as) -> Dec (contains x bs) -> count x (as ++ bs) == count x (cs ++ ds)
      handle (yes x-as) (yes x-bs) =
        count-++ x as bs
        >=> (\i -> (count1 c-as x-as i)     +' (count1 c-bs x-bs i))
        >=> (\i -> (count1 c-cs x-cs (~ i)) +' (count1 c-ds x-ds (~ i)))
        >=> sym (count-++ x cs ds)
        where
        x-cs : contains x cs
        x-cs = ca-cs (inj-l (co-as x-as))
        x-ds : contains x ds
        x-ds = ca-ds (co-as x-as , co-bs x-bs)

      handle (yes x-as) (no ¬x-bs) =
        count-++ x as bs
        >=> (\i -> (count1 c-as x-as i)     +' (count0 c-bs ¬x-bs i))
        >=> (\i -> (count1 c-cs x-cs (~ i)) +' (count0 c-ds ¬x-ds (~ i)))
        >=> sym (count-++ x cs ds)
        where
        x-cs : contains x cs
        x-cs = ca-cs (inj-l (co-as x-as))
        ¬x-ds : ¬ (contains x ds)
        ¬x-ds x-ds = ¬x-bs (ca-bs (proj₂ (co-ds x-ds)))

      handle (no ¬x-as) (yes x-bs) =
        count-++ x as bs
        >=> (\i -> (count0 c-as ¬x-as i)    +' (count1 c-bs x-bs i))
        >=> (\i -> (count1 c-cs x-cs (~ i)) +' (count0 c-ds ¬x-ds (~ i)))
        >=> sym (count-++ x cs ds)
        where
        x-cs : contains x cs
        x-cs = ca-cs (inj-r (co-bs x-bs))
        ¬x-ds : ¬ (contains x ds)
        ¬x-ds x-ds = ¬x-as (ca-as (proj₁ (co-ds x-ds)))
      handle (no ¬x-as) (no ¬x-bs) =
        count-++ x as bs
        >=> (\i -> (count0 c-as ¬x-as i)     +' (count0 c-bs ¬x-bs i))
        >=> (\i -> (count0 c-cs ¬x-cs (~ i)) +' (count0 c-ds ¬x-ds (~ i)))
        >=> sym (count-++ x cs ds)
        where
        ¬x-cs : ¬(contains x cs)
        ¬x-cs x-cs = handle2 (co-cs x-cs)
          where
          handle2 : (P x ⊎ Q x) -> Bot
          handle2 (inj-l p-x) = ¬x-as (ca-as p-x)
          handle2 (inj-r q-x) = ¬x-bs (ca-bs q-x)

        ¬x-ds : ¬ (contains x ds)
        ¬x-ds x-ds = ¬x-as (ca-as (proj₁ (co-ds x-ds)))

-- Range of numbers. Uses clopen semantics.

clopen-range : Nat -> Nat -> List Nat
clopen-range zero    n       = allNatsUnder n
clopen-range (suc m) zero    = []
clopen-range (suc m) (suc n) = map suc (clopen-range m n)

clopen-range-≥ : {m n : Nat} -> (m ≥ n) -> clopen-range m n == []
clopen-range-≥ {zero}  {zero}  gt = refl
clopen-range-≥ {zero}  {suc n} gt = bot-elim (zero-≮ gt)
clopen-range-≥ {suc m} {zero}  gt = refl
clopen-range-≥ {suc m} {suc n} gt =
  cong (map suc) (clopen-range-≥ {m} {n} (pred-≤ gt))


clopen-range-suc : {m n : Nat} -> m ≤ n -> clopen-range m (suc n) == n :: (clopen-range m n)
clopen-range-suc {zero} {n} lt = refl
clopen-range-suc {suc m} {zero} lt = bot-elim (zero-≮ lt)
clopen-range-suc {suc m} {suc n} lt =
  begin
    clopen-range (suc m) (suc (suc n))
  ==<>
    map suc (clopen-range m (suc n))
  ==< cong (map suc) (clopen-range-suc {m} {n} (pred-≤ lt)) >
    map suc (n :: (clopen-range m n))
  ==<>
    (suc n) :: (clopen-range (suc m) (suc n))
  end

private
  clopen-range0-++ : {m n : Nat} -> m ≤ n
                      -> clopen-range 0 n == (clopen-range m n) ++ clopen-range 0 m
  clopen-range0-++ {m} {n} (zero , path) =
    begin
      clopen-range 0 n
    ==< cong (clopen-range 0) (sym path) >
      clopen-range 0 m
    ==<>
      [] ++ clopen-range 0 m
    ==< cong (_++ clopen-range 0 m) (sym (clopen-range-≥ (0 , sym path))) >
      (clopen-range m n) ++ clopen-range 0 m
    end
  clopen-range0-++ {m} {zero} (suc i , path) = bot-elim (zero-suc-absurd (sym path))
  clopen-range0-++ {m} {(suc n)} (suc i , path) =
    begin
      clopen-range 0 (suc n)
    ==< clopen-range-suc zero-≤ >
      n :: (clopen-range 0 n)
    ==< cong (n ::_) (clopen-range0-++ lt) >
      n :: ((clopen-range m n) ++ clopen-range 0 m)
    ==< cong (_++ (clopen-range 0 m)) (sym (clopen-range-suc lt)) >
      (clopen-range m (suc n)) ++ clopen-range 0 m
    end
    where
    lt : m ≤ n
    lt = i , cong pred path

clopen-range-+-left : (m n p : Nat) -> clopen-range (m +' n) (m +' p) == map (m +'_) (clopen-range n p)
clopen-range-+-left 0       n p = sym (map-identity (clopen-range n p))
clopen-range-+-left (suc m) n p =
  begin
    clopen-range (suc m +' n) (suc m +' p)
  ==<>
    map suc (clopen-range (m +' n) (m +' p))
  ==< cong (map suc) (clopen-range-+-left m n p) >
    map suc (map (m +'_) (clopen-range n p))
  ==< double-map suc (m +'_) (clopen-range n p) >
    map ((suc m) +'_) (clopen-range n p)
  end


clopen-range-++ : {m n p : Nat} -> m ≤ n -> n ≤ p
                  -> clopen-range m p == clopen-range n p ++ clopen-range m n
clopen-range-++ {m} {n} {p} m≤n@(k1 , k1-path) n≤p@(k2 , k2-path) = full-path
  where
  k3 = k2 +' k1
  k3-path : k3 +' m == p
  k3-path = (snd (trans-≤ m≤n n≤p))

  full-path : clopen-range m p == clopen-range n p ++ clopen-range m n
  full-path =
    begin
    begin
      clopen-range m p
    ==< (\i -> clopen-range (+'-right-zero {m} (~ i)) ((sym k3-path >=> +'-commute {k3} {m}) i)) >
      clopen-range (m +' 0) (m +' k3)
    ==< clopen-range-+-left m 0 k3 >
      map (m +'_) (clopen-range 0 k3)
    ==< cong (map (m +'_)) (clopen-range0-++ (k2 , refl)) >
      map (m +'_) ((clopen-range k1 k3) ++ clopen-range 0 k1)
    ==< InfinityMonoidʰ.preserves-∙ (mapʰ (m +'_)) (clopen-range k1 k3) (clopen-range 0 k1) >
      map (m +'_) (clopen-range k1 k3) ++
      map (m +'_) (clopen-range 0 k1)
    ==< (\i -> (clopen-range-+-left m k1 k3 (~ i)) ++
               (clopen-range-+-left m 0  k1 (~ i))) >
      (clopen-range (m +' k1) (m +' k3)) ++
      (clopen-range (m +' 0) (m +' k1))
    ==< (\i -> (clopen-range (+'-commute {m} {k1} i) (+'-commute {m} {k3} i)) ++
               (clopen-range (+'-commute {m} {0} i) (+'-commute {m} {k1} i))) >
      (clopen-range (k1 +' m) (k3 +' m)) ++
      (clopen-range m (k1 +' m))
    ==< (\i -> (clopen-range (k1-path i) (k3-path i)) ++
               (clopen-range m (k1-path i))) >
      (clopen-range n p) ++ (clopen-range m n)
    end

private
  clopen-range-contains-only : (m n : Nat) -> ContainsOnly ((m ≤_) ∩ (_< n)) (clopen-range m n)
  clopen-range-contains-only zero n {k} ck = zero-≤ , onlyNatsUnder< n ck
  clopen-range-contains-only (suc m) zero ()
  clopen-range-contains-only (suc m) (suc n) {k} ck = m≤k , k<n
    where
    Σj : Σ[ j ∈ Nat ] (contains j (clopen-range m n) × suc j == k)
    Σj = map-contains' suc (clopen-range m n) ck
    j = ⟨ Σj ⟩

    rec : (m ≤ j) × (j < n)
    rec = clopen-range-contains-only m n (fst (snd Σj))
    m≤j = fst rec
    j<n = snd rec

    m≤k : (suc m) ≤ k
    m≤k = fst m≤j , +'-right-suc >=> cong suc (snd m≤j) >=> (snd (snd Σj))
    k<n : k < (suc n)
    k<n = fst j<n , +'-right-suc >=> +'-right {suc (fst j<n)} (sym (snd (snd Σj)))
                    >=> cong suc (snd j<n)

  clopen-range-contains-all : (m n : Nat) -> ContainsAll ((m ≤_) ∩ (_< n)) (clopen-range m n)
  clopen-range-contains-all zero    n (m≤k , k<n) = allNatsUnder< n k<n
  clopen-range-contains-all (suc m) zero    (m≤k , k<n) = bot-elim (zero-≮ (trans-≤-< m≤k k<n))
  clopen-range-contains-all (suc m) (suc n) {zero} (sm≤k , _) = bot-elim (zero-≮ sm≤k)
  clopen-range-contains-all (suc m) (suc n) {suc k} (sm≤k , k<sn) =
    map-contains suc (clopen-range m n) (clopen-range-contains-all m n ((pred-≤ sm≤k) , (pred-≤ k<sn)))

  clopen-range-no-duplicates : (m n : Nat) -> NoDuplicates (clopen-range m n)
  clopen-range-no-duplicates zero    n       = all-nats-no-duplicates n
  clopen-range-no-duplicates (suc m) zero    = lift tt
  clopen-range-no-duplicates (suc m) (suc n) =
    map-no-duplicates suc-injective (clopen-range-no-duplicates m n)

  clopen-range-sorted : (m n : Nat) -> Sorted _>_ (clopen-range m n)
  clopen-range-sorted zero    n       = all-nats-sorted n
  clopen-range-sorted (suc m) zero    = lift tt
  clopen-range-sorted (suc m) (suc n) = map-sorted suc-monotonic-> (clopen-range-sorted m n)

clopen-range-canonical : (m n : Nat) -> CanonicalList≥ ((m ≤_) ∩ (_< n)) (clopen-range m n)
clopen-range-canonical m n = ((co , ca) , nd) , sorted
  where
  co = clopen-range-contains-only m n
  ca = clopen-range-contains-all m n
  nd = clopen-range-no-duplicates m n
  sorted = sorted>->sorted≥ (clopen-range-sorted m n)
