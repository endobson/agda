{-# OPTIONS --cubical --safe --exact-split #-}

module category.example where

open import base
open import cubical
open import category.base
open import category.constructions.iterated-product
open import category.constructions.isomorphism
open import category.constructions.functor-cat
open import category.displayed
open import category.instances.discrete
open import category.instances.finset
open import category.instances.set
open import category.monoidal.base
open import equality-path
open import hlevel
open import nat


ℕC : PreCategory ℓ-zero ℓ-zero
ℕC = DiscreteC (isOfHLevelSuc 2 isSetNat)

-- module _
--   {ℓObjC ℓObjD ℓMorC ℓMorD : Level}
--   {C : PreCategory ℓObjC ℓMorC} {D : PreCategory ℓObjD ℓMorD}
--   {F G : Functor C D} where
--
--   private
--     obj-path : (c : Obj C) -> (nt1 nt2 : NaturalTransformation F G)
--                (p1 p2 : nt1 == nt2) ->
--                Path (NT-obj nt1 c == NT-obj nt2 c) (\i -> NT-obj (p1 i) c) (\i -> NT-obj (p2 i) c)
--     obj-path c nt1 nt2 p1 p2 i j =
--       isSet-Mor D (NT-obj nt1 c) (NT-obj nt2 c)
--                   (cong (\nt -> NT-obj nt c) p1) (cong (\nt -> NT-obj nt c) p2) i j
--   isSet-NaturalTransformation : isSet (NaturalTransformation F G)
--   isSet-NaturalTransformation nt1 nt2 p1 p2 i j .NaturalTransformation.NT-obj c =
--     obj-path c nt1 nt2 p1 p2 i j
--   isSet-NaturalTransformation nt1 nt2 p1 p2 i j .NaturalTransformation.NT-mor {x} {y} f =
--     square i j
--     where
--     square : PathP (\k -> PathP (\k2 -> (obj-path x nt1 nt2 p1 p2 k k2 ⋆⟨ D ⟩ _ ==
--                                          _ ⋆⟨ D ⟩ obj-path y nt1 nt2 p1 p2 k k2))
--                                 (NT-mor nt1 f) (NT-mor nt2 f))
--               (cong (\nt -> NT-mor nt f) p1)
--               (cong (\nt -> NT-mor nt f) p2)
--     square = isSet->SquareP (\i j -> isOfHLevelPath 2 (isSet-Mor D) _ _)


-- module _ {ℓO ℓM ℓD : Level} {D : Type ℓD} (C : D -> PreCategory ℓO ℓM) where
--
--   LargeProdC : PreCategory _ _
--   LargeProdC = ?
--     where
--     sorts : CategorySorts _ _
--     sorts .CategorySorts.Obj = Σ[ d ∈ D ] (Obj (C d))
--     sorts .CategorySorts.Mor (d1 , o1) (d2 , o2) =
--       Σ[ p ∈ d1 == d2 ] Σ[ m1 ∈

-- module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) (M : MonoidalStr C) where
--   open CategoryHelpers C
--   open MonoidalStrHelpers M
--
--   private
--     PC : (n : Nat) -> PreCategory ℓO ℓM
--     PC n = IteratedProductC C n
--
--   C2 : PreCategoryᴰ (IsoC (FinSetC ℓ-zero)) _ _
--   C2 .PreCategoryᴰ.Objᴰ ((S , isSet-S) , (n , eq)) =
--     Functor (DiscreteC isSet-S) (FunctorC (PC n) C)
--   C2 .PreCategoryᴰ.Morᴰ {S1@((_ , isSet-S1) , _)} {S2@(_ , (n2 , _))}
--                         ((set-function g , tt) , isIso-g) f1 f2 =
--     NaturalTransformation f1 ?
--     where
--     check-f1 : Functor
--     f2' : Functor (DiscreteC isSet-S1) (PC n2)
--     f2' = ?


record CategoryᴰSorts {ℓO ℓM : Level} (C : PreCategory ℓO ℓM)
                      (ℓOᴰ ℓMᴰ : Level) : Type (ℓ-max* 3 ℓO ℓM (ℓ-suc (ℓ-max ℓOᴰ ℓMᴰ))) where
  field
    Objᴰ : (c : Obj C) -> Type ℓOᴰ
    Morᴰ : {a b : Obj C} (f : C [ a , b ]) (c : Objᴰ a) (d : Objᴰ b) -> Type ℓMᴰ

record CategoryᴰOps {ℓO ℓM ℓOᴰ ℓMᴰ : Level} {C : PreCategory ℓO ℓM}
                    (S : CategoryᴰSorts C ℓOᴰ ℓMᴰ) : Type (ℓ-max* 4 ℓO ℓM ℓOᴰ ℓMᴰ) where
  private
    module S = CategoryᴰSorts S

  field
    idᴰ : {c : Obj C} {d : S.Objᴰ c} -> S.Morᴰ (id C) d d
    _⋆ᴰ_ : {a b c : Obj C} {f : C [ a , b ]} {g : C [ b , c ]}
           {aᴰ : S.Objᴰ a} {bᴰ : S.Objᴰ b} {cᴰ : S.Objᴰ c}
           (fᴰ : S.Morᴰ f aᴰ bᴰ) (gᴰ : S.Morᴰ g bᴰ cᴰ) ->
           S.Morᴰ (f ⋆⟨ C ⟩ g) aᴰ cᴰ


record CategoryᴰLaws {ℓO ℓM ℓOᴰ ℓMᴰ : Level} {C : PreCategory ℓO ℓM}
                     {S : CategoryᴰSorts C ℓOᴰ ℓMᴰ} (O : CategoryᴰOps S) :
                     Type (ℓ-max* 4 ℓO ℓM ℓOᴰ ℓMᴰ) where
  private
    module S = CategoryᴰSorts S
    module O = CategoryᴰOps O
    module C = PreCategory C

  field
    ⋆ᴰ-left-id :
      {s t : Obj C} {f : C [ s , t ]} {sᴰ : S.Objᴰ s} {tᴰ : S.Objᴰ t}
      (fᴰ : S.Morᴰ f sᴰ tᴰ) ->
        PathP (\i -> S.Morᴰ (C.⋆-left-id f i) sᴰ tᴰ) (O.idᴰ O.⋆ᴰ fᴰ) fᴰ
    ⋆ᴰ-right-id :
      {s t : Obj C} {f : C [ s , t ]} {sᴰ : S.Objᴰ s} {tᴰ : S.Objᴰ t}
      (fᴰ : S.Morᴰ f sᴰ tᴰ) ->
        PathP (\i -> S.Morᴰ (C.⋆-right-id f i) sᴰ tᴰ) (fᴰ O.⋆ᴰ O.idᴰ) fᴰ
    ⋆ᴰ-assoc :
      {a b c d : Obj C} {f : C [ a , b ]} {g : C [ b , c ]} {h : C [ c , d ]}
      {aᴰ : S.Objᴰ a} {bᴰ : S.Objᴰ b} {cᴰ : S.Objᴰ c} {dᴰ : S.Objᴰ d}
      (fᴰ : S.Morᴰ f aᴰ bᴰ) (gᴰ : S.Morᴰ g bᴰ cᴰ) (hᴰ : S.Morᴰ h cᴰ dᴰ) ->
      PathP (\i -> S.Morᴰ (C.⋆-assoc f g h i) aᴰ dᴰ)
            ((fᴰ O.⋆ᴰ gᴰ) O.⋆ᴰ hᴰ) (fᴰ O.⋆ᴰ (gᴰ O.⋆ᴰ hᴰ))
    isSet-Morᴰ :
      {a b : Obj C} {f : C [ a , b ]} {aᴰ : S.Objᴰ a} {bᴰ : S.Objᴰ b} ->
      isSet (S.Morᴰ f aᴰ bᴰ)


record CategoryᴰSortsP {ℓO ℓM : Level} (C : PreCategory ℓO ℓM)
                       (ℓOᴰ ℓMᴰ : Level) : Type (ℓ-max* 3 ℓO ℓM (ℓ-suc (ℓ-max ℓOᴰ ℓMᴰ))) where
  field
    Objᴰ : (c : Obj C) -> Type ℓOᴰ
    Morᴰ : {a : Obj C} (f : C [ a , a ]) (c : Objᴰ a) (d : Objᴰ a) -> Type ℓMᴰ

record CategoryᴰOpsP {ℓO ℓM ℓOᴰ ℓMᴰ : Level} {C : PreCategory ℓO ℓM}
                     (S : CategoryᴰSortsP C ℓOᴰ ℓMᴰ) : Type (ℓ-max* 4 ℓO ℓM ℓOᴰ ℓMᴰ) where
  private
    module S = CategoryᴰSortsP S

  field
    idᴰ : {c : Obj C} {d : S.Objᴰ c} -> S.Morᴰ (id C) d d
    _⋆ᴰ_ : {a : Obj C} {f : C [ a , a ]} {g : C [ a , a ]}
           {aᴰ : S.Objᴰ a} {bᴰ : S.Objᴰ a} {cᴰ : S.Objᴰ a}
           (fᴰ : S.Morᴰ f aᴰ bᴰ) (gᴰ : S.Morᴰ g bᴰ cᴰ) ->
           S.Morᴰ (f ⋆⟨ C ⟩ g) aᴰ cᴰ

record CategoryᴰLawsP {ℓO ℓM ℓOᴰ ℓMᴰ : Level} {C : PreCategory ℓO ℓM}
                      {S : CategoryᴰSortsP C ℓOᴰ ℓMᴰ} (O : CategoryᴰOpsP S) :
                      Type (ℓ-max* 4 ℓO ℓM ℓOᴰ ℓMᴰ) where
  private
    module S = CategoryᴰSortsP S
    module O = CategoryᴰOpsP O
    module C = PreCategory C

  field
    ⋆ᴰ-left-id :
      {s : Obj C} {f : C [ s , s ]} {sᴰ : S.Objᴰ s} {tᴰ : S.Objᴰ s}
      (fᴰ : S.Morᴰ f sᴰ tᴰ) ->
        PathP (\i -> S.Morᴰ (C.⋆-left-id f i) sᴰ tᴰ) (O.idᴰ O.⋆ᴰ fᴰ) fᴰ
    ⋆ᴰ-right-id :
      {s : Obj C} {f : C [ s , s ]} {sᴰ : S.Objᴰ s} {tᴰ : S.Objᴰ s}
      (fᴰ : S.Morᴰ f sᴰ tᴰ) ->
        PathP (\i -> S.Morᴰ (C.⋆-right-id f i) sᴰ tᴰ) (fᴰ O.⋆ᴰ O.idᴰ) fᴰ
    ⋆ᴰ-assoc :
      {a : Obj C} {f : C [ a , a ]} {g : C [ a , a ]} {h : C [ a , a ]}
      {aᴰ : S.Objᴰ a} {bᴰ : S.Objᴰ a} {cᴰ : S.Objᴰ a} {dᴰ : S.Objᴰ a}
      (fᴰ : S.Morᴰ f aᴰ bᴰ) (gᴰ : S.Morᴰ g bᴰ cᴰ) (hᴰ : S.Morᴰ h cᴰ dᴰ) ->
      PathP (\i -> S.Morᴰ (C.⋆-assoc f g h i) aᴰ dᴰ)
            ((fᴰ O.⋆ᴰ gᴰ) O.⋆ᴰ hᴰ) (fᴰ O.⋆ᴰ (gᴰ O.⋆ᴰ hᴰ))
    isSet-Morᴰ :
      {a : Obj C} {f : C [ a , a ]} {aᴰ : S.Objᴰ a} {bᴰ : S.Objᴰ a} ->
      isSet (S.Morᴰ f aᴰ bᴰ)

isDiscreteC : {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) -> Type (ℓ-max ℓO ℓM)
isDiscreteC C =
  Σ[ f ∈ (∀ {o1 o2 : Obj C} -> C [ o1 , o2 ] -> o1 == o2) ]
    (∀ o -> f (idᵉ C o) == reflᵉ o)

-- module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) (isDiscC : isDiscreteC C) (magic : Magic) where
--
--   module _ {ℓOᴰ ℓMᴰ : Level} {S : CategoryᴰSortsP C ℓOᴰ ℓMᴰ} where
--     private
--       module S = CategoryᴰSortsP S
--
--     CategoryᴰSortsP->CategoryᴰSorts : CategoryᴰSorts C ℓOᴰ ℓMᴰ
--     CategoryᴰSortsP->CategoryᴰSorts .CategoryᴰSorts.Objᴰ = S.Objᴰ
--     CategoryᴰSortsP->CategoryᴰSorts .CategoryᴰSorts.Morᴰ {a} {b} f c d =
--       S.Morᴰ (transport (\i -> C [ p i , b ]) f)
--              (transport (\i -> CategoryᴰSortsP.Objᴰ S (p i)) c) d
--       where
--       p = fst isDiscC f
--
--     open CategoryᴰSorts CategoryᴰSortsP->CategoryᴰSorts
--
--     Morᴰ-path : {a : Obj C} (c : Objᴰ a) (d : Objᴰ a) ->
--                 S.Morᴰ (id C) c d == Morᴰ (id C) c d
--     Morᴰ-path {a} c d j = S.Morᴰ (arg1 j) (arg2 j) d
--       where
--       f = (idᵉ C a)
--       p : a == a
--       p = fst isDiscC (idᵉ C a)
--
--       q : p == refl
--       q = snd isDiscC a
--
--       arg1 : f == transport (\i -> C [ p i , a ]) f
--       arg1 = sym (transportRefl f) >=>
--              (\j -> transport (\i -> C [ q (~ j) i , a ]) f)
--
--       arg2 : c == transport (\i -> Objᴰ (p i)) c
--       arg2 = sym (transportRefl c) >=>
--              (\j -> transport (\i -> Objᴰ (q (~ j) i)) c)
--
--
--     Morᴰ-path' : {a b : Obj C} (f : C [ a , b ]) (c : Objᴰ a) (d : Objᴰ b) ->
--                  Morᴰ f c d ==
--                  Morᴰ (id C) (transport (\i -> Objᴰ (fst isDiscC f i)) c) d
--     Morᴰ-path' {a} {b} f c d = \j -> Morᴰ (arg1 j) (arg2 j) d
--       where
--       p : a == b
--       p = fst isDiscC f
--
--       arg1 : PathP (\i -> C [ p i , b ]) f (id C)
--       arg1 = ?
--       arg2 : PathP (\i -> Objᴰ (p i)) c (transport (\i -> Objᴰ (p i)) c)
--       arg2 = transport-filler (\i -> Objᴰ (p i)) c
--
--
--
--
--     module _ (O : CategoryᴰOpsP S) where
--       private
--         module O = CategoryᴰOpsP O
--
--       CategoryᴰOpsP->CategoryᴰOps : CategoryᴰOps CategoryᴰSortsP->CategoryᴰSorts
--       CategoryᴰOpsP->CategoryᴰOps .CategoryᴰOps.idᴰ {c} {d} =
--         transport (Morᴰ-path d d) O.idᴰ
--       CategoryᴰOpsP->CategoryᴰOps .CategoryᴰOps._⋆ᴰ_
--         {a} {b} {c} {f} {g} {a'} {b'} {c'} f' g' = magic



module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) (M : MonoidalStr C) where
  open CategoryHelpers C
  open MonoidalStrHelpers M
  private

    PC : (n : Nat) -> PreCategory ℓO ℓM
    PC n = IteratedProductC C n

  FC : (n : Nat) -> PreCategory _ _
  FC n = FunctorC (PC n) C

  -- C4 : PreCategoryᴰ (DiscreteC isSetNat) _ _
  -- C4 .PreCategoryᴰ.Objᴰ n = Top
  -- C4 .PreCategoryᴰ.Morᴰ {a} {b} p _ _ =
  --   Functor (IteratedProductC C a) (IteratedProductC C b)
  -- C4 .PreCategoryᴰ.idᴰ {n} = idF (IteratedProductC C n)
  -- C4 .PreCategoryᴰ._⋆ᴰ_ f1 f2 = functor-compose f1 f2
  -- C4 .PreCategoryᴰ.⋆ᴰ-left-id f = Cat-⋆-left-id _ _ f
  -- C4 .PreCategoryᴰ.⋆ᴰ-right-id f = Cat-⋆-right-id _ _ f
  -- C4 .PreCategoryᴰ.⋆ᴰ-assoc f g h = Cat-⋆-assoc _ _ f g h
  -- C4 .PreCategoryᴰ.isSet-Morᴰ = ?

  path->id' : {ℓ : Level} {A : Type ℓ} {x y : A} -> x == y -> x === y
  path->id' {x = x} {y = y} path =
    transport (\i -> x === path i) refl-===


  -- C5 : PreCategoryᴰ (DiscreteC isSetNat) _ _
  -- C5 .PreCategoryᴰ.Objᴰ n = Functor (IteratedProductC C n) C
  -- C5 .PreCategoryᴰ.Morᴰ {a} {b} p f1 f2 = cases (path->id' p) f1 f2
  --   where
  --   cases : a === b ->
  --           Functor (IteratedProductC C a) C ->
  --           Functor (IteratedProductC C b) C ->
  --           Type _
  --   cases refl-=== f1 f2 = NaturalTransformation f1 f2
  -- C5 .PreCategoryᴰ.idᴰ {n} = ?
  --  id (FC n)
  -- C5 .PreCategoryᴰ._⋆ᴰ_ f1 f2 = functor-compose f1 f2
  -- C5 .PreCategoryᴰ.⋆ᴰ-left-id f = Cat-⋆-left-id _ _ f
  -- C5 .PreCategoryᴰ.⋆ᴰ-right-id f = Cat-⋆-right-id _ _ f
  -- C5 .PreCategoryᴰ.⋆ᴰ-assoc f g h = Cat-⋆-assoc _ _ f g h
  -- C5 .PreCategoryᴰ.isSet-Morᴰ = ?



  -- C3 : PreCategoryᴰ (TotalC C2) _ _
  -- C3 .PreCategoryᴰ.Objᴰ (((S , _) , _) , cs) =
  --   Σ[ o ∈ Obj C ] (∀ s -> C [ cs s , o ])
  -- C3 .PreCategoryᴰ.Morᴰ ((set-function f , tt) , ms) o1 o2 = ?


  -- C2 : PreCategoryᴰ (FinSetC ℓ-zero) _ _
  -- C2 .PreCategoryᴰ.Objᴰ ((S , isSet-S) , (n , eq)) =
  --   Functor (DiscreteC isSet-S) (PC n)
  -- C2 .PreCategoryᴰ.Morᴰ {S1@((_ , isSet-S1) , _)} {S2@(_ , (n2 , _))} (set-function g , tt) f1 f2 =
  --   NaturalTransformation f1 ?
  --   where
  --   f2' : Functor (DiscreteC isSet-S1) (PC n2)
  --   f2' = ?



  NC : PreCategory _ _
  NC = DiscreteC (isOfHLevelSuc 2 isSetNat)

  Mor3 : {n1 n2 : Nat} -> (p : n1 == n2) -> Obj (FC n1) -> Obj (FC n2) -> Type _
  Mor3 {n1} {n2} p o1 o2 = (FC n2) [ (transport (\i -> (Obj (FC (p i)))) o1) , o2 ]

  Mor3-refl : (n : Nat) -> (o1 o2 : Obj (FC n)) -> Mor3 (refl {x = n}) o1 o2 == (FC n) [ o1 , o2 ]
  Mor3-refl n o1 o2 j = (FC n) [ transportRefl o1 j , o2 ]

  Mor3-Ind : {ℓ : Level} ->
             (P : (n1 n2 : Nat) (p : n1 == n2) (o1 : Obj (FC n1)) (o2 : Obj (FC n2)) ->
                  Mor3 p o1 o2 -> Type ℓ) ->
             ((n : Nat) (o1 : Obj (FC n)) (o2 : Obj (FC n)) (m : Mor3 (refl {x = n}) o1 o2) ->
              P n n refl o1 o2 m) ->
             (n1 n2 : Nat) (p : n1 == n2) (o1 : Obj (FC n1)) (o2 : Obj (FC n2)) ->
             (m : Mor3 p o1 o2) -> P n1 n2 p o1 o2 m
  Mor3-Ind P refl-case n1 n2 p o1 o2 m =
    transport pP Pm'
    where
    p'1 : Obj (FC n1) == Obj (FC n2)
    p'1 i = Obj (FC (p i))

    p'2 : Mor3 p o1 o2 == Mor3 (refl {x = n2}) (transport (\i -> Obj (FC (p i))) o1) o2
    p'2 = (\j -> Mor3 (\i -> p (i ∨ j)) (transp (\i -> p'1 (i ∧ j)) (~ j) o1) o2)

    m' : Mor3 (refl {x = n2}) (transport (\i -> Obj (FC (p i))) o1) o2
    m' = transport p'2 m

    Pm' : P n2 n2 refl (transport (\i -> Obj (FC (p i))) o1) o2 m'
    Pm' = refl-case n2 (transport (\i -> Obj (FC (p i))) o1) o2 m'

    pP : (P n2 n2 refl (transport (\i -> Obj (FC (p i))) o1) o2 m') ==
         (P n1 n2 p o1 o2 m)
    pP j = P (p (~ j)) n2 (\i -> p (i ∨ (~ j)))
             (transport-filler p'1 o1 (~ j)) o2
             (transport-filler p'2 m (~ j))

  Mor3-id : (n : Nat) (o : Obj (FC n)) -> Mor3 (reflᵉ n) o o
  Mor3-id n o = transport (sym (Mor3-refl n o o)) (id (FC n))

  Mor3-⋆ : (n1 n2 : Nat) (p12 : n1 == n2) (o1 : Obj (FC n1)) (o2 : Obj (FC n2)) ->
           (m12 : Mor3 p12 o1 o2) ->
           (n3 : Nat) (p23 : n2 == n3) (o3 : Obj (FC n3))
           (m23 : Mor3 p23 o2 o3) -> Mor3 (p12 >=> p23) o1 o3
  Mor3-⋆ = Mor3-Ind P refl-case
    where
    P = \n1 n2 p12 o1 o2 m12 ->
         ∀ (n3 : Nat) (p23 : n2 == n3) (o3 : Obj (FC n3))
         (m23 : Mor3 p23 o2 o3) -> Mor3 (p12 >=> p23) o1 o3


    refl-case : (n : Nat) -> (o1 o2 : Obj (FC n)) (m : Mor3 (reflᵉ n) o1 o2) ->
                P n n refl o1 o2 m
    refl-case = \n o1 o2 m12 n3 p23 o3 m23 -> Mor3-Ind P2 refl-case2 n n3 p23 o2 o3 m23 o1 m12
      where
      P2 = \n2 n3 p23 o2 o3 m23 ->
           (o1 : Obj (FC n2)) -> (m : Mor3 (reflᵉ n2) o1 o2) ->
           Mor3 (refl >=> p23) o1 o3

      refl-case2 : (n : Nat) (o2 o3 : Obj (FC n))
                   (m23 : Mor3 (reflᵉ n) o2 o3)
                   (o1 : Obj (FC n))
                   (m12 : Mor3 (reflᵉ n) o1 o2) ->
                   Mor3 (reflᵉ n >=> reflᵉ n) o1 o3
      refl-case2 n o2 o3 m23 o1 m12 =
        transport (sym (Mor3-refl n o1 o3) >=>
                   (\i -> Mor3 (compPath-sym (reflᵉ n) (~ i)) o1 o3))
          ((transport (Mor3-refl n o1 o2) m12) ⋆⟨ FC n ⟩
           (transport (Mor3-refl n o2 o3) m23))


 {-





  C3 : PreCategoryᴰ (DiscreteC isSetNat) (ℓ-max ℓO ℓM) _
  C3 .PreCategoryᴰ.Objᴰ n = Obj (FC n)
  C3 .PreCategoryᴰ.Morᴰ {n1} {n2} p o1 o2 =
    (FC n2) [ (transport (\i -> (Obj (FC (p i)))) o1) , o2 ]
  C3 .PreCategoryᴰ.idᴰ {n} {o} =
    transport (\i -> (FC n) [ (transportRefl o (~ i)) , o ])
              (id (FC n))
  C3 .PreCategoryᴰ._⋆ᴰ_ {n1} {n2} {n3} {p12} {p23} {o1} {o2} {o3} f1 f2 =
    f1'2 ⋆⟨ FC n3 ⟩ f2
    where
    opaque
      f1' : (FC n3) [ (transport (\i -> (Obj (FC (p23 i)))) (transport (\i -> (Obj (FC (p12 i)))) o1)) ,
                      (transport (\i -> (Obj (FC (p23 i)))) o2) ]
      f1' = transport (\j ->
              (FC (p23 j)) [
                (transport-filler (\i -> (Obj (FC (p23 i)))) (transport (\i -> (Obj (FC (p12 i)))) o1) j) ,
                (transport-filler (\i -> (Obj (FC (p23 i)))) o2 j) ])
              f1

      f1'2 : (FC n3) [ (transport (\i -> (Obj (FC ((p12 >=> p23) i)))) o1) ,
                       (transport (\i -> (Obj (FC (p23 i)))) o2) ]
      f1'2 = transport (\j ->
               (FC n3) [
                 (transport-twice (\i -> (Obj (FC (p23 i)))) (\i -> (Obj (FC (p12 i)))) o1 >=>
                  (\i -> (transport (cong-trans (\o -> (Obj (FC o))) p12 p23 i) o1))) j
                 ,
                 (transport (\i -> (Obj (FC (p23 i)))) o2) ])
               f1'

  C3 .PreCategoryᴰ.⋆ᴰ-left-id {n1} {n2} {p} {o1} {o2} f1 = ans
    where
    comp3 = PreCategoryᴰ._⋆ᴰ_ C3
    idᴰ' = PreCategoryᴰ.idᴰ C3


    check-f1 : (FC n2) [ (transport (\i -> (Obj (FC (p i)))) o1) , o2 ]
    check-f1 = f1

    id-f1 : (FC n2) [ (transport (\i -> (Obj (FC ((refl >=> p) i)))) o1) , o2 ]
    id-f1 = comp3 {n1} {n1} {n2} {refl} {p} (idᴰ' {n1} {o1}) f1

    ans : PathP (\j -> (FC n2) [ (transport (\i -> (Obj (FC (PreCategory.⋆-left-id NC p j i)))) o1) , o2 ])
                id-f1 f1
    ans = ?
-}
