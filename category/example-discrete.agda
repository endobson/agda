{-# OPTIONS --cubical --safe --exact-split #-}

module category.example-discrete where

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


module _ {ℓO : Level} (Ob : Type ℓO) (isSet-Ob : isSet Ob) (magic : Magic) where
  private
    C = DiscreteC (isOfHLevelSuc 2 isSet-Ob)
    module C = PreCategory C

  module _ {ℓOᴰ ℓMᴰ : Level} {S : CategoryᴰSortsP C ℓOᴰ ℓMᴰ} where
    private
      module S = CategoryᴰSortsP S

    CategoryᴰSortsP->CategoryᴰSorts : CategoryᴰSorts C ℓOᴰ ℓMᴰ
    CategoryᴰSortsP->CategoryᴰSorts .CategoryᴰSorts.Objᴰ = S.Objᴰ
    CategoryᴰSortsP->CategoryᴰSorts .CategoryᴰSorts.Morᴰ {a} {b} p c d =
      S.Morᴰ refl (transport (\i -> S.Objᴰ (p i)) c) d

    open CategoryᴰSorts CategoryᴰSortsP->CategoryᴰSorts


    Morᴰ-path : {a : Obj C} (f : C [ a , a ]) (c : Objᴰ a) (d : Objᴰ a) ->
                     S.Morᴰ f c d == Morᴰ f c d
    Morᴰ-path {a} f c d =
      transport (\i -> S.Morᴰ (fp (~ i)) c d == Morᴰ (fp (~ i)) c d) (Morᴰ-path-id c d)
      where
      fp : f == id C
      fp = isSet-Ob a a f (id C)

      Morᴰ-path-id : {a : Obj C} (c : Objᴰ a) (d : Objᴰ a) ->
                  S.Morᴰ (id C) c d == Morᴰ (id C) c d
      Morᴰ-path-id {a} c d = \j -> S.Morᴰ refl (cp j) d
        where
        p = (idᵉ C a)

        cp : c == transport (\i -> Objᴰ (p i)) c
        cp = transport-filler (\i -> Objᴰ (p i)) c


    Morᴰ-path' : {a b : Obj C} (p : C [ a , b ]) (c : Objᴰ a) (d : Objᴰ b) ->
                 Morᴰ p c d ==
                 Morᴰ refl (transport (\i -> Objᴰ (p i)) c) d
    Morᴰ-path' {a} {b} p c d =
      \j -> Morᴰ (\i -> p (i ∨ j)) (transport-filler (\i -> Objᴰ (p (i ∧ j))) c j) d


    Morᴰ-path'-refl :
      {a : Obj C} (c : Objᴰ a) (d : Objᴰ a) ->
      PathP (\i -> Morᴰ refl c d == Morᴰ refl (transport-filler (\i -> Objᴰ a) c (~ i)) d)
            (Morᴰ-path' refl c d) refl
    Morᴰ-path'-refl {a} c d = magic


    Morᴰ-path'-rev : {a b : Obj C} (p : C [ a , b ]) (c : Objᴰ a) (d : Objᴰ b) ->
                 Morᴰ p c d ==
                 Morᴰ refl c (transport (\i -> Objᴰ (p (~ i))) d)
    Morᴰ-path'-rev {a} {b} p c d =
      \j -> Morᴰ (\i -> p (i ∧ (~ j))) c (transport-filler (\i -> Objᴰ (p (~ i ∨ ~ j))) d j)

    Morᴰ-path'-both :
      {a b c : Obj C} (p : C [ a , b ]) (q : C [ b , c ])
      (a' : Objᴰ a) (c' : Objᴰ c) ->
      Morᴰ (p >=> q) a' c' ==
      Morᴰ (refl >=> refl) (transport (\i -> Objᴰ (p i)) a') (transport (\i -> Objᴰ (q (~ i))) c')
    Morᴰ-path'-both {a} {b} {c} p q a' c' =
      \j -> Morᴰ ((\i -> p (i ∨ j)) >=> (\i -> q (i ∧ (~ j))))
                 (transport-filler (\i -> Objᴰ (p (i ∧ j))) a' j)
                 (transport-filler (\i -> Objᴰ (q (~ i ∨ ~ j))) c' j)

    lower-left : {a b : Obj C} {p : C [ a , b ]} {c : Objᴰ a} {d : Objᴰ b} ->
                 Morᴰ p c d ->
                 S.Morᴰ refl (transport (\i -> Objᴰ (p i)) c) d
    lower-left {a} {b} {p} {c} {d} =
      transport (Morᴰ-path' p c d >=> sym (Morᴰ-path refl _ _))

    lower-right : {a b : Obj C} {p : C [ a , b ]} {c : Objᴰ a} {d : Objᴰ b} ->
                 Morᴰ p c d ->
                 S.Morᴰ refl c (transport (\i -> Objᴰ (p (~ i))) d)
    lower-right {a} {b} {p} {c} {d} =
      transport (Morᴰ-path'-rev p c d >=> sym (Morᴰ-path refl _ _))

    lower-both : {a b c : Obj C} {p : C [ a , b ]} {q : C [ b , c ]}
                 {a' : Objᴰ a} {c' : Objᴰ c} ->
                 Morᴰ (p >=> q) a' c' ->
                 S.Morᴰ (refl >=> refl) (transport (\i -> Objᴰ (p i)) a')
                                        (transport (\i -> Objᴰ (q (~ i))) c')
    lower-both {a} {b} {c} {p} {q} {a'} {c'} =
      transport (Morᴰ-path'-both p q a' c' >=> sym (Morᴰ-path _ _ _))

    raise-both : {a b c : Obj C} {p : C [ a , b ]} {q : C [ b , c ]}
                 {a' : Objᴰ a} {c' : Objᴰ c} ->
                 S.Morᴰ (refl >=> refl) (transport (\i -> Objᴰ (p i)) a')
                                        (transport (\i -> Objᴰ (q (~ i))) c') ->
                 Morᴰ (p >=> q) a' c'
    raise-both {a} {b} {c} {p} {q} {a'} {c'} =
      transport (sym (Morᴰ-path'-both p q a' c' >=> sym (Morᴰ-path _ _ _)))

    lower-raise-both :
      {a b c : Obj C} (p : C [ a , b ]) (q : C [ b , c ])
      (a' : Objᴰ a) (c' : Objᴰ c) ->
      (m : S.Morᴰ (refl >=> refl) (transport (\i -> Objᴰ (p i)) a')
                                  (transport (\i -> Objᴰ (q (~ i))) c')) ->
      (lower-both (raise-both m)) == m
    lower-raise-both = magic

    lower-id : {a : Obj C} {p : C [ a , a ]} {c : Objᴰ a} {d : Objᴰ a} ->
               Morᴰ p c d ->
               S.Morᴰ p c d
    lower-id = transport (sym (Morᴰ-path _ _ _))



    module _ (O : CategoryᴰOpsP S) where
      private
        module O = CategoryᴰOpsP O

      Σcomp : {a b c : Obj C} {f : C [ a , b ]} {g : C [ b , c ]}
              {a' : Objᴰ a} {b' : Objᴰ b} {c' : Objᴰ c}
              (f' : Morᴰ f a' b') (g' : Morᴰ g b' c') ->
              Σ[ fg' ∈ Morᴰ (f >=> g) a' c' ] (lower-both fg' == lower-left f' O.⋆ᴰ lower-right g')
      Σcomp {a} {b} {c} {f} {g} {a'} {b'} {c'} f' g' =
        raise-both fg'2 ,
        lower-raise-both _ _ _ _ fg'2
        where

        fg'2 : S.Morᴰ (refl >=> refl) (transport (\i -> Objᴰ (f i)) a')
                                      (transport (\i -> Objᴰ (g (~ i))) c')
        fg'2 = lower-left f' O.⋆ᴰ lower-right g'



      CategoryᴰOpsP->CategoryᴰOps : CategoryᴰOps CategoryᴰSortsP->CategoryᴰSorts
      CategoryᴰOpsP->CategoryᴰOps .CategoryᴰOps.idᴰ {c} {d} =
        transport (Morᴰ-path (id C) d d) O.idᴰ
      CategoryᴰOpsP->CategoryᴰOps .CategoryᴰOps._⋆ᴰ_ f' g' = fst (Σcomp f' g')

      private
        module O2 = CategoryᴰOps CategoryᴰOpsP->CategoryᴰOps

      module _ (L : CategoryᴰLawsP O) where
        private
          module L = CategoryᴰLawsP L

   --     CategoryᴰLawsP->CategoryᴰLaws : CategoryᴰLaws CategoryᴰOpsP->CategoryᴰOps
   --     CategoryᴰLawsP->CategoryᴰLaws .CategoryᴰLaws.⋆ᴰ-left-id
   --       {s} {t} {f} {s'} {t'} f' = magic
   --       where
   --       t'2 = (transport (\i -> Objᴰ (f (~ i))) t')

   --       f'2 : S.Morᴰ refl s' t'2
   --       f'2 = lower-right f'

   --       id' : S.Morᴰ refl s' s'
   --       id' = O.idᴰ

   --       id'2 : Morᴰ refl s' s'
   --       id'2 = O2.idᴰ

   --       id-path : PathP (\i -> S.Morᴰ refl (transport-filler refl s' (~ i)) s')
   --                       (lower-left O2.idᴰ) O.idᴰ
   --       id-path = magic
   --         where
   --         check : (lower-left O2.idᴰ) ==
   --                 (transport (Morᴰ-path' refl s' s' >=> sym (Morᴰ-path refl _ _))
   --                   (transport (Morᴰ-path (id C) s' s') O.idᴰ))
   --         check = refl





   --       id-f : PathP (\i -> S.Morᴰ (C.⋆-left-id refl i) s' t'2) (id' O.⋆ᴰ f'2) f'2
   --       id-f = L.⋆ᴰ-left-id f'2

   --       test-p : (id'2 O2.⋆ᴰ f') == raise-both ((lower-left O2.idᴰ) O.⋆ᴰ (lower-right f'))
   --       test-p = magic

   --       -- id-f' : PathP (\i -> Morᴰ (C.⋆-left-id refl i) s' t'2) (id' O.⋆ᴰ f'2) f'2
   --       -- id-f' = transport
   --       --           (\j -> PathP (\i -> Morᴰ-path (C.⋆-left-id refl i) s' t'2 j) (id' O.⋆ᴰ f'2) f'2)
   --       --           id-f
