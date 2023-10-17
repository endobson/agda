{-# OPTIONS --cubical --safe --exact-split #-}

open import base
open import category.adjunction
open import category.base
open import cubical
open import category.bicategory.cat
open import category.constructions.functor-cat
open import category.constructions.opposite
open import category.constructions.functor-cat.univalent
open import category.functor
open import category.isomorphism
open import category.natural-isomorphism
open import category.natural-transformation
open import category.univalent
open import equality-path
open import equality.identity-system
open import equivalence
open import isomorphism renaming (iso to cons-iso)
open import hlevel
open import sigma
open import sigma.base

module category.adjunction.unique where

private
  module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD}
           {L : Functor C D}
    where
    private
      module C = CategoryHelpers C
      module D = CategoryHelpers D
      module L = Functor L
    module _ where

      module _ {R1 R2 : Functor D C} (a1 : Adjunction L R1) (a2 : Adjunction L R2) where
        private
          module R1 = Functor R1
          module R2 = Functor R2
          module a1 = Adjunction a1
          module a2 = Adjunction a2

        adj-mor : (d : Obj D) -> C [ R1.obj d , R2.obj d ]
        adj-mor d = a2.unit.obj (R1.obj d) ⋆⟨ C ⟩ R2.mor (a1.counit.obj d)

      module _ {R1 R2 : Functor D C} (a1 : Adjunction L R1) (a2 : Adjunction L R2) where
        private
          module R1 = Functor R1
          module R2 = Functor R2
          module a1 = Adjunction a1
          module a2 = Adjunction a2

        opaque
          adj-mor-inv : (d : Obj D) -> adj-mor a1 a2 d ⋆⟨ C ⟩ adj-mor a2 a1 d == id C
          adj-mor-inv d =
            begin
              (a2.unit.obj (R1.obj d) ⋆ R2.mor (a1.counit.obj d)) ⋆
              (a1.unit.obj (R2.obj d) ⋆ R1.mor (a2.counit.obj d))
            ==< ⋆-assoc >=> ⋆-right (sym ⋆-assoc) >
              a2.unit.obj (R1.obj d) ⋆
              ((R2.mor (a1.counit.obj d) ⋆ a1.unit.obj (R2.obj d)) ⋆
               R1.mor (a2.counit.obj d))
            ==< ⋆-right (⋆-left (sym (a1.unit.mor _))) >
              a2.unit.obj (R1.obj d) ⋆
              ((a1.unit.obj (R2.obj (L.obj (R1.obj d))) ⋆
                R1.mor (L.mor (R2.mor (a1.counit.obj d)))) ⋆
               R1.mor (a2.counit.obj d))
            ==< ⋆-right ⋆-assoc >=> sym ⋆-assoc >
              (a2.unit.obj (R1.obj d) ⋆ a1.unit.obj (R2.obj (L.obj (R1.obj d)))) ⋆
              (R1.mor (L.mor (R2.mor (a1.counit.obj d))) ⋆ R1.mor (a2.counit.obj d))
            ==< ⋆-right (sym (R1.⋆ _ _)) >
              (a2.unit.obj (R1.obj d) ⋆ a1.unit.obj (R2.obj (L.obj (R1.obj d)))) ⋆
              (R1.mor (L.mor (R2.mor (a1.counit.obj d)) ⋆⟨ D ⟩ a2.counit.obj d))
            ==< ⋆-right (cong R1.mor (sym (a2.counit.mor _)) >=> R1.⋆ _ _) >
              (a2.unit.obj (R1.obj d) ⋆ a1.unit.obj (R2.obj (L.obj (R1.obj d)))) ⋆
              (R1.mor (a2.counit.obj (L.obj (R1.obj d))) ⋆
               R1.mor (a1.counit.obj d))
            ==< sym ⋆-assoc >
              ((a2.unit.obj (R1.obj d) ⋆ a1.unit.obj (R2.obj (L.obj (R1.obj d)))) ⋆
               R1.mor (a2.counit.obj (L.obj (R1.obj d)))) ⋆
              R1.mor (a1.counit.obj d)
            ==< ⋆-left (⋆-left (sym (a1.unit.mor _))) >
              ((a1.unit.obj (R1.obj d) ⋆
                R1.mor (L.mor (a2.unit.obj (R1.obj d)))) ⋆
               R1.mor (a2.counit.obj (L.obj (R1.obj d)))) ⋆
              R1.mor (a1.counit.obj d)
            ==< ⋆-left (⋆-assoc >=> ⋆-right (sym (R1.⋆ _ _))) >
              (a1.unit.obj (R1.obj d) ⋆
               (R1.mor (L.mor (a2.unit.obj (R1.obj d)) ⋆⟨ D ⟩
                        a2.counit.obj (L.obj (R1.obj d))))) ⋆
              R1.mor (a1.counit.obj d)
            ==< ⋆-left (⋆-right (cong R1.mor (a2.tri-L _))) >
              (a1.unit.obj (R1.obj d) ⋆ (R1.mor (id D))) ⋆ R1.mor (a1.counit.obj d)
            ==< ⋆-left (⋆-right (cong R1.mor (sym (L.id _))) >=> (a1.unit.mor _)) >
              (id C ⋆ a1.unit.obj (R1.obj d)) ⋆ R1.mor (a1.counit.obj d)
            ==< ⋆-left ⋆-left-id >
              (a1.unit.obj (R1.obj d)) ⋆⟨ C ⟩ (R1.mor (a1.counit.obj d))
            ==< a1.tri-R d >
              id C
            end
            where
            open C
            open EqReasoning

      module _ {R1 R2 : Functor D C} (a1 : Adjunction L R1) (a2 : Adjunction L R2) where
        private
          module R1 = Functor R1
          module R2 = Functor R2
          module a1 = Adjunction a1
          module a2 = Adjunction a2

        opaque
          adj-mor-unit : (c : Obj C) -> a1.unit.obj c ⋆⟨ C ⟩ adj-mor a1 a2 (L.obj c) == a2.unit.obj c
          adj-mor-unit c =
            sym ⋆-assoc >=>
            ⋆-left (sym (a2.unit.mor _)) >=>
            ⋆-assoc >=>
            ⋆-right (sym (R2.⋆ _ _) >=> cong R2.mor (a1.tri-L _) >=> R2.id _) >=>
            ⋆-right-id
            where
            open C

          adj-mor-counit : (d : Obj D) -> L.mor (adj-mor a1 a2 d) ⋆⟨ D ⟩ a2.counit.obj d == a1.counit.obj d
          adj-mor-counit d =
            ⋆-left (L.⋆ _ _) >=>
            ⋆-assoc >=>
            ⋆-right (sym (a2.counit.mor _)) >=>
            sym ⋆-assoc >=>
            ⋆-left (a2.tri-L _) >=>
            ⋆-left-id
            where
            open D

    isomorphic-right-Adjoints :
      {R1 R2 : Functor D C} ->
      (Adjunction L R1) -> (Adjunction L R2) ->
      NaturalIsomorphism R1 R2
    isomorphic-right-Adjoints {R1} {R2} a1 a2 =
      record { obj = obj ; mor = mor } ,
      \o -> record { inv = inv o ; sec = inv⋆obj o ; ret = obj⋆inv o }
      where
      module R1 = Functor R1
      module R2 = Functor R2
      module a1 = Adjunction a1
      module a2 = Adjunction a2

      obj : (d : Obj D) -> C [ R1.obj d , R2.obj d ]
      obj = adj-mor a1 a2
      inv : (d : Obj D) -> C [ R2.obj d , R1.obj d ]
      inv = adj-mor a2 a1
      obj⋆inv : (d : Obj D) -> obj d ⋆⟨ C ⟩ inv d == id C
      obj⋆inv = adj-mor-inv a1 a2
      inv⋆obj : (d : Obj D) -> inv d ⋆⟨ C ⟩ obj d == id C
      inv⋆obj = adj-mor-inv a2 a1

      opaque
        mor : {d1 d2 : Obj D} -> (m : D [ d1 , d2 ]) ->
              obj d1 ⋆⟨ C ⟩ R2.mor m == R1.mor m ⋆⟨ C ⟩ obj d2
        mor {d1} {d2} m =
          begin
            (a2.unit.obj (R1.obj d1) ⋆ R2.mor (a1.counit.obj d1)) ⋆ R2.mor m
          ==< ⋆-assoc >=> ⋆-right (sym (R2.⋆ _ _)) >
            a2.unit.obj (R1.obj d1) ⋆ (R2.mor (a1.counit.obj d1 ⋆⟨ D ⟩ m))
          ==< ⋆-right (cong R2.mor (a1.counit.mor m)) >
            a2.unit.obj (R1.obj d1) ⋆ (R2.mor (L.mor (R1.mor m) ⋆⟨ D ⟩ a1.counit.obj d2))
          ==< ⋆-right (R2.⋆ _ _) >=> sym ⋆-assoc >
            (a2.unit.obj (R1.obj d1) ⋆ R2.mor (L.mor (R1.mor m))) ⋆ (R2.mor (a1.counit.obj d2))
          ==< ⋆-left (a2.unit.mor (R1.mor m)) >=> ⋆-assoc >
            R1.mor m ⋆ (a2.unit.obj (R1.obj d2) ⋆ R2.mor (a1.counit.obj d2))
          end
          where
          open C
          open EqReasoning


private
  module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD} where
    op-Adjunction : {L : Functor C D} {R : Functor D C} ->
                    Adjunction L R -> Adjunction (opF R) (opF L)
    op-Adjunction {L} {R} a = record
      { unit = unit
      ; counit = counit
      ; tri-L = a.tri-R
      ; tri-R = a.tri-L
      }
      where
      module a = Adjunction a

      unit : NaturalTransformation (idF (OpCat D)) (opF R ⋆F opF L)
      unit = record
        { obj = NT-obj (opNT a.counit)
        ; mor = NT-mor (opNT a.counit)
        }

      counit : NaturalTransformation (opF L ⋆F opF R) (idF (OpCat C))
      counit = record
        { obj = NT-obj (opNT a.unit)
        ; mor = NT-mor (opNT a.unit)
        }

  module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD}  where

    LeftAdjoint≃RightAdjoint : {G : Functor D C} ->
      (Σ[ F ∈ Functor C D ] (Adjunction F G)) ≃
      (Σ[ F' ∈ Functor (OpCat C) (OpCat D) ] (Adjunction (opF G) F'))
    LeftAdjoint≃RightAdjoint {G} = isoToEquiv (cons-iso forward backward (\_ -> refl) (\_ -> refl))
      where
      forward : (Σ[ F ∈ Functor C D ] (Adjunction F G)) ->
                (Σ[ F' ∈ Functor (OpCat C) (OpCat D) ] (Adjunction (opF G) F'))
      forward (F , a) = opF F , op-Adjunction a
      backward : (Σ[ F' ∈ Functor (OpCat C) (OpCat D) ] (Adjunction (opF G) F')) ->
                 (Σ[ F ∈ Functor C D ] (Adjunction F G))
      backward (F' , a) = opF F' , op-Adjunction a

    module _ {L : Functor C D} {R1 : Functor D C} {R2 : Functor D C}
             (a1 : Adjunction L R1) (a2 : Adjunction L R2) where
      private
        module a1 = Adjunction a1
        module a2 = Adjunction a2
      record AdjunctionConversionʳ : Type (ℓ-max* 4 ℓOC ℓMC ℓOD ℓMD) where
        field
          iso : NaturalIsomorphism R1 R2

        nt : NaturalTransformation R1 R2
        nt = fst iso

        nt' : NaturalTransformation R2 R1
        nt' = fst (flip-NI iso)

        field
          unit : a1.unit ⋆NT (L NT◀ nt) == a2.unit
          counit : (nt NT▶ L) ⋆NT a2.counit == a1.counit

        module nt = NaturalTransformation nt
        module nt' = NaturalTransformation nt'

        opaque
          unit' : a2.unit ⋆NT (L NT◀ nt') == a1.unit
          unit' =
            (\i -> unit (~ i) ⋆NT (L NT◀ nt')) >=>
            ⋆NT-assoc a1.unit (L NT◀ nt) (L NT◀ nt') >=>
            cong (a1.unit ⋆NT_) p >=>
            ⋆NT-right-id a1.unit

            where
            p : (L NT◀ nt) ⋆NT (L NT◀ nt') == id-NT (L ⋆F R1)
            p = natural-transformation-path (\c -> isIso.ret (snd iso _))

          counit' : (nt' NT▶ L) ⋆NT a1.counit == a2.counit
          counit' =
            (\i -> (nt' NT▶ L) ⋆NT counit (~ i)) >=>
            sym (⋆NT-assoc (nt' NT▶ L) (nt NT▶ L) a2.counit)>=>
            cong (_⋆NT a2.counit) p >=>
            ⋆NT-left-id a2.counit

            where
            p : (nt' NT▶ L) ⋆NT (nt NT▶ L) == id-NT (R2 ⋆F L)
            p = natural-transformation-path (\c ->
              sym (F-⋆ L _ _) >=>
              cong (F-mor L) (isIso.sec (snd iso _)) >=>
              F-id L _)

    module _ {L : Functor C D} {R1 : Functor D C} {R2 : Functor D C}
             {a1 : Adjunction L R1} {a2 : Adjunction L R2}
             {c1 c2 : AdjunctionConversionʳ a1 a2} where
      private
        module a1 = Adjunction a1
        module a2 = Adjunction a2
        module c1 = AdjunctionConversionʳ c1
        module c2 = AdjunctionConversionʳ c2

      opaque
        adjunction-conversion-path :
          ((d : Obj D) -> NT-obj c1.nt d == NT-obj c2.nt d) -> c1 == c2
        adjunction-conversion-path fp = \i -> record
          { iso = nt-i i
          ; unit = unit i
          ; counit = counit i
          }
          where
          nt-p : c1.nt == c2.nt
          nt-p = natural-transformation-path fp

          nt-i : c1.iso == c2.iso
          nt-i = ΣProp-path (\{nt} -> isProp-isNaturalIso R1 R2 {nt}) nt-p

          unit : PathP (\i -> a1.unit ⋆NT (L NT◀ nt-p i) == a2.unit) c1.unit c2.unit
          unit = isProp->PathP (\i -> (isSet-NaturalTransformation _ _))

          counit : PathP (\i -> (nt-p i NT▶ L) ⋆NT a2.counit == a1.counit) c1.counit c2.counit
          counit = isProp->PathP (\i -> (isSet-NaturalTransformation _ _))


module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD}
         {L : Functor C D}
  where
  private
    module _ {R1 R2 : Functor D C} (a1 : Adjunction L R1) (a2 : Adjunction L R2) where
      right-conversion : AdjunctionConversionʳ a1 a2
      right-conversion = record
        { iso = isomorphic-right-Adjoints a1 a2
        ; unit = natural-transformation-path (adj-mor-unit a1 a2)
        ; counit = natural-transformation-path (adj-mor-counit a1 a2)
        }

      opaque
        isProp-conversion : isProp (AdjunctionConversionʳ a1 a2)
        isProp-conversion c1 c2 = adjunction-conversion-path obj-path
          where
          module a1 = Adjunction a1
          module a2 = Adjunction a2
          module c1 = AdjunctionConversionʳ c1
          module c2 = AdjunctionConversionʳ c2
          module L = Functor L
          module R1 = Functor R1
          module R2 = Functor R2

          --  This natural trasformation can reduce to both c1.nt ⋆ c2.nt'
          --  via the a2 triangle, but also to id via the a1 triangle.
          --
          --  +-------------------+
          --  | c1.nt ▶    idF    |
          --  |-------------------|
          --  |  R2  ◀   a2.unit  |
          --  |-------------------|
          --  | a2.counit  ▶  R2  |
          --  |-------------------|
          --  |   idF    ◀ c2.nt' |
          --  +-------------------+

          obj-path : (d : Obj D) -> NT-obj c1.nt d == NT-obj c2.nt d
          obj-path d = path
            where
            nt1 : NaturalTransformation (R1 ⋆F (idF C)) (R2 ⋆F (idF C))
            nt1 = (c1.nt NT▶ (idF C))

            nt2 : NaturalTransformation (R2 ⋆F (idF C)) ((idF D) ⋆F R2)
            nt2 = (R2 NT◀ a2.unit) ⋆NT (⋆F-assoc-NT' R2 L R2 ⋆NT (a2.counit NT▶ R2))

            nt3 : NaturalTransformation ((idF D) ⋆F R2) ((idF D) ⋆F R1)
            nt3 = ((idF D) NT◀ c2.nt')

            nt123 : NaturalTransformation (R1 ⋆F (idF C)) ((idF D) ⋆F R1)
            nt123 = nt1 ⋆NT (nt2 ⋆NT nt3)

            nt1-obj : NT-obj nt1 d == NT-obj c1.nt d
            nt1-obj = refl

            nt2-obj : NT-obj nt2 d == id C
            nt2-obj = ⋆-right ⋆-left-id >=> a2.tri-R d
              where
              open CategoryHelpers C

            nt3-obj : NT-obj nt3 d == NT-obj c2.nt' d
            nt3-obj = refl

            nt123-obj : NT-obj nt123 d == (NT-obj c1.nt d ⋆⟨ C ⟩ NT-obj c2.nt' d)
            nt123-obj = ⋆-right (⋆-left nt2-obj >=> ⋆-left-id)
              where
              open CategoryHelpers C

            nt123-obj' : NT-obj nt123 d == id C
            nt123-obj' =
              begin
               c1.nt.obj d ⋆ ((a2.unit.obj (R2.obj d) ⋆ (id C ⋆ (R2.mor (a2.counit.obj d)))) ⋆
                              c2.nt'.obj d)
              ==< ⋆-right (⋆-left (⋆-right ⋆-left-id)) >
               c1.nt.obj d ⋆ ((a2.unit.obj (R2.obj d) ⋆ (R2.mor (a2.counit.obj d))) ⋆ c2.nt'.obj d)
              ==< ⋆-right ⋆-assoc >=> sym ⋆-assoc >
               (c1.nt.obj d ⋆ a2.unit.obj (R2.obj d)) ⋆ (R2.mor (a2.counit.obj d) ⋆ c2.nt'.obj d)
              ==< ⋆-left (sym (a2.unit.mor _)) >
               (a2.unit.obj (R1.obj d) ⋆ (R2.mor (L.mor (c1.nt.obj d)))) ⋆
               (R2.mor (a2.counit.obj d) ⋆ c2.nt'.obj d)
              ==< ⋆-assoc >=>
                  ⋆-right (sym ⋆-assoc >=>
                           ⋆-left (sym (R2.⋆ _ _) >=>
                                   (\i -> R2.mor (NT-obj (c1.counit i) d)))) >
               a2.unit.obj (R1.obj d) ⋆ (R2.mor (a1.counit.obj d) ⋆ c2.nt'.obj d)
              ==< ⋆-right (sym (c2.nt'.mor _)) >
               a2.unit.obj (R1.obj d) ⋆ (c2.nt'.obj (L.obj (R1.obj d)) ⋆ R1.mor (a1.counit.obj d))
              ==< sym ⋆-assoc >=> ⋆-left (\i -> NT-obj (c2.unit' i) (R1.obj d)) >
               a1.unit.obj (R1.obj d) ⋆ R1.mor (a1.counit.obj d)
              ==< a1.tri-R d >
               id C
              end
              where
              open CategoryHelpers C
              open EqReasoning

            path : NT-obj c1.nt d == NT-obj c2.nt d
            path =
              sym ⋆-right-id >=>
              ⋆-right (sym (isIso.sec (snd c2.iso _))) >=>
              sym ⋆-assoc >=>
              ⋆-left (sym nt123-obj >=> nt123-obj') >=>
              ⋆-left-id
              where
              open CategoryHelpers C

      isContr-AdjunctionConversionʳ : isContr (AdjunctionConversionʳ a1 a2)
      isContr-AdjunctionConversionʳ = right-conversion , isProp-conversion right-conversion

  module _ (univC : isUnivalent' C) where

    module _ {R1 R2 : Functor D C} {a1 : Adjunction L R1} {a2 : Adjunction L R2}
             (rc : AdjunctionConversionʳ a1 a2) where
      private
        FC = FunctorC D C
        open isIdentitySystem
        module rc = AdjunctionConversionʳ (right-conversion a1 a2)
        module a1 = Adjunction a1
        module a2 = Adjunction a2

        ni : CatIso FC R1 R2
        ni = eqFun ΣIso≃CatIso (eqInv (existential-eq (\_ -> (isNaturalIso'≃isNaturalIso _ _))) rc.iso)

        rp : R1 == R2
        rp = isUnivalent-FunctorC univC .to-path ni

        rp2 : PathP (\i -> CatIso FC R1 (rp i)) (idCatIso FC R1) ni
        rp2 = isUnivalent-FunctorC univC .to-path-over ni

        opaque
          unit-p : PathP (\i -> NaturalTransformation (idF C) (L ⋆F (rp i))) a1.unit a2.unit
          unit-p =
            transP-mid
              (sym (⋆NT-right-id a1.unit))
              (\i -> a1.unit ⋆NT (L NT◀ (CatIso.mor (rp2 i))))
              rc.unit

          counit-p : PathP (\i -> NaturalTransformation ((rp i) ⋆F L) (idF D)) a1.counit a2.counit
          counit-p =
            transP-mid
              (sym (⋆NT-left-id a1.counit) >=>
               DD.⋆-left (natural-transformation-path (\_ -> sym (F-id L _))))
              (\i -> (CatIso.inv (rp2 i) NT▶ L) ⋆NT a1.counit)
              (DD.⋆-left (natural-transformation-path (\c -> refl)) >=> rc.counit')
            where
            module DD = CategoryHelpers (FunctorC D D)

          triL-p :
            ∀ (c : Obj C) ->
            PathP (\i -> (NT-obj (unit-p i NT▶ L) c) ⋆⟨ D ⟩
                         (NT-obj (L NT◀ counit-p i) c) == id D)
              (a1.tri-L c) (a2.tri-L c)
          triL-p c = isProp->PathP (\_ -> isSet-Mor D _ _)

          triR-p :
            ∀ (d : Obj D) ->
            PathP (\i -> (NT-obj (rp i NT◀ unit-p i) d) ⋆⟨ C ⟩
                         (NT-obj (counit-p i NT▶ rp i) d) == id C)
              (a1.tri-R d) (a2.tri-R d)
          triR-p d = isProp->PathP (\_ -> isSet-Mor C _ _)

      opaque
        base-path : R1 == R2
        base-path i = rp i

        over-path : PathP (\i -> Adjunction L (base-path i)) a1 a2
        over-path i .Adjunction.unit    = unit-p i
        over-path i .Adjunction.counit  = counit-p i
        over-path i .Adjunction.tri-L c = triL-p c i
        over-path i .Adjunction.tri-R d = triR-p d i

    isProp-RightAdjoint : isProp (Σ (Functor D C) (Adjunction L))
    isProp-RightAdjoint (_ , a1) (_ , a2) = \i -> base-path rc i , over-path rc i
      where
      rc : AdjunctionConversionʳ a1 a2
      rc = (right-conversion a1 a2)

module _ {ℓOC ℓMC ℓOD ℓMD : Level} {C : PreCategory ℓOC ℓMC} {D : PreCategory ℓOD ℓMD} where
  isProp-LeftAdjoint :
    {R : Functor D C} (univ : isUnivalent' D) -> isProp (Σ[ L ∈ Functor C D ] (Adjunction L R))
  isProp-LeftAdjoint univ =
    ≃-isProp (equiv⁻¹ LeftAdjoint≃RightAdjoint) (isProp-RightAdjoint (isUnivalent-OpCat univ))
