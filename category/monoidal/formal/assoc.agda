{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.assoc where

open import base
open import category.base
open import category.monoidal.base
open import category.monoidal.formal.base
open import category.monoidal.formal.directed
open import relation
open import order
open import order.instances.nat
open import equality


isAssocMor : {a b : WObj} -> Pred (BasicMor a b) ℓ-zero
isAssocMor m = isDirectedMor m ⊎ isDirectedMor (invert-bm m)

AssocMor : (a b : WObj) -> Type ℓ-zero
AssocMor a b = Σ (BasicMor a b) isAssocMor

isAssocPath : {a b : WObj} -> Pred (BasicPath a b) ℓ-zero
isAssocPath (empty p) = Top
isAssocPath (m :: p) = isAssocMor m × isAssocPath p

AssocPath : (a b : WObj) -> Type ℓ-zero
AssocPath a b = Σ (BasicPath a b) isAssocPath

assoc-mor->length= : {o1 o2 : WObj} -> AssocMor o1 o2 -> WObj-length o1 == WObj-length o2
assoc-mor->length= (m , inj-l dm) = dirmor->length= (m , dm)
assoc-mor->length= (m , inj-r dm) = sym (dirmor->length= (invert-bm m , dm))

assoc-path->length= : {o1 o2 : WObj} -> AssocPath o1 o2 -> WObj-length o1 == WObj-length o2
assoc-path->length= (empty p , _) = cong WObj-length p
assoc-path->length= (m :: p , (am , ap)) =
  assoc-mor->length= (m , am) >=> assoc-path->length= (p , ap)


module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open InMonoidal MC obj
  open InMonoidalDir MC obj

  assoc-path->mor : {a b : WObj} -> AssocPath a b -> C [ inj₀ a , inj₀ b ]
  assoc-path->mor (p , _) = basic-path->mor p

  am->mor : {a b : WObj} -> AssocMor a b -> C [ inj₀ a , inj₀ b ]
  am->mor (m , _)= basic-mor->mor m



  private
    cases : {o1 o2 : WObj} -> (p : BasicPath o1 o2) -> (ap : isAssocPath p) ->
            isεFree o1 -> isCanon o2 ->
            Σ[ dp ∈ DirectedPath o1 o2 ] (directed-path->mor dp == basic-path->mor p)
    cases (empty p) tt _ _ = (empty p , tt) , refl
    cases {o1} {o2} (m :: p) (inj-l dm , ap) εF-o1 c-o2 =
      let (dp2 , ap2) = cases p ap (dirmor-preserves-isεFree (m , dm) εF-o1) c-o2 in
      cons-dirmor (m , dm) dp2 , ⋆-right ap2
    cases {o1} {o2} (_::_ {om} m p) (inj-r dm' , ap) εF-o1 c-o2 =
      mid-canon-path , proof
      where
      fp : AssocPath o1 o2
      fp = (m :: p) , (inj-r dm' , ap)

      εF-om : isεFree om
      εF-om = (dirmor-reflects-isεFree (invert-bm m , dm') εF-o1)

      rec : Σ[ dp ∈ DirectedPath om o2 ] (directed-path->mor dp == assoc-path->mor (p , ap))
      rec = cases p ap εF-om c-o2

      lp : WObj-length o1 == WObj-length o2
      lp = assoc-path->length= fp

      mid-canon-path : DirectedPath o1 o2
      mid-canon-path = dirpath-to-isCanon o1 o2 εF-o1 c-o2 lp

      mid-path2 : DirectedPath om o2
      mid-path2 = cons-dirmor (invert-bm m , dm') mid-canon-path

      mid-path2-path : directed-path->mor mid-path2 == directed-path->mor (fst rec)
      mid-path2-path = parallel-dirpaths-to-canon om o2 εF-om c-o2 mid-path2 (fst rec)

      inverses : AreInverses C (basic-mor->mor m) (basic-mor->mor (invert-bm m))
      inverses = AreInverses-invert-bm m

      proof : directed-path->mor mid-canon-path == assoc-path->mor fp
      proof =
        sym ⋆-left-id >=>
        ⋆-left (sym (proj₁ inverses)) >=>
        ⋆-assoc >=>
        ⋆-right (mid-path2-path >=> snd rec)



  private
    P : Pred WObj _
    P o1 = (o2 : WObj) -> (isεFree o1) -> (isCanon o2) ->
           (m1 m2 : AssocPath o1 o2) ->
           (assoc-path->mor m1 == assoc-path->mor m2)
  parallel-assoc-paths-to-canon : ∀ o -> P o
  parallel-assoc-paths-to-canon o1 o2 εF-o1 c-o2 (p1 , ap1) (p2 , ap2) =
    sym (snd rec1) >=> parallel-dirpaths-to-canon o1 o2 εF-o1 c-o2 (fst rec1) (fst rec2) >=> (snd rec2)
    where
    rec1 : Σ[ dp ∈ DirectedPath o1 o2 ] (directed-path->mor dp == basic-path->mor p1)
    rec1 = cases p1 ap1 εF-o1 c-o2
    rec2 : Σ[ dp ∈ DirectedPath o1 o2 ] (directed-path->mor dp == basic-path->mor p2)
    rec2 = cases p2 ap2 εF-o1 c-o2
