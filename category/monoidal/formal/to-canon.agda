{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.to-canon where

open import base
open import additive-group
open import additive-group.instances.nat
open import category.base
open import category.isomorphism
open import category.monoidal.base
open import category.monoidal.formal.base
open import category.monoidal.formal.clean
open import category.monoidal.formal.clean-mor
open import category.monoidal.formal.directed
open import category.monoidal.formal.factor
open import category.monoidal.formal.factor2
open import category.monoidal.formal.isomorphism
open import relation
open import order
open import sum
open import order.instances.nat
open import equality-path


MorDirection : {a b : WObj} -> Pred (BasicMor a b) ℓ-zero
MorDirection m = isForwardMor m ⊎ isForwardMor (invert-bm m)

PathDirections : {a b : WObj} -> Pred (BasicPath a b) ℓ-zero
PathDirections (empty _) = Top
PathDirections (m :: p) = MorDirection m × PathDirections p


decide-direction : {a b : WObj} -> (m : BasicMor a b) -> MorDirection m
decide-direction (α⇒' _ _ _) = inj-l tt
decide-direction (λ⇒' _) = inj-l tt
decide-direction (ρ⇒' _) = inj-l tt
decide-direction (α⇐' _ _ _) = inj-r tt
decide-direction (λ⇐' _) = inj-r tt
decide-direction (ρ⇐' _) = inj-r tt
decide-direction (m ⊗ˡ' _) = decide-direction m
decide-direction (_ ⊗ʳ' m) = decide-direction m


decide-directions : {a b : WObj} -> (p : BasicPath a b) -> PathDirections p
decide-directions (empty p) = tt
decide-directions (m :: p) = decide-direction m , decide-directions p

-- TODO move and rename
clean-mor->forward-mor : {a b : WObj} -> (m : BasicMor a b) -> isCleanMor m -> isForwardMor m
clean-mor->forward-mor (λ⇒' _) _ = tt
clean-mor->forward-mor (ρ⇒' _) _ = tt
clean-mor->forward-mor (m ⊗ˡ' w) c = clean-mor->forward-mor m c
clean-mor->forward-mor (w ⊗ʳ' m) c = clean-mor->forward-mor m c

clean-path->forward-path : {a b : WObj} -> (p : BasicPath a b) -> isCleanPath p -> isForwardPath p
clean-path->forward-path (empty p) _ = tt
clean-path->forward-path (m :: p) (cm , cp) =
  clean-mor->forward-mor m cm , clean-path->forward-path p cp

directed-mor->forward-mor : {a b : WObj} -> (m : BasicMor a b) -> isDirectedMor m -> isForwardMor m
directed-mor->forward-mor (α⇒' _ _ _) _ = tt
directed-mor->forward-mor (m ⊗ˡ' w) d = directed-mor->forward-mor m d
directed-mor->forward-mor (w ⊗ʳ' m) d = directed-mor->forward-mor m d

directed-path->forward-path : {a b : WObj} -> (p : BasicPath a b) -> isDirectedPath p -> isForwardPath p
directed-path->forward-path (empty p) _ = tt
directed-path->forward-path (m :: p) (dm , dp) =
  directed-mor->forward-mor m dm , directed-path->forward-path p dp


_fp++_ : {a b c : WObj} -> ForwardPath a b -> ForwardPath b c -> ForwardPath a c
_fp++_ {c = c} (empty p , _) =
  transport (\i -> ForwardPath (p (~ i)) c)
_fp++_ (m :: p , fm , fp) p2 =
  let (rp , rfp) = (p , fp) fp++ p2 in
  (m :: rp , fm , rfp)


basic-mor->length= : {o1 o2 : WObj} -> BasicMor o1 o2 -> WObj-length o1 == WObj-length o2
basic-mor->length= (λ⇒' o) = refl
basic-mor->length= (λ⇐' o) = refl
basic-mor->length= (ρ⇒' o) = +-right-zero
basic-mor->length= (ρ⇐' o) = sym +-right-zero
basic-mor->length= (m ⊗ˡ' c) =
  +-left (basic-mor->length= m)
basic-mor->length= (a ⊗ʳ' m) =
  +-right (basic-mor->length= m)
basic-mor->length= (α⇒' a b c) =
  +-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c)
basic-mor->length= (α⇐' a b c) =
  sym (+-assocᵉ (WObj-length a) (WObj-length b) (WObj-length c))

basic-path->length= : {o1 o2 : WObj} -> BasicPath o1 o2 -> WObj-length o1 == WObj-length o2
basic-path->length= (empty p) = cong WObj-length p
basic-path->length= (m :: p) =
  basic-mor->length= m >=> basic-path->length= p

forward-path-to-isCanon :
  (o1 o2 : WObj) -> (isCanon o2) -> (WObj-length o1 == WObj-length o2) ->
                     ForwardPath o1 o2
forward-path-to-isCanon o1 o2 c-o2 lp =
  (fst cp , clean-path->forward-path (fst cp) (snd cp)) fp++
  (fst dp , directed-path->forward-path (fst dp) (snd dp))
  where
  om = clean o1

  cp : CleanPath o1 om
  cp = clean->clean-path (snd (Σclean o1))

  lp2 : WObj-length om == WObj-length o2
  lp2 = sym (basic-path->length= (fst cp)) >=> lp

  dp : DirectedPath om o2
  dp = either (\iε -> dirpath-to-isCanon-ε om o2 iε c-o2 lp2)
              (\εF -> dirpath-to-isCanon om o2 εF c-o2 lp2)
              (Clean->isε⊎isεFree (snd (Σclean o1)))


module InMonoidalCanon {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open InMonoidal MC obj
  open InMonoidalDir MC obj
  open InMonoidalFactor MC obj
  open InMonoidalFactor2 MC obj
  open InMonoidalIso MC obj



  private
    cases : {o1 o2 : WObj} -> (p : BasicPath o1 o2) -> (ds : PathDirections p) ->
            isCanon o2 ->
            Σ[ fp ∈ ForwardPath o1 o2 ] (forward-path->mor fp == basic-path->mor p)
    cases (empty p) tt _ = (empty p , tt) , refl
    cases (m :: p) (inj-l fm , ds) c-o2 =
      let (fp , q) = cases p ds c-o2 in
      cons-forward-mor (m , fm) fp , ⋆-right q
    cases {o1} {o2} (_::_ {om} m p) (inj-r fm' , ds) c-o2 =
      mid-canon-path , proof
      where

      rec : Σ[ fp ∈ ForwardPath om o2 ] (forward-path->mor fp == basic-path->mor p)
      rec = cases p ds c-o2

      lp : WObj-length o1 == WObj-length o2
      lp = basic-path->length= (m :: p)


      mid-canon-path : ForwardPath o1 o2
      mid-canon-path = forward-path-to-isCanon o1 o2 c-o2 lp

      mid-path2 : ForwardPath om o2
      mid-path2 = cons-forward-mor (invert-bm m , fm') mid-canon-path

      mid-path2-path : forward-path->mor mid-path2 == forward-path->mor (fst rec)
      mid-path2-path = parallel-forward-paths-to-canon mid-path2 (fst rec) c-o2

      inverses : AreInverses C (basic-mor->mor m) (basic-mor->mor (invert-bm m))
      inverses = AreInverses-invert-bm m

      proof : forward-path->mor mid-canon-path == basic-path->mor (m :: p)
      proof =
        sym ⋆-left-id >=>
        ⋆-left (sym (proj₁ inverses)) >=>
        ⋆-assoc >=>
        ⋆-right (mid-path2-path >=> snd rec)


  private
    P : Pred WObj _
    P o1 = (o2 : WObj) ->
           (m1 m2 : BasicPath o1 o2) ->
           (isCanon o2) ->
           (basic-path->mor m1 == basic-path->mor m2)

  parallel-paths-to-canon : ∀ o -> P o
  parallel-paths-to-canon o1 o2 p1 p2 c-o2 =
    sym (snd rec1) >=> parallel-forward-paths-to-canon (fst rec1) (fst rec2) c-o2 >=> (snd rec2)
    where
    rec1 : Σ[ dp ∈ ForwardPath o1 o2 ] (forward-path->mor dp == basic-path->mor p1)
    rec1 = cases p1 (decide-directions p1) c-o2
    rec2 : Σ[ dp ∈ ForwardPath o1 o2 ] (forward-path->mor dp == basic-path->mor p2)
    rec2 = cases p2 (decide-directions p2) c-o2


  parallel-paths : ∀ {o1 o2} ->
    (p1 p2 : BasicPath o1 o2) ->
    basic-path->mor p1 == basic-path->mor p2
  parallel-paths {o1} {o2} p1 p2 = p1=p2
    where
    Σc : Σ[ c ∈ WObj ] (WObj-length c == WObj-length o2 × isCanon c)
    Σc = fst (∃!canon (WObj-length o2))
    c = fst Σc

    cp : BasicPath o2 c
    cp = fst (forward-path-to-isCanon o2 c (snd (snd Σc)) (sym (fst (snd Σc))))

    p1' : BasicPath o1 c
    p1' = p1 bp++ cp
    p2' : BasicPath o1 c
    p2' = p2 bp++ cp


    p1'=p2' : basic-path->mor p1' == basic-path->mor p2'
    p1'=p2' = parallel-paths-to-canon o1 c p1' p2' (snd (snd Σc))

    iso-cp : isIso C (basic-path->mor cp)
    iso-cp = isIso-basic-path cp

    p1=p2 : basic-path->mor p1 == basic-path->mor p2
    p1=p2 = isIso->isMono iso-cp (sym (basic-path->mor-bp++ p1 cp) >=>
                                  p1'=p2' >=>
                                  basic-path->mor-bp++ p2 cp)
