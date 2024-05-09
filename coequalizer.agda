{-# OPTIONS --cubical --safe --exact-split #-}

module coequalizer where

open import base
open import coequalizer.singleton
open import cubical hiding (glue)
open import equality-path
open import equality.pathp-iso
open import equality.square
open import equivalence
open import functions
open import hlevel
open import isomorphism
open import relation
open import sigma
open import sigma.base
open import univalence

-- Following the paper:
-- https://arxiv.org/abs/1901.06022
-- PATH SPACES OF HIGHER INDUCTIVE TYPES IN HOMOTOPY TYPE THEORY
-- - NICOLAI KRAUS AND JAKOB VON RAUMER

data _//_ {ℓA ℓR : Level} (A : Type ℓA) (R : Rel A ℓR) : Type (ℓ-max ℓA ℓR) where
  [_] : A -> A // R
  glue : {a1 a2 : A} -> R a1 a2 -> [ a1 ] == [ a2 ]

private
  module _ {ℓA ℓR : Level} (A : Type ℓA) (R : Rel A ℓR) (a₀ : A) (ℓ : Level) where

    record Obj : Type (ℓ-max* 3 ℓA ℓR (ℓ-suc ℓ)) where
      field
        T : A -> Type ℓ
        base : T a₀
        eq : {b c : A} -> R b c -> T b ≃ T c

    record Obj' : Type (ℓ-max* 3 ℓA ℓR (ℓ-suc ℓ)) where
      field
        T : A // R -> Type ℓ
        base : T ([ a₀ ])


module _ {ℓ : Level} {A : Type ℓ} {R : Rel A ℓ} {a₀ : A} where
  private
    ℓA = ℓ
    ℓR = ℓ

    module _ (s t : Obj A R a₀ ℓ) where
      private
        module s = Obj s
        module t = Obj t

      record Mor : Type (ℓ-max* 3 ℓA ℓR ℓ) where
        field
          f : ∀ (b : A) -> s.T b -> t.T b
          base-path : f a₀ s.base == t.base
          eq-path : ∀ {b c} -> (r : R b c) -> (eqFun (t.eq r) ∘ f b) == (f c ∘ eqFun (s.eq r))

    module _ (s t : Obj' A R a₀ ℓ) where
      private
        module s = Obj' s
        module t = Obj' t

      record Mor' : Type (ℓ-max* 3 ℓA ℓR ℓ) where
        field
          f : ∀ (b : A // R) -> s.T b -> t.T b
          base-path : f [ a₀ ] s.base == t.base


    module _ {r s t : Obj A R a₀ ℓ} (m1 : Mor r s) (m2 : Mor s t) where
      private
        module m1 = Mor m1
        module m2 = Mor m2
      Mor∘ : Mor r t
      Mor∘ .Mor.f b rb = m2.f b (m1.f b rb)
      Mor∘ .Mor.base-path = cong (m2.f a₀) m1.base-path >=> m2.base-path
      Mor∘ .Mor.eq-path {b} {c} rbc =
        (\j x -> m2.eq-path rbc j (m1.f b x)) >=>
        (\j x -> m2.f c (m1.eq-path rbc j x))

    Obj'->Obj : Obj' A R a₀ ℓ -> Obj A R a₀ ℓ
    Obj'->Obj o = record
      { T = \a -> Obj'.T o [ a ]
      ; base = Obj'.base o
      ; eq = \r -> Iso.fun univalence-iso (cong (Obj'.T o) (glue r))
      }

    Obj->Obj' : Obj A R a₀ ℓ -> Obj' A R a₀ ℓ
    Obj->Obj' o = record
      { T = \{ [ a ] -> Obj.T o a ; (glue r i) -> Iso.inv univalence-iso (Obj.eq o r) i }
      ; base = Obj.base o
      }

    Obj'<->Obj : Iso (Obj' A R a₀ ℓ) (Obj A R a₀ ℓ)
    Obj'<->Obj = iso Obj'->Obj Obj->Obj' Obj->Obj'->Obj Obj'->Obj->Obj'
      where
      opaque
        Obj->Obj'->Obj : ∀ o -> Obj'->Obj (Obj->Obj' o) == o
        Obj->Obj'->Obj o i .Obj.T    = Obj.T o
        Obj->Obj'->Obj o i .Obj.base = Obj.base o
        Obj->Obj'->Obj o i .Obj.eq r = Iso.rightInv univalence-iso (Obj.eq o r) i

        Obj'->Obj->Obj' : ∀ o -> Obj->Obj' (Obj'->Obj o) == o
        Obj'->Obj->Obj' o i .Obj'.T [ a ] = Obj'.T o [ a ]
        Obj'->Obj->Obj' o i .Obj'.T (glue r j) = Iso.leftInv univalence-iso (\k -> Obj'.T o (glue r k)) i j
        Obj'->Obj->Obj' o i .Obj'.base = Obj'.base o


    Mor'->Mor : ∀ {o1 o2} -> Mor' o1 o2 -> Mor (Obj'->Obj o1) (Obj'->Obj o2)
    Mor'->Mor m .Mor.f a = Mor'.f m [ a ]
    Mor'->Mor m .Mor.base-path = Mor'.base-path m
    Mor'->Mor m .Mor.eq-path r =
      transport function-pathp==commuting-square (\i -> Mor'.f m (glue r i))

    Mor->Mor' : ∀ {o1 o2} -> Mor (Obj'->Obj o1) (Obj'->Obj o2) -> Mor' o1 o2
    Mor->Mor'           m .Mor'.f [ a ] = Mor.f m a
    Mor->Mor' {o1} {o2} m .Mor'.f (glue {b} {c} r i) = path i
      where
      path : PathP (\i -> Obj'.T o1 (glue r i) -> Obj'.T o2 (glue r i)) (Mor.f m b) (Mor.f m c)
      path = transport (sym function-pathp==commuting-square) (Mor.eq-path m r)
    Mor->Mor'           m .Mor'.base-path = Mor.base-path m

    Mor'<->Mor : ∀ o1 o2 -> Iso (Mor' o1 o2) (Mor (Obj'->Obj o1) (Obj'->Obj o2))
    Mor'<->Mor o1 o2 = iso Mor'->Mor Mor->Mor' (Mor->Mor'->Mor {o1} {o2}) Mor'->Mor->Mor'
      where
      opaque
        Mor'->Mor->Mor' : ∀ {o1 o2} (m : Mor' o1 o2) -> (Mor->Mor' (Mor'->Mor m)) == m
        Mor'->Mor->Mor' m i .Mor'.f [ a ] = Mor'.f m [ a ]
        Mor'->Mor->Mor' m i .Mor'.base-path = Mor'.base-path m
        Mor'->Mor->Mor' m i .Mor'.f (glue r j) =
          transport-sym function-pathp==commuting-square (\k -> Mor'.f m (glue r k)) i j

        Mor->Mor'->Mor : ∀ {o1 o2} (m : Mor (Obj'->Obj o1) (Obj'->Obj o2)) ->
                           (Mor'->Mor {o1} {o2} (Mor->Mor' m)) == m
        Mor->Mor'->Mor m i .Mor.f a = Mor.f m a
        Mor->Mor'->Mor m i .Mor.base-path = Mor.base-path m
        Mor->Mor'->Mor {o1} {o2} m i .Mor.eq-path {b} {c} r =
          transport-sym
            (sym (function-pathp==commuting-squareᵉ
                     (\k -> Obj'.T o1 (glue r k))
                     (\k -> Obj'.T o2 (glue r k))
                     (Mor.f m b) (Mor.f m c)))
            (Mor.eq-path m r) i

    Obj'==Obj : Obj' A R a₀ ℓ == Obj A R a₀ ℓ
    Obj'==Obj = isoToPath Obj'<->Obj

    Mor'==Mor-part1 : ∀ o1 o2 -> (Mor' o1 o2) == (Mor (Obj'->Obj o1) (Obj'->Obj o2))
    Mor'==Mor-part1 o1 o2 = isoToPath (Mor'<->Mor o1 o2)

    Mor'==Mor : PathP (\i -> Obj'==Obj i -> Obj'==Obj i -> Type ℓ) Mor' Mor
    Mor'==Mor i =
      hcomp (\k -> \{ (i = i0) -> Mor'
                    ; (i = i1) -> \o1 o2 -> Mor (path o1 k) (path o2 k)
                    })
            (\o1 o2 -> Mor'==Mor-part1 (transp (\j -> Obj'==Obj (i ∧ ~ j)) (~ i) o1)
                                       (transp (\j -> Obj'==Obj (i ∧ ~ j)) (~ i) o2)
                                       i)
      where
      path : ∀ o -> (Obj'->Obj (transport (sym Obj'==Obj) o)) == o
      path o = (\i -> Obj'->Obj (step1 i)) >=> Iso.rightInv Obj'<->Obj o
        where
        step1 : (transport (sym Obj'==Obj) o) == Obj->Obj' o
        step1 = (\i -> transport (sym-isoToPath Obj'<->Obj i) o) >=>
                (\i -> transport-isoToPath (iso⁻¹ Obj'<->Obj) i o)


    glue-eq : ∀ {b c : A} -> (r : R b c) -> (Path (A // R) [ a₀ ] [ b ]) ≃ (Path (A // R) [ a₀ ] [ c ])
    glue-eq {b} {c} r =
      isoToEquiv (iso (\p -> p >=> glue r) (\p -> p >=> sym (glue r)) unglue-glue glue-unglue)
      where
      opaque
        glue-unglue : ∀ p -> ((p >=> glue r) >=> sym (glue r)) == p
        glue-unglue p =
          compPath-assoc p (glue r) (sym (glue r)) >=>
          cong (p >=>_) (compPath-sym (glue r)) >=>
          compPath-refl-right p
        unglue-glue : ∀ p -> ((p >=> sym (glue r)) >=> (glue r)) == p
        unglue-glue p =
          compPath-assoc p (sym (glue r)) (glue r) >=>
          cong (p >=>_) (compPath-sym (sym (glue r))) >=>
          compPath-refl-right p


    init-Obj' : Obj' A R a₀ ℓ
    init-Obj' .Obj'.T b = [ a₀ ] == b
    init-Obj' .Obj'.base = refl

    init-Obj : Obj A R a₀ ℓ
    init-Obj .Obj.T b = Path (A // R) [ a₀ ] [ b ]
    init-Obj .Obj.base = refl
    init-Obj .Obj.eq = glue-eq

    same-init : Obj'->Obj init-Obj' == init-Obj
    same-init i .Obj.T b = Path (A // R) [ a₀ ] [ b ]
    same-init i .Obj.base = refl
    same-init i .Obj.eq {b} {c} r = path i
      where
      opaque
        inner-path : Path (Path (A // R) [ a₀ ] [ b ] -> Path (A // R) [ a₀ ] [ c ])
                          (\p -> transport (\i -> Path (A // R) [ a₀ ] (glue r i)) p)
                          (\p -> p >=> glue r)
        inner-path =
          (\i p -> transport (\i -> Path (A // R) [ a₀ ] (glue r i)) (compPath-refl-right p (~ i))) >=>
          (\i p -> transp (\j -> Path (A // R) [ a₀ ] (glue r (i ∨ j))) i (p >=> (\j -> glue r (i ∧ j))))


        path : Path (Path (A // R) [ a₀ ] [ b ] ≃ Path (A // R) [ a₀ ] [ c ])
                    (pathToEquiv (\i -> Path (A // R) [ a₀ ] (glue r i)))
                    (glue-eq r)
        path = equiv-path inner-path

    isInitial-init-Obj' : ∀ o2 -> isContr (Mor' init-Obj' o2)
    isInitial-init-Obj' = isContr-mor
      where
      module _ (o2 : Obj' A R a₀ ℓ) where
        opaque
          module o = Obj' init-Obj'
          module o2 = Obj' o2

          path-Σ1 : Mor' init-Obj' o2 ==
                   (Σ[ f ∈ (∀ (b : A // R) -> o.T b -> o2.T b) ] (f [ a₀ ] o.base == o2.base))
          path-Σ1 = isoToPath (iso f b (\_ -> refl) (\_ -> refl))
            where
            f : Mor' init-Obj' o2 ->
                (Σ[ f ∈ (∀ (b : A // R) -> o.T b -> o2.T b) ] (f [ a₀ ] o.base == o2.base))
            f m .fst = Mor'.f m
            f m .snd = Mor'.base-path m

            b : (Σ[ f ∈ (∀ (b : A // R) -> o.T b -> o2.T b) ] (f [ a₀ ] o.base == o2.base)) ->
                Mor' init-Obj' o2
            b (f , bp) .Mor'.f = f
            b (f , bp) .Mor'.base-path = bp

          path-Σ2 : (Σ[ f ∈ (∀ (b : A // R) -> [ a₀ ] == b -> o2.T b) ] (f [ a₀ ] refl == o2.base)) ==
                    (Σ[ b ∈ o2.T [ a₀ ] ] (b == o2.base))
          path-Σ2 j =
            Σ[ f ∈ singleton-Π-path o2.T [ a₀ ] j ]
               (singleton-Π-value o2.T [ a₀ ] j f == o2.base)

          isContr-mor : isContr (Mor' init-Obj' o2)
          isContr-mor = subst isContr (sym (path-Σ1 >=> path-Σ2)) (isContr-singleton' o2.base)

    isInitial-init-Obj-raw : ∀ (o2 : Obj A R a₀ ℓ) -> isContr (Mor init-Obj o2)
    isInitial-init-Obj-raw = transport (p1 >=> p2 >=> p3) isInitial-init-Obj'
      where
      check : PathP (\i -> (Obj'==Obj i) -> Obj A R a₀ ℓ) (\o2 -> Obj'->Obj o2) (\o2 -> o2)
      check = transP-right (sym (transport-isoToPath Obj'<->Obj))
                           (\i o -> transp (\j -> Obj'==Obj (i ∨ j)) i o)

      p1 = (\i -> ∀ (o2 : Obj' A R a₀ ℓ) -> isContr (Mor'==Mor-part1 init-Obj' o2 i))
      p2 = (\i -> ∀ (o2 : Obj' A R a₀ ℓ) -> isContr (Mor (same-init i) (Obj'->Obj o2)))
      p3 = (\i -> ∀ (o2 : Obj'==Obj i) -> isContr (Mor init-Obj (check i o2)))

    opaque
      isInitial-init-Obj : ∀ (o2 : Obj A R a₀ ℓ) -> isContr (Mor init-Obj o2)
      isInitial-init-Obj = isInitial-init-Obj-raw

  module _ (P : ∀ {b} -> Path (A // R) [ a₀ ] [ b ] -> Type ℓ)
           (r₀ : P (reflᵉ [ a₀ ]))
           (e : ∀ {b c} -> (q : Path (A // R) [ a₀ ] [ b ]) -> (s : R b c) ->
                P q ≃ P (q >=> glue s))
           where
    private

      BasedPath : A -> Type _
      BasedPath b = Path ( A // R) [ a₀ ] [ b ]

      add-glue : {b c : A} -> (r : R b c) -> BasedPath b -> BasedPath c
      add-glue r p = p >=> glue r
      add-unglue : {b c : A} -> (r : R b c) -> BasedPath c -> BasedPath b
      add-unglue r p = p >=> sym (glue r)

      glue-eq' : ∀ {b c : A} -> (r : R b c) -> Σ (BasedPath b) P ≃ Σ (BasedPath c) P
      glue-eq' r = existential-eq (\q -> (e q r)) >eq> (equiv⁻¹ (reindexΣ (glue-eq r) P))

      Σinitial-Obj : Σ[ o ∈ Obj A R a₀ ℓ ] (∀ o2 -> isContr (Mor o o2))
      Σinitial-Obj = init-Obj , isInitial-init-Obj

      //-path-ind-Obj : Obj A R a₀ ℓ
      //-path-ind-Obj .Obj.T b = Σ[ q ∈ [ a₀ ] == [ b ] ] (P q)
      //-path-ind-Obj .Obj.base = refl , r₀
      //-path-ind-Obj .Obj.eq = glue-eq'


      init-Mor : Mor init-Obj //-path-ind-Obj
      init-Mor = fst (snd Σinitial-Obj //-path-ind-Obj)

      init-f : (b : A) -> BasedPath b -> Σ (BasedPath b) P
      init-f = Mor.f init-Mor

      proj-Mor : Mor //-path-ind-Obj init-Obj
      proj-Mor .Mor.f _ (q , p) = q
      proj-Mor .Mor.base-path _ = refl
      proj-Mor .Mor.eq-path r = reflᵉ (add-glue r ∘ fst)

      id-Mor : Mor init-Obj init-Obj
      id-Mor .Mor.f _ q = q
      id-Mor .Mor.base-path _ = refl
      id-Mor .Mor.eq-path _ = refl

      comped-Mor : Mor init-Obj init-Obj
      comped-Mor = Mor∘ init-Mor proj-Mor

      φ : comped-Mor == id-Mor
      φ = isContr->isProp (snd Σinitial-Obj init-Obj) comped-Mor id-Mor

      φ1 : ∀ {b} (q : [ a₀ ] == [ b ]) -> fst (init-f b q) == q
      φ1 q i = Mor.f (φ i) _ q

      φ2 : PathP (\i -> (φ1 refl i) == refl) (Mor.base-path comped-Mor) (Mor.base-path id-Mor)
      φ2 i = Mor.base-path (φ i)

      φ3 : PathP (\i -> (∀ {b c} -> (r : R b c) ->
                          Path ((q : BasedPath b) -> _)
                          (\q -> add-glue r (φ1 q i))
                          (\q -> φ1 (add-glue r q) i)))
                 (Mor.eq-path comped-Mor)
                 (Mor.eq-path id-Mor)
      φ3 i = Mor.eq-path (φ i)


    //-path-ind : {b : A} -> (q : BasedPath b) -> P q
    //-path-ind {b} q = substᵉ P (φ1 q) (snd (init-f b q))

    //-path-ind-base-path : //-path-ind refl == r₀
    //-path-ind-base-path = transP-sym path1 path2
      where
      path1 : PathP (\i -> P (φ1 refl (~ i))) (//-path-ind refl) (snd (init-f a₀ refl))
      path1 = symP (subst-filler P (φ1 refl) (snd (init-f a₀ refl)))

      φ2-rot : Mor.base-path comped-Mor == φ1 refl
      φ2-rot = rotate-square-ARBC->ABRC φ2

      same-path : Path _ (cong fst (Mor.base-path init-Mor)) (φ1 refl)
      same-path = sym (compPath-refl-right _) >=> φ2-rot

      path2 : PathP (\i -> P (φ1 refl i)) (snd (init-f a₀ refl)) r₀
      path2 = transport (\j -> PathP (\i -> P (same-path j i)) (snd (init-f a₀ refl)) r₀)
                        (\i -> snd (Mor.base-path init-Mor i))

    //-path-ind-glue :
      {b c : A} -> (q : BasedPath b) -> (r : R b c) ->
      //-path-ind (q >=> glue r) == eqFun (e q r) (//-path-ind q)
    //-path-ind-glue {b} {c} q r = full-path
      where
      q' : BasedPath c
      q' = add-glue r q

      point1 : Σ (BasedPath b) P
      point1 = init-f _ q

      point2 : Σ (BasedPath c) P
      point2 = eqFun (glue-eq' r) point1

      point3 : Σ (BasedPath c) P
      point3 = init-f _ q'

      γ : Path (Σ (BasedPath c) P) point2 point3
      γ j = Mor.eq-path init-Mor r j q

      γ₁ : Path (BasedPath c) (fst point2) (fst point3)
      γ₁ i = fst (γ i)

      γ₂ : PathP (\i -> P (γ₁ i)) (snd point2) (snd point3)
      γ₂ i = snd (γ i)


      path1 : PathP (\i -> P (φ1 (add-glue r q) (~ i)))
                 (//-path-ind (add-glue r q))
                 (snd point3)
      path1 = symP (subst-filler P (φ1 (add-glue r q)) (snd (init-f c (add-glue r q))))

      path2 : PathP (\i -> P (φ1 q i))
                 (snd point1)
                 (//-path-ind q)
      path2 = (subst-filler P (φ1 q) (snd (init-f b q)))

      path3 : PathP (\i -> P (add-glue r (φ1 q i)))
                 (snd point2)
                 (eqFun (e q r) (//-path-ind q))
      path3 i = eqFun (e (φ1 q i) r) (path2 i)


      full-pathp : PathP (\j -> ((\i -> P (φ1 (add-glue r q) (~ i))) >=>
                                 ((\i -> P (γ₁ (~ i))) >=>
                                  (\i -> P (add-glue r (φ1 q i))))) j)
                         (//-path-ind (add-glue r q))
                         (eqFun (e q r) (//-path-ind q))
      full-pathp = transP path1 (transP (symP γ₂) path3)

      simplify-path :
        ((\i -> P (φ1 (add-glue r q) (~ i))) >=>
         ((\i -> P (γ₁ (~ i))) >=>
          (\i -> P (add-glue r (φ1 q i))))) ==
        refl
      simplify-path = sym (rearrange-square Pφ3')
        where
        φ3' : PathP (\i -> (∀ {b c} -> (r : R b c) ->
                            Path ((q : BasedPath b) -> (BasedPath c))
                            (\q -> add-glue r (φ1 q i))
                            (\q -> φ1 (add-glue r q) i)))
                    (\r j q -> fst (Mor.eq-path init-Mor r j q))
                    (\_ -> refl)
        φ3' = transP-right
                (\i r -> (compPath-refl-left (\j q -> fst (Mor.eq-path init-Mor r j q)) (~ i)))
                φ3


        Pφ3' : Square (\j -> P (fst (Mor.eq-path init-Mor r j q)))
                      refl
                      (\i -> P (add-glue r (φ1 q i)))
                      (\i -> P (φ1 (add-glue r q) i))
        Pφ3' i j = P (φ3' i r j q)

        module _ {ℓ : Level} {T : Type ℓ} {x0 x1 x2 : T}
                 {p1 : x0 == x1}
                 {p2 : x0 == x2}
                 {p3 : x1 == x2}
                 (s : Square p1 refl p2 p3)
          where
          opaque
            step1 : (p1 >=> p3) == (p2 >=> refl)
            step1 = square-commutes s

            step2 : (p1 >=> p3) == p2
            step2 = step1 >=> compPath-refl-right p2

            step3 : p3 == (sym p1) >=> p2
            step3 = sym (compPath-refl-left p3) >=>
                    cong (_>=> p3) (sym (compPath-sym (sym p1))) >=>
                    compPath-assoc (sym p1) p1 p3 >=>
                    cong ((sym p1) >=>_) step2

            rearrange-square : refl == (sym p3) >=> ((sym p1) >=> p2)
            rearrange-square = sym (compPath-sym (sym p3)) >=>
                               cong (sym p3 >=>_) step3


      full-path : (//-path-ind (add-glue r q)) == (eqFun (e q r) (//-path-ind q))
      full-path =
        transport (\i -> PathP (\j -> simplify-path i j)
                           (//-path-ind (add-glue r q))
                           (eqFun (e q r) (//-path-ind q)))
                  full-pathp
