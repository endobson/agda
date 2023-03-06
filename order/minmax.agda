{-# OPTIONS --cubical --safe --exact-split #-}

module order.minmax where

open import base
open import equality
open import hlevel.base
open import order
open import relation
open import sum
open import truncation


record MinOperationStr {ℓD ℓ< : Level} {D : Type ℓD} (LO : LinearOrderStr D ℓ<) :
                       Type (ℓ-max ℓ< ℓD) where
  private
    _<'_ = LinearOrderStr._<_ LO

  field
    min : D -> D -> D
    min-≮-left  : {x y : D} -> ¬ (x <' min x y)
    min-≮-right : {x y : D} -> ¬ (y <' min x y)
    min-greatest-< : {x y z : D} -> z <' x -> z <' y -> z <' min x y


module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {{MO : MinOperationStr LO }} where
  open MinOperationStr MO public

  private
    instance
      ILO = LO

  min-commute : {x y : D} -> min x y == min y x
  min-commute = connected-< not< not<
    where
    not< : {x y : D} -> ¬ (min x y < min y x)
    not< {x} {y} xy<yx =
      unsquash isPropBot (∥-map2 handle (comparison-< _ _ _ xy<yx) (comparison-< _ _ _ xy<yx))
      where
      handle : (min x y < x) ⊎ (x < min y x) -> (min x y < y) ⊎ (y < min y x) -> Bot
      handle (inj-r x<yx) _            = min-≮-right x<yx
      handle (inj-l xy<x) (inj-r y<yx) = min-≮-left y<yx
      handle (inj-l xy<x) (inj-l xy<y) = irrefl-< (min-greatest-< xy<x xy<y)


  min-<-path : {x y : D} -> x < y -> min x y == x
  min-<-path x<y =
    connected-< (\xy<x -> irrefl-< (min-greatest-< xy<x (trans-< xy<x x<y)))
                min-≮-left

  min->-path : {x y : D} -> x > y -> min x y == y
  min->-path x>y = min-commute >=> min-<-path x>y

  min-<-right-path : {x y : D} -> min x y < y -> min x y == x
  min-<-right-path xy<y =
    connected-< (\xy<x -> irrefl-< (min-greatest-< xy<x xy<y))
                min-≮-left


  min-<-left-path : {x y : D} -> min x y < x -> min x y == y
  min-<-left-path xy<x =
    min-commute >=> (min-<-right-path (trans-=-< min-commute xy<x))

  min-idempotent : {x : D} -> min x x == x
  min-idempotent {x} =
    connected-< (\xx<x -> irrefl-path-< (min-<-right-path xx<x) xx<x)
                min-≮-left

  min₁-reflects-< : {x y z : D} -> min x y < min x z -> y < z
  min₁-reflects-< {x} {y} {z} xy<xz =
    unsquash isProp-< (∥-map2 handle (comparison-< _ z _ xy<xz)
                                     (comparison-< _ x _ xy<xz))
    where
    handle : (min x y < z) ⊎ (z < min x z) ->
             (min x y < x) ⊎ (x < min x z) ->
             y < z
    handle (inj-r z<xz) _            = bot-elim (min-≮-right z<xz)
    handle (inj-l xy<z) (inj-r x<xz) = bot-elim (min-≮-left x<xz)
    handle (inj-l xy<z) (inj-l xy<x) =
       trans-=-< (sym (min-<-left-path xy<x)) xy<z

  min₂-reflects-< : {x y z : D} -> min x y < min z y -> x < z
  min₂-reflects-< xy<zy = min₁-reflects-< (subst2 _<_ min-commute min-commute xy<zy)


record MaxOperationStr {ℓD ℓ< : Level} {D : Type ℓD} (LO : LinearOrderStr D ℓ<) :
                       Type (ℓ-max ℓ< ℓD) where
  private
    _<'_ = LinearOrderStr._<_ LO

  field
    max : D -> D -> D
    max-≮-left  : {x y : D} -> ¬ (max x y <' x)
    max-≮-right : {x y : D} -> ¬ (max x y <' y)
    max-least-< : {x y z : D} -> x <' z -> y <' z -> max x y <' z


module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {{MO : MaxOperationStr LO }} where
  open MaxOperationStr MO public

  private
    instance
      ILO = LO

  max-commute : {x y : D} -> max x y == max y x
  max-commute = connected-< not< not<
    where
    not< : {x y : D} -> ¬ (max x y < max y x)
    not< {x} {y} xy<yx =
      unsquash isPropBot (∥-map2 handle (comparison-< _ _ _ xy<yx) (comparison-< _ _ _ xy<yx))
      where
      handle : (max x y < x) ⊎ (x < max y x) -> (max x y < y) ⊎ (y < max y x) -> Bot
      handle (inj-l xy<x) _            = max-≮-left xy<x
      handle (inj-r x<yx) (inj-l xy<y) = max-≮-right xy<y
      handle (inj-r x<yx) (inj-r y<yx) = irrefl-< (max-least-< y<yx x<yx)

  max-<-path : {x y : D} -> x < y -> max x y == y
  max-<-path x<y =
    connected-< max-≮-right
                (\y<xy -> irrefl-< (max-least-< (trans-< x<y y<xy) y<xy))

  max->-path : {x y : D} -> x > y -> max x y == x
  max->-path x>y = max-commute >=> max-<-path x>y

  max-<-right-path : {x y : D} -> y < max x y -> max x y == x
  max-<-right-path y<xy =
    connected-< max-≮-left (\x<xy -> irrefl-< (max-least-< x<xy y<xy))

  max-<-left-path : {x y : D} -> x < max x y -> max x y == y
  max-<-left-path x<xy =
    max-commute >=> (max-<-right-path (trans-<-= x<xy max-commute))

  max-idempotent : {x : D} -> max x x == x
  max-idempotent {x} =
    connected-< max-≮-left
                (\x<xx -> irrefl-path-< (sym (max-<-right-path x<xx)) x<xx)

  max₁-reflects-< : {x y z : D} -> max x y < max x z -> y < z
  max₁-reflects-< {x} {y} {z} xy<xz =
    unsquash isProp-< (∥-map2 handle (comparison-< _ y _ xy<xz)
                                     (comparison-< _ x _ xy<xz))
    where
    handle : (max x y < y) ⊎ (y < max x z) ->
             (max x y < x) ⊎ (x < max x z) ->
             y < z
    handle (inj-l xy<y) _            = bot-elim (max-≮-right xy<y)
    handle (inj-r y<xz) (inj-l xy<x) = bot-elim (max-≮-left xy<x)
    handle (inj-r y<xz) (inj-r x<xz) =
      trans-<-= y<xz (max-<-left-path x<xz)

  max₂-reflects-< : {x y z : D} -> max x y < max z y -> x < z
  max₂-reflects-< xy<zy = max₁-reflects-< (subst2 _<_ max-commute max-commute xy<zy)


module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {PO : PartialOrderStr D ℓ≤}
         {{CO : CompatibleOrderStr LO PO}} {{MO : MaxOperationStr LO}} where
  private
    instance
      ILO = LO
      IPO = PO

  max-≤-left : {x y : D} -> x ≤ max x y
  max-≤-left = convert-≮ max-≮-left

  max-≤-right : {x y : D} -> y ≤ max x y
  max-≤-right = convert-≮ max-≮-right

  max-least-≤ : {x y z : D} -> x ≤ z -> y ≤ z -> max x y ≤ z
  max-least-≤ {x} {y} {z} x≤z y≤z =
    convert-≮ (\z<xy -> unsquash isPropBot (∥-map2 handle (comparison-< _ _ _ z<xy)
                                                          (comparison-< _ _ _ z<xy)))
    where
    handle : (z < x ⊎ x < max x y) -> (z < y ⊎ y < max x y) -> Bot
    handle (inj-l z<x)  _            = irrefl-< (trans-≤-< x≤z z<x)
    handle (inj-r x<xy) (inj-l z<y)  = irrefl-< (trans-≤-< y≤z z<y)
    handle (inj-r x<xy) (inj-r y<xy) = irrefl-< (max-least-< x<xy y<xy)

  max-≤-path : {x y : D} -> x ≤ y -> max x y == y
  max-≤-path x≤y = antisym-≤ (max-least-≤ x≤y refl-≤) max-≤-right

  max-≥-path : {x y : D} -> x ≥ y -> max x y == x
  max-≥-path x≥y = max-commute >=> max-≤-path x≥y

  max₁-preserves-≤ : {x y z : D} -> y ≤ z -> max x y ≤ max x z
  max₁-preserves-≤ y≤z = max-least-≤ max-≤-left (trans-≤ y≤z max-≤-right)

  max₂-preserves-≤ : {x y z : D} -> x ≤ y -> max x z ≤ max y z
  max₂-preserves-≤ x≤y = max-least-≤ (trans-≤ x≤y max-≤-left) max-≤-right

  max-preserves-≤ : {w x y z : D} -> w ≤ x -> y ≤ z -> max w y ≤ max x z
  max-preserves-≤ w≤x y≤z = trans-≤ (max₂-preserves-≤ w≤x) (max₁-preserves-≤ y≤z)


module _ {ℓD ℓ< ℓ≤ : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {PO : PartialOrderStr D ℓ≤}
         {{CO : CompatibleOrderStr LO PO}} {{MO : MinOperationStr LO}} where
  private
    instance
      ILO = LO
      IPO = PO

  min-≤-left : {x y : D} -> min x y ≤ x
  min-≤-left = convert-≮ min-≮-left

  min-≤-right : {x y : D} -> min x y ≤ y
  min-≤-right = convert-≮ min-≮-right

  min-greatest-≤ : {x y z : D} -> z ≤ x -> z ≤ y -> z ≤ min x y
  min-greatest-≤ {x} {y} {z} z≤x z≤y =
    convert-≮ (\xy<z -> unsquash isPropBot (∥-map2 handle (comparison-< _ _ _ xy<z)
                                                          (comparison-< _ _ _ xy<z)))
    where
    handle : (min x y < x ⊎ x < z) -> (min x y < y ⊎ y < z) -> Bot
    handle (inj-r x<z)  _            = irrefl-< (trans-≤-< z≤x x<z)
    handle (inj-l xy<x) (inj-r y<z)  = irrefl-< (trans-≤-< z≤y y<z)
    handle (inj-l xy<x) (inj-l xy<y) = irrefl-< (min-greatest-< xy<x xy<y)

  min-≤-path : {x y : D} -> x ≤ y -> min x y == x
  min-≤-path x≤y = antisym-≤ min-≤-left (min-greatest-≤ refl-≤ x≤y)

  min-≥-path : {x y : D} -> x ≥ y -> min x y == y
  min-≥-path x≥y = min-commute >=> min-≤-path x≥y

  min₁-preserves-≤ : {x y z : D} -> y ≤ z -> min x y ≤ min x z
  min₁-preserves-≤ y≤z = min-greatest-≤ min-≤-left (trans-≤ min-≤-right y≤z)

  min₂-preserves-≤ : {x y z : D} -> x ≤ y -> min x z ≤ min y z
  min₂-preserves-≤ x≤y = min-greatest-≤ (trans-≤ min-≤-left x≤y) min-≤-right

  min-preserves-≤ : {w x y z : D} -> w ≤ x -> y ≤ z -> min w y ≤ min x z
  min-preserves-≤ w≤x y≤z = trans-≤ (min₂-preserves-≤ w≤x) (min₁-preserves-≤ y≤z)


module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {{MO : MinOperationStr LO }} where
  private
    instance
      ILO = LO
      IPO = NegatedLinearOrder LO
      CPO = CompatibleNegatedLinearOrder LO

  min-assoc : {x y z : D} -> min (min x y) z == min x (min y z)
  min-assoc =
    antisym-≤ (min-greatest-≤ (trans-≤ min-≤-left min-≤-left)
                              (min₂-preserves-≤ min-≤-right))
              (min-greatest-≤ (min₁-preserves-≤ min-≤-left)
                              (trans-≤ min-≤-right min-≤-right))

  min-preserves-< : {w x y z : D} -> w < x -> y < z -> min w y < min x z
  min-preserves-< {w} {x} {y} {z} w<x y<z =
    unsquash isProp-< (∥-map handle (comparison-< _ x _ y<z))
    where
    handle : (y < x) ⊎ (x < z) -> min w y < min x z
    handle (inj-l y<x) =
      trans-≤-< min-≤-right (min-greatest-< y<x y<z)
    handle (inj-r x<z) =
      trans-<-= (trans-≤-< min-≤-left w<x) (sym (min-<-path x<z))


module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<} {{MO : MaxOperationStr LO }} where
  private
    instance
      ILO = LO
      IPO = NegatedLinearOrder LO
      CPO = CompatibleNegatedLinearOrder LO

  max-assoc : {x y z : D} -> max (max x y) z == max x (max y z)
  max-assoc =
    antisym-≤ (max-least-≤ (max₁-preserves-≤ max-≤-left)
                           (trans-≤ max-≤-right max-≤-right))
              (max-least-≤ (trans-≤ max-≤-left max-≤-left)
                           (max₂-preserves-≤ max-≤-right))

  max-preserves-< : {w x y z : D} -> w < x -> y < z -> max w y < max x z
  max-preserves-< {w} {x} {y} {z} w<x y<z =
    unsquash isProp-< (∥-map handle (comparison-< _ y _ w<x))
    where
    handle : (w < y) ⊎ (y < x) -> max w y < max x z
    handle (inj-l w<y) =
      trans-=-< (max-<-path w<y) (trans-<-≤ y<z max-≤-right)
    handle (inj-r y<x) =
      trans-<-≤ (max-least-< w<x y<x) max-≤-left


module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<}
         {{MinO : MinOperationStr LO }} {{MaxO : MaxOperationStr LO }} where
  private
    instance
      ILO = LO
      PO = NegatedLinearOrder LO
      CO = CompatibleNegatedLinearOrder LO

  max-distrib-min : {a b c : D} -> max a (min b c) == min (max a b) (max a c)
  max-distrib-min {a} {b} {c} = antisym-≤ abc≤abac abac≤abc
    where

    abc≤abac : max a (min b c) ≤ min (max a b) (max a c)
    abc≤abac = min-greatest-≤ abc≤ab abc≤ac
      where
      abc≤ab : max a (min b c) ≤ max a b
      abc≤ab = max₁-preserves-≤ min-≤-left

      abc≤ac : max a (min b c) ≤ max a c
      abc≤ac = max₁-preserves-≤ min-≤-right


    abac≤abc : min (max a b) (max a c) ≤ max a (min b c)
    abac≤abc abc<abac =
      unsquash isPropBot (∥-map2 handle (comparison-< _ (max a b) _ abc<abac)
                                        (comparison-< _ (max a c) _ abc<abac))
      where
      handle : (max a (min b c) < (max a b)) ⊎ ((max a b) < min (max a b) (max a c)) ->
               (max a (min b c) < (max a c)) ⊎ ((max a c) < min (max a b) (max a c)) ->
               Bot
      handle (inj-r ab<abac)   _            = min-≮-left ab<abac
      handle (inj-l abc<ab) (inj-r ac<abac) = min-≮-right ac<abac
      handle (inj-l abc<ab) (inj-l abc<ac)  =
        irrefl-< (min-greatest-< (max₁-reflects-< abc<ab) (max₁-reflects-< abc<ac))

  min-distrib-max : {a b c : D} -> min a (max b c) == max (min a b) (min a c)
  min-distrib-max {a} {b} {c} = antisym-≤ abc≤abac abac≤abc
    where

    abc≤abac : min a (max b c) ≤ max (min a b) (min a c)
    abc≤abac abac<abc =
      unsquash isPropBot (∥-map2 handle (comparison-< _ (min a b) _ abac<abc)
                                        (comparison-< _ (min a c) _ abac<abc))
      where
      handle : (max (min a b) (min a c) < (min a b)) ⊎ ((min a b) < min a (max b c)) ->
               (max (min a b) (min a c) < (min a c)) ⊎ ((min a c) < min a (max b c)) ->
               Bot
      handle (inj-l abac<ab) _               = max-≮-left abac<ab
      handle (inj-r ab<abc)  (inj-l abac<ac) = max-≮-right abac<ac
      handle (inj-r ab<abc)  (inj-r ac<abc)  =
        irrefl-< (max-least-< (min₁-reflects-< ab<abc) (min₁-reflects-< ac<abc))


    abac≤abc : max (min a b) (min a c) ≤ min a (max b c)
    abac≤abc = max-least-≤ ab≤abc ac≤abc
      where
      ab≤abc : min a b ≤ min a (max b c)
      ab≤abc = min₁-preserves-≤ max-≤-left

      ac≤abc : min a c ≤ min a (max b c)
      ac≤abc = min₁-preserves-≤ max-≤-right



module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<}
         {{DLO : DecidableLinearOrderStr LO}}  {{MO : MaxOperationStr LO}} where
  private
    instance
      ILO = LO

  split-max : {x y : D} -> (max x y == x) ⊎ (max x y == y)
  split-max {x} {y} = handle (trichotomous-< x y)
    where
    handle : Tri< x y -> (max x y == x) ⊎ (max x y == y)
    handle (tri< x<y _ _) = inj-r (max-<-path x<y)
    handle (tri= _ x=y _) = inj-l ((\i -> max x (x=y (~ i))) >=> max-idempotent)
    handle (tri> _ _ x>y) = inj-l (max-commute >=> max-<-path x>y)

  max-property : {ℓ : Level} {P : Pred D ℓ} -> (q r : D) -> P q -> P r -> P (max q r)
  max-property {P = P} q r pq pr = handle split-max
    where
    handle : (max q r == q) ⊎ (max q r == r) -> P (max q r)
    handle (inj-l m=q) = subst P (sym m=q) pq
    handle (inj-r m=r) = subst P (sym m=r) pr

module _ {ℓD ℓ< : Level} {D : Type ℓD} {LO : LinearOrderStr D ℓ<}
         {{DLO : DecidableLinearOrderStr LO}}  {{MO : MinOperationStr LO}} where
  private
    instance
      ILO = LO

  split-min : {x y : D} -> (min x y == x) ⊎ (min x y == y)
  split-min {x} {y} = handle (trichotomous-< x y)
    where
    handle : Tri< x y -> (min x y == x) ⊎ (min x y == y)
    handle (tri< x<y _ _) = inj-l (min-<-path x<y)
    handle (tri= _ x=y _) = inj-l ((\i -> min x (x=y (~ i))) >=> min-idempotent)
    handle (tri> _ _ x>y) = inj-r (min-commute >=> min-<-path x>y)

  min-property : {ℓ : Level} {P : Pred D ℓ} -> (q r : D) -> P q -> P r -> P (min q r)
  min-property {P = P} q r pq pr = handle split-min
    where
    handle : (min q r == q) ⊎ (min q r == r) -> P (min q r)
    handle (inj-l m=q) = subst P (sym m=q) pq
    handle (inj-r m=r) = subst P (sym m=r) pr


module _ {ℓD : Level} {D : Type ℓD} {ℓ< : Level} {{LO : LinearOrderStr D ℓ<}} where
  record isMax (d1 d2 d3 : D) : Type (ℓ-max ℓD ℓ<) where
    field
      left  : d3 ≮ d1
      right : d3 ≮ d2
      least : ∀ {d} -> d1 < d -> d2 < d -> d3 < d

  record isMin (d1 d2 d3 : D) : Type (ℓ-max ℓD ℓ<) where
    field
      left     : d1 ≮ d3
      right    : d2 ≮ d3
      greatest : ∀ {d} -> d < d1 -> d < d2 -> d < d3


  isMin->MinOperationStr : (∀ d1 d2 -> Σ D (isMin d1 d2)) -> MinOperationStr LO
  isMin->MinOperationStr min' = record
    { min = \d1 d2 -> fst (min' d1 d2)
    ; min-≮-left = isMin.left (snd (min' _ _))
    ; min-≮-right = isMin.right (snd (min' _ _))
    ; min-greatest-< = isMin.greatest (snd (min' _ _))
    }

  isMax->MaxOperationStr : (∀ d1 d2 -> Σ D (isMax d1 d2)) -> MaxOperationStr LO
  isMax->MaxOperationStr max' = record
    { max = \d1 d2 -> fst (max' d1 d2)
    ; max-≮-left = isMax.left (snd (max' _ _))
    ; max-≮-right = isMax.right (snd (max' _ _))
    ; max-least-< = isMax.least (snd (max' _ _))
    }
