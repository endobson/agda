{-# OPTIONS --cubical --safe --exact-split #-}

module equality.identity-system where

open import base
open import cubical
open import equality-path
open import equivalence
open import hlevel
open import isomorphism
open import relation
open import sigma.base
open import univalence

record isIdentitySystem {ℓA ℓR} {A : Type ℓA} (R : Rel A ℓR)
                        (refl : (a : A) -> R a a) : Type (ℓ-max ℓA ℓR) where
  field
    to-path : {a1 a2 : A} -> R a1 a2 -> a1 == a2
    to-path-over : {a1 a2 : A} -> (r : R a1 a2) ->
                   PathP (\i -> R a1 (to-path r i)) (refl a1) r

  isContr-ΣR : {a : A} -> isContr (Σ A (R a))
  isContr-ΣR {a} .fst = a , refl a
  isContr-ΣR {a} .snd (_ , r2) i = to-path r2 i , to-path-over r2 i


-- Some existing identity systems
isIdentitySystem-Path : {ℓA : Level} {A : Type ℓA} -> isIdentitySystem (\a1 a2 -> Path A a1 a2) reflᵉ
isIdentitySystem-Path = record
  { to-path = \p -> p
  ; to-path-over = \p i j -> p (i ∧ j)
  }

isIdentitySystem-Equiv : {ℓA ℓR : Level} {A : Type ℓA} {R : Rel A ℓR}
                         (eq : (∀ {a b} -> (a == b) ≃ R a b)) ->
                         isIdentitySystem R (\_ -> eqFun eq refl)
isIdentitySystem-Equiv {A = A} {R = R} eq = record
  { to-path = eqInv eq
  ; to-path-over = \r -> transP-left (\i -> eqFun eq (\j -> eqInv eq r (i ∧ j))) (eqSec eq r)
  }

-- Isos are an identity system for hSets

isIdentitySystem-Iso : {ℓ : Level} ->
  isIdentitySystem (\(a b : hSet ℓ) -> Iso (fst a) (fst b)) (\_ -> id-iso)
isIdentitySystem-Iso .isIdentitySystem.to-path i = ΣProp-path isProp-isSet (isoToPath i)
isIdentitySystem-Iso .isIdentitySystem.to-path-over {a , sa} {b , sb} i =
  transP-left (transport-filler (\j -> Iso a (isoToPath i j)) id-iso)
              (isSet-iso-path sa sb (\j e -> transport-isoToPath i j (transportRefl e j)))

-- J rule for identity systems

module _ {ℓA ℓR : Level} {A : Type ℓA} {R : Rel A ℓR} {r0 : (a : A) -> R a a}
         (ids : isIdentitySystem R r0) (a : A) where
  private
    module ids = isIdentitySystem ids

  Ids-Σrefl : Path (Path (Σ A (R a)) (a , r0 a) (a , r0 a))
                   (\i -> ids.to-path (r0 a) i , ids.to-path-over (r0 a) i)
                   refl
  Ids-Σrefl = isSet->Square (isProp->isSet (isContr->isProp ids.isContr-ΣR))

  Ids-refl : ids.to-path (r0 a) == refl
  Ids-refl i j = fst (Ids-Σrefl i j)

  Ids-refl-over : PathP (\j -> PathP (\i -> R a (Ids-refl j i)) (r0 a) (r0 a))
                        (ids.to-path-over (r0 a)) refl
  Ids-refl-over i j = snd (Ids-Σrefl i j)


module _ {ℓA ℓR ℓP : Level} {A : Type ℓA} {R : Rel A ℓR} {r0 : (a : A) -> R a a} {a : A}
         (ids : isIdentitySystem R r0)
         (P : (b : A) (r : R a b) -> Type ℓP)
         (P-refl : P a (r0 a)) where
  private
    module ids = isIdentitySystem ids
    P' : Σ A (R a) -> Type _
    P' (b , r) = P b r

  IdsJ : {b : A} (r : R a b) -> P b r
  IdsJ {b} r = transport (\i -> P (ids.to-path r i) (ids.to-path-over r i)) P-refl

  IdsJ-refl : (IdsJ (r0 a)) == P-refl
  IdsJ-refl = (\j -> transport (\i -> P' (Ids-Σrefl ids a j i)) P-refl) >=>
              transportRefl P-refl

-- Path introduction for identity systems
module _ {ℓA ℓR : Level} {A : Type ℓA} {R : Rel A ℓR} {r0 : (a : A) -> R a a}
         {ids1 ids2 : isIdentitySystem R r0} where
  private
    module ids1 = isIdentitySystem ids1
    module ids2 = isIdentitySystem ids2
  isIdentitySystem-path :
    ({a b : A} (r : R a b) ->
      Σ[ p ∈ (ids1.to-path r == ids2.to-path r) ]
        PathP (\i -> PathP (\j -> R a (p i j)) (r0 a) r)
          (ids1.to-path-over r) (ids2.to-path-over r)) ->
    ids1 == ids2
  isIdentitySystem-path ps i .isIdentitySystem.to-path r = fst (ps r) i
  isIdentitySystem-path ps i .isIdentitySystem.to-path-over r = snd (ps r) i


-- Show that isIdentitySystem is the equivalent of being R-contractable
private
  isContr-ΣR->isIdentitySystem :
    {ℓA ℓR : Level} {A : Type ℓA} (R : Rel A ℓR) (r : (a : A) -> R a a) ->
    ((a : A) -> isContr (Σ A (R a))) -> isIdentitySystem R r
  isContr-ΣR->isIdentitySystem {A = A} R refl' ctr = record
    { to-path = (\r i -> fst (path r i))
    ; to-path-over = (\r i -> snd (path r i))
    }
    where
    isProp-ΣR : (a : A) -> isProp (Σ A (R a))
    isProp-ΣR a = isContr->isProp (ctr a)

    path : {a b : A} -> (r : R a b) -> (a , refl' a) == (b , r)
    path {a} {b} r = isProp-ΣR a (a , refl' a) (b , r)

isContr-ΣR≃isIdentitySystem :
  {ℓA ℓR : Level} {A : Type ℓA} (R : Rel A ℓR) (r : (a : A) -> R a a) ->
  ((a : A) -> isContr (Σ A (R a))) ≃ isIdentitySystem R r
isContr-ΣR≃isIdentitySystem {A = A} R refl' = isoToEquiv (iso f b fb bf)
  where
  f = isContr-ΣR->isIdentitySystem R refl'
  b = \ids a -> isIdentitySystem.isContr-ΣR ids {a}
  fb : ∀ ids -> (f (b ids)) == ids
  fb ids = isIdentitySystem-path ps
    where
    ids2 : isIdentitySystem R refl'
    ids2 = f (b ids)
    module ids = isIdentitySystem ids
    module ids2 = isIdentitySystem ids2

    module _ {a : A} where
      P : (b : A) (r : R a b) -> Type _
      P b r =
        Σ[ p ∈ (ids2.to-path r == ids.to-path r) ]
          PathP (\i -> PathP (\j -> R a (p i j)) (refl' a) r)
            (ids2.to-path-over r) (ids.to-path-over r)

      P0 : P a (refl' a)
      P0 = p0 , p1
        where
        pl = Ids-refl ids2 a
        pr = sym (Ids-refl ids a)
        p0 : ids2.to-path (refl' a) == ids.to-path (refl' a)
        p0 = pl >=> pr

        liftR : {p1 p2 : a == a} -> p1 == p2 -> I -> Type _
        liftR p = (\i -> PathP (\j -> R a (p i j)) (refl' a) (refl' a))

        A' = \i -> liftR pl i
        B' = \i -> liftR pr i
        AB'1 = A' >=> B'
        AB'2 = \i -> liftR p0 i

        AB-path : AB'1 == AB'2
        AB-path =
          cong-trans (\ap -> PathP (\j -> R a (ap j)) (refl' a) (refl' a))
            (Ids-refl ids2 a) (sym (Ids-refl ids a))

        p1' : PathP (\i -> AB'1 i) (ids2.to-path-over (refl' a)) (ids.to-path-over (refl' a))
        p1' = transP (Ids-refl-over ids2 a) (symP (Ids-refl-over ids a))


        p1 : PathP (\i -> AB'2 i) (ids2.to-path-over (refl' a)) (ids.to-path-over (refl' a))
        p1 = transport
              (\k -> PathP (\i -> AB-path k i)
                      (ids2.to-path-over (refl' a)) (ids.to-path-over (refl' a)))
              p1'

      ps : {b : A} (r : R a b) -> P b r
      ps {b} = IdsJ ids P P0

  bf : ∀ ctr -> (b (f ctr)) == ctr
  bf ctr = isPropΠ (\_ -> isProp-isContr) (b (f ctr)) ctr

-- Show that if we have an IdentitySystem on R then to-path is an equivalence between
-- R and the path type.
isIdentitySystem->isEquiv : ∀ {ℓA ℓR} {A : Type ℓA} {R : Rel A ℓR} {r} ->
  (ids : isIdentitySystem R r) -> ∀ {a b : A} -> isEquiv (isIdentitySystem.to-path ids {a} {b})
isIdentitySystem->isEquiv {A = A} {R = R} {r = refl'}
  ids@(record {to-path = to-path ; to-path-over = to-path-over }) =
  isoToIsEquiv (iso forward backward fb bf)
  where
  forward : {a b : A} -> R a b -> a == b
  forward = to-path

  backward : {a b : A} -> a == b -> R a b
  backward {a} p = transport (\i -> R a (p i)) (refl' a)

  refl-case : {a : A} -> to-path (refl' a) == refl
  refl-case {a} i j = fst (sq i j)
    where
    sq : Square {A = (Σ A (R a))}
           (\i -> (to-path (refl' a) i , to-path-over (refl' a) i))
           (\i -> (a , refl' a))
           (\i -> (a , refl' a))
           (\i -> (a , refl' a))
    sq = isSet->Square (isProp->isSet (isContr->isProp (isIdentitySystem.isContr-ΣR ids)))

  fb : {a b : A} (p : a == b) -> (forward (backward p)) == p
  fb {a} {b} = J (\ b p -> (forward (backward p)) == p)
                 ans
    where
    ans : to-path (transport refl (refl' a)) == refl
    ans = cong to-path (transportRefl (refl' a)) >=> refl-case

  bf : {a b : A} (r : R a b) -> (backward (forward r)) == r
  bf {a} {b} = IdsJ ids (\b r -> (backward (forward r)) == r) check
    where
    check : transport (\i -> R a (to-path (refl' a) i)) (refl' a) == (refl' a)
    check = (\j -> transport (\i -> R a (refl-case {a} j i)) (refl' a)) >=>
            transportRefl (refl' a)
