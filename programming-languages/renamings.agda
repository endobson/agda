{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.renamings where

open import base
open import container.finmap
open import container.finmap.composition
open import container.finmap.remove
open import equality
open import functions
open import hlevel.base
open import hlevel
open import list
open import nat
open import order
open import order.instances.nat
open import relation
open import sum
open import sigma.base

private
  variable
    ℓ : Level

  Atom : Type₀
  Atom = Nat

  instance
    isSet'-Atom : isSet' Atom
    isSet'-Atom .isSet'.f = isSetNat
  
  DiscreteAtom : Discrete Atom
  DiscreteAtom = decide-nat

  FinSet : Type ℓ -> Type ℓ
  FinSet A = FinMap' A Top

isRenaming : Pred (FinMap' Atom Atom) ℓ-zero
isRenaming = isBijectiveFinMap'

isProp-isRenaming : {m : (FinMap' Atom Atom)} -> isProp (isRenaming m)
isProp-isRenaming =
  isProp× (isPropΠⁱ (\_ -> isPropΠⁱ (\_ -> isPropΠⁱ (\_ -> isPropΠ2 \_ _ -> isSetNat _ _))))
          (isPropΠⁱ (\_ -> isPropΠⁱ (\_ -> isPropΠⁱ (\_ -> isPropΠ2 \_ _ -> isSetNat _ _))))

Renaming : Type₀
Renaming = Σ (FinMap' Atom Atom) isRenaming

-- Lifts a renaming to a function that is constant where in is not defined.
use-renaming : Renaming -> Atom -> Atom
use-renaming (m , isRename) = f m isRename
  where
  f : (m : FinMap' Atom Atom) -> isRenaming m -> Atom -> Atom
  f [] _ a = a
  f (fm-cons a1 a2 m) isRename a3 = 
    case (DiscreteAtom a1 a3) of \{
      (yes _) -> a2 ;
      (no _) -> f m (isBijectiveFinMap'-rest _ isRename) a3}

use-renaming-HasKV : {k v : Atom} (r : Renaming) -> HasKV' k v ⟨ r ⟩ -> use-renaming r k == v
use-renaming-HasKV {k} {v} ((fm-cons k2 v2 m) , r) (has-kv-here kp vp _) with (DiscreteAtom k2 k)
... | (yes _) = sym vp
... | (no k2!=k) = bot-elim (k2!=k (sym kp))
use-renaming-HasKV {k} {v} ((fm-cons k2 v2 m) , r) hkv@(has-kv-skip _ _ hkv') with (DiscreteAtom k2 k)
... | (yes p) = snd r (has-kv-here (sym p) refl m) hkv
... | (no _) = use-renaming-HasKV (m , (isBijectiveFinMap'-rest _ r)) hkv'


use-renaming-¬HasKey : {v : Atom} (r : Renaming) -> ¬ (HasKey' v ⟨ r ⟩) -> use-renaming r v == v
use-renaming-¬HasKey {v} (m , r) ¬hk = handle m r ¬hk
  where
  handle : (m : FinMap' Atom Atom) -> (r : isRenaming m) -> 
           ¬ (HasKey' v m) -> use-renaming (m , r) v == v
  handle [] r ¬hk = refl
  handle (fm-cons k2 v2 m) r ¬hk with (DiscreteAtom k2 v)
  ... | (yes p) = bot-elim (¬hk (v2 , has-kv-here (sym p) refl m))
  ... | (no _) = handle m (isBijectiveFinMap'-rest _ r) (¬hk ∘ HasKey'-skip)

single-renaming : Atom -> Atom -> Renaming
single-renaming a1 a2 = _ , isBijectiveFinMap'-single a1 a2

empty-renaming : Renaming
empty-renaming = _ , isBijectiveFinMap'-[]

single-renaming-unique-value : {k1 v1 k2 v2 : Atom} -> HasKV' k1 v1 ⟨ single-renaming k2 v2 ⟩ -> 
                               (k1 == k2 × v1 == v2)
single-renaming-unique-value (has-kv-here kp vp _) = kp , vp


invert-renaming : Renaming -> Renaming
invert-renaming (m , bij) = fm'-invert m , fm'-invert/bijective m bij

invert-single-renaming :
  {v1 v2 : Atom} -> invert-renaming (single-renaming v1 v2) == single-renaming v2 v1
invert-single-renaming = ΣProp-path isProp-isRenaming refl

invert-empty-renaming : invert-renaming empty-renaming == empty-renaming
invert-empty-renaming = ΣProp-path isProp-isRenaming refl

RenamingExtension : Renaming -> Renaming -> Type₀
RenamingExtension orig result = ⟨ orig ⟩ fm⊆ ⟨ result ⟩

invert-RenamingExtension : 
  {r1 r2 : Renaming} -> RenamingExtension r1 r2 -> 
  RenamingExtension (invert-renaming r1) (invert-renaming r2)
invert-RenamingExtension re {k} {v} hkv = 
  fm'-invert/HasKV (re (subst (HasKV' v k) (fm'-invert/Involution _) (fm'-invert/HasKV hkv)))


record RenamingUnion (left right result : Renaming) : Type₀ where
  field
    forward-left : RenamingExtension left result
    forward-right : RenamingExtension right result
    backward : {k v : Atom} -> HasKV' k v ⟨ result ⟩ -> 
               HasKV' k v ⟨ left ⟩ ⊎ HasKV' k v ⟨ right ⟩

invert-RenamingUnion : 
  {r1 r2 r3 : Renaming} -> RenamingUnion r1 r2 r3 -> 
  RenamingUnion (invert-renaming r1) (invert-renaming r2) (invert-renaming r3)
invert-RenamingUnion {r1} {r2} {r3} ru .RenamingUnion.forward-left = 
  invert-RenamingExtension {r1} {r3} (RenamingUnion.forward-left ru)
invert-RenamingUnion {r1} {r2} {r3} ru .RenamingUnion.forward-right = 
  invert-RenamingExtension {r2} {r3} (RenamingUnion.forward-right ru)
invert-RenamingUnion {r1} {r2} {r3} ru .RenamingUnion.backward {k} {v} hkv = 
  ⊎-map fm'-invert/HasKV fm'-invert/HasKV
        (RenamingUnion.backward ru (subst (HasKV' v k) (fm'-invert/Involution _) (fm'-invert/HasKV hkv)))


RenamingComposition : (left right result : Renaming) -> Type₀
RenamingComposition l r res = FinMapComposition' ⟨ l ⟩ ⟨ r ⟩ ⟨ res ⟩

Σcompose-renamings : (r1 r2 : Renaming) -> Σ Renaming (RenamingComposition r1 r2)
Σcompose-renamings (m1 , r1) (m2 , r2) = 
  (m3 , isBijectiveFinMap-FinMapComposition' r1 r2 c) , c
  where
  m3 = finmap'-compose m1 m2 
  c : FinMapComposition' m1 m2 m3
  c = FinMapComposition'-finmap-compose'

compose-renamings : (r1 r2 : Renaming) -> Renaming
compose-renamings r1 r2 = fst (Σcompose-renamings r1 r2)

RenamingComposition-compose-renamings :
  (r1 r2 : Renaming) -> RenamingComposition r1 r2 (compose-renamings r1 r2)
RenamingComposition-compose-renamings r1 r2 = snd (Σcompose-renamings r1 r2)
  
RenamingComposition-single-renaming :
  {v1 v2 v3 : Atom} ->
  RenamingComposition (single-renaming v1 v2) (single-renaming v2 v3) (single-renaming v1 v3)
RenamingComposition-single-renaming .FinMapComposition'.forward hkv1 hkv2 = 
  (has-kv-here (fst paths1) (snd paths2) [])
  where
  paths1 = single-renaming-unique-value hkv1
  paths2 = single-renaming-unique-value hkv2
RenamingComposition-single-renaming .FinMapComposition'.backward hkv =
  _ , has-kv-here (fst paths) refl [] , has-kv-here refl (snd paths) []
  where
  paths = single-renaming-unique-value hkv

record CompatibleRenamings (r1 r2 : Renaming) : Type₀ where
  field
    domain : {k1 k2 v : Atom} -> HasKV' k1 v ⟨ r1 ⟩ -> HasKV' k2 v ⟨ r2 ⟩ -> k1 == k2
    range : {k v1 v2 : Atom} -> HasKV' k v1 ⟨ r1 ⟩ -> HasKV' k v2 ⟨ r2 ⟩ -> v1 == v2

RenamingUnion->CompatibleRenamings :
  {r1 r2 r3 : Renaming} -> RenamingUnion r1 r2 r3 -> CompatibleRenamings r1 r2
RenamingUnion->CompatibleRenamings {r3 = m3 , i3 , f3 } ru .CompatibleRenamings.domain hkv1 hkv2 = 
  i3 (RenamingUnion.forward-left ru hkv1) (RenamingUnion.forward-right ru hkv2)
RenamingUnion->CompatibleRenamings {r3 = m3 , i3 , f3 } ru .CompatibleRenamings.range hkv1 hkv2 = 
  f3 (RenamingUnion.forward-left ru hkv1) (RenamingUnion.forward-right ru hkv2)


module _ where
  MatchedRenamings : (r1 r2 : Renaming) -> Type₀
  MatchedRenamings r1 r2 = {k v : Atom} -> HasKV' k v ⟨ r1 ⟩ -> Σ[ v2 ∈ Atom ] (HasKV' v v2 ⟨ r2 ⟩)

  RenamingUnion-RenamingComposition :
   {r1 r2 r3 r4 r5 r6 r7 r8 r9 : Renaming} ->
   RenamingUnion r1 r2 r3 ->
   RenamingUnion r4 r5 r6 ->
   RenamingComposition r1 r4 r7 ->
   RenamingComposition r2 r5 r8 ->
   RenamingComposition r3 r6 r9 ->
   MatchedRenamings r1 r4 ->
   MatchedRenamings r2 r5 ->
   RenamingUnion r7 r8 r9
  RenamingUnion-RenamingComposition {r1} {r2} {r3} {r4} {r5} {r6} {r7} {r8} {r9}
    ru123 ru456 rc147 rc258 rc369 m14 m25 = 
    record { forward-left = forward-left ; forward-right = forward-right ; backward = backward }
    where
    forward-left : RenamingExtension r7 r9
    forward-left hkv7 = FinMapComposition'.forward rc369 hkv3 hkv6
      where
      res14 = FinMapComposition'.backward rc147 hkv7
      hkv3 = RenamingUnion.forward-left ru123 (fst (snd res14))
      hkv6 = RenamingUnion.forward-left ru456 (snd (snd res14))
    forward-right : RenamingExtension r8 r9
    forward-right hkv8 = FinMapComposition'.forward rc369 hkv3 hkv6
      where
      res25 = FinMapComposition'.backward rc258 hkv8
      hkv3 = RenamingUnion.forward-right ru123 (fst (snd res25))
      hkv6 = RenamingUnion.forward-right ru456 (snd (snd res25))
    backward : {k v : Atom} -> HasKV' k v ⟨ r9 ⟩ -> 
               HasKV' k v ⟨ r7 ⟩ ⊎ HasKV' k v ⟨ r8 ⟩
    backward {k} {v} hkv9 =
      handle (RenamingUnion.backward ru123 (fst (snd res36)))
             (RenamingUnion.backward ru456 (snd (snd res36)))
      where
      res36 = FinMapComposition'.backward rc369 hkv9
      mid = fst res36
      handle : (HasKV' k mid ⟨ r1 ⟩ ⊎ HasKV' k mid ⟨ r2 ⟩) ->
               (HasKV' mid v ⟨ r4 ⟩ ⊎ HasKV' mid v ⟨ r5 ⟩) ->
               (HasKV' k v ⟨ r7 ⟩ ⊎ HasKV' k v ⟨ r8 ⟩)
      handle (inj-l hkv1) (inj-l hkv4) = inj-l (FinMapComposition'.forward rc147 hkv1 hkv4)
      handle (inj-r hkv2) (inj-r hkv5) = inj-r (FinMapComposition'.forward rc258 hkv2 hkv5)
      handle (inj-l hkv1) (inj-r hkv5) = 
        inj-l (FinMapComposition'.forward rc147 hkv1 (subst (\v -> HasKV' mid v ⟨ r4 ⟩) p (snd hv4)))
        where
        hv4 = m14 hkv1
        cr45 = RenamingUnion->CompatibleRenamings ru456
        p = CompatibleRenamings.range cr45 (snd hv4) hkv5
      handle (inj-r hkv2) (inj-l hkv4) = 
        inj-r (FinMapComposition'.forward rc258 hkv2 (subst (\v -> HasKV' mid v ⟨ r5 ⟩) (sym p) (snd hv5)))
        where
        hv5 = m25 hkv2
        cr45 = RenamingUnion->CompatibleRenamings ru456
        p = CompatibleRenamings.range cr45 hkv4 (snd hv5)
 
 
RenamingUnion-RenamingComposition-left :
 {r1 r2 r3 r4 r5 r6 r7 : Renaming} ->
 RenamingUnion r1 r2 r3 ->
 RenamingComposition r1 r4 r5 ->
 RenamingComposition r2 r4 r6 ->
 RenamingComposition r3 r4 r7 ->
 RenamingUnion r5 r6 r7
RenamingUnion-RenamingComposition-left {r1} {r2} {r3} {r4} {r5} {r6} {r7}
  ru123 rc145 rc246 rc347 =
  record { forward-left = forward-left ; forward-right = forward-right ; backward = backward }
  where
  forward-left : RenamingExtension r5 r7
  forward-left hkv5 = FinMapComposition'.forward rc347 hkv3 hkv4
    where
    res14 = FinMapComposition'.backward rc145 hkv5
    hkv3 = RenamingUnion.forward-left ru123 (fst (snd res14))
    hkv4 = (snd (snd res14))
  forward-right : RenamingExtension r6 r7
  forward-right hkv6 = FinMapComposition'.forward rc347 hkv3 hkv4
    where
    res24 = FinMapComposition'.backward rc246 hkv6
    hkv3 = RenamingUnion.forward-right ru123 (fst (snd res24))
    hkv4 = (snd (snd res24))
  backward : {k v : Atom} -> HasKV' k v ⟨ r7 ⟩ -> 
             HasKV' k v ⟨ r5 ⟩ ⊎ HasKV' k v ⟨ r6 ⟩
  backward hkv7 = 
    ⊎-map (\ hkv1 -> FinMapComposition'.forward rc145 hkv1 hkv4) 
          (\ hkv2 -> FinMapComposition'.forward rc246 hkv2 hkv4)
          res12
    where
    res34 = FinMapComposition'.backward rc347 hkv7
    hkv4 = (snd (snd res34))
    res12 = RenamingUnion.backward ru123 (fst (snd res34))
    

RenamingUnion-RenamingComposition-right :
 {r1 r2 r3 r4 r5 r6 r7 : Renaming} ->
 RenamingUnion r1 r2 r3 ->
 RenamingComposition r4 r1 r5 ->
 RenamingComposition r4 r2 r6 ->
 RenamingComposition r4 r3 r7 ->
 RenamingUnion r5 r6 r7
RenamingUnion-RenamingComposition-right {r1} {r2} {r3} {r4} {r5} {r6} {r7}
  ru123 rc415 rc426 rc437 =
  record { forward-left = forward-left ; forward-right = forward-right ; backward = backward }
  where
  forward-left : RenamingExtension r5 r7
  forward-left hkv5 = FinMapComposition'.forward rc437 hkv4 hkv3
    where
    res41 = FinMapComposition'.backward rc415 hkv5
    hkv3 = RenamingUnion.forward-left ru123 (snd (snd res41))
    hkv4 = (fst (snd res41))
  forward-right : RenamingExtension r6 r7
  forward-right hkv6 = FinMapComposition'.forward rc437 hkv4 hkv3
    where
    res42 = FinMapComposition'.backward rc426 hkv6
    hkv3 = RenamingUnion.forward-right ru123 (snd (snd res42))
    hkv4 = (fst (snd res42))
  backward : {k v : Atom} -> HasKV' k v ⟨ r7 ⟩ -> 
             HasKV' k v ⟨ r5 ⟩ ⊎ HasKV' k v ⟨ r6 ⟩
  backward hkv7 = 
    ⊎-map (\ hkv1 -> FinMapComposition'.forward rc415 hkv4 hkv1) 
          (\ hkv2 -> FinMapComposition'.forward rc426 hkv4 hkv2)
          res12
    where
    res43 = FinMapComposition'.backward rc437 hkv7
    hkv4 = (fst (snd res43))
    res12 = RenamingUnion.backward ru123 (snd (snd res43))

renaming-source-atoms : Renaming -> FinSet Atom
renaming-source-atoms r = fm'-keys ⟨ r ⟩

renaming-target-atoms : Renaming -> FinSet Atom
renaming-target-atoms r = fm'-keys (fm'-invert ⟨ r ⟩)

isFreshBoundOfRenaming : (r : Renaming) (v : Atom) -> Type₀
isFreshBoundOfRenaming r b = 
  (a : Atom) -> b ≤ a -> ¬ (Σ[ k ∈ Atom ] (HasKV' k a ⟨ r ⟩)) ×
                         ¬ (Σ[ v ∈ Atom ] (HasKV' a v ⟨ r ⟩))

computeFreshBoundOfRenaming : (r : Renaming) -> Σ Atom (isFreshBoundOfRenaming r)
computeFreshBoundOfRenaming (m , _) = handle m
  where
  isFreshBoundOfMap : (m : FinMap' Atom Atom) (v : Atom) -> Type₀
  isFreshBoundOfMap m b = 
    (a : Atom) -> b ≤ a -> ¬ (Σ[ k ∈ Atom ] (HasKV' k a m)) ×
                           ¬ (Σ[ v ∈ Atom ] (HasKV' a v m))


  handle : (m : FinMap' Atom Atom) -> Σ Atom (isFreshBoundOfMap m)
  handle [] = 0 , \a lt -> ((\{(_ , ())}) , (\{(_ , ())}))
  handle fm@(fm-cons k v m) = ans , freshBound
    where
    rec = handle m
    ans = max (suc (max k v)) (fst rec)
    
    freshBound : isFreshBoundOfMap fm ans
    freshBound a ans≤a = case-k , case-v
      where
      case-k : ¬ (Σ[ k ∈ Atom ] (HasKV' k a fm))
      case-k (_ , has-kv-here kp vp _) = irrefl-< lt
        where
        lt : v < v
        lt = (trans-<-≤
               (suc-≤ ≤-max-right)
               (trans-≤ (≤-max-left {suc (max k v)} {fst rec}) (trans-≤ ans≤a (path-≤ vp))))
      case-k (k , has-kv-skip _ _ hkv) =
        fst ((snd rec) a (trans-≤ ≤-max-right ans≤a)) (k , hkv)

      case-v : ¬ (Σ[ v ∈ Atom ] (HasKV' a v fm))
      case-v (_ , has-kv-here kp vp _) = irrefl-< lt
        where
        lt : k < k
        lt = (trans-<-≤
               (suc-≤ ≤-max-left)
               (trans-≤ (≤-max-left {suc (max k v)} {fst rec}) (trans-≤ ans≤a (path-≤ kp))))
      case-v (v , has-kv-skip _ _ hkv) =
        snd ((snd rec) a (trans-≤ ≤-max-right ans≤a)) (v , hkv)

renaming-union : (r1 r2 : Renaming) -> CompatibleRenamings r1 r2 ->
                 Σ[ r3 ∈ Renaming ] (RenamingUnion r1 r2 r3)
renaming-union ren1@(r1 , is-r1) ren2@(r2 , is-r2) c = ren , ru
  where
  fm = fm'-union r1 r2 

  isInj : isInjectiveFinMap' fm
  isInj {k1} {k2} {v} hk1 hk2 = handle (HasKV-fm'-union/split _ _ hk1) (HasKV-fm'-union/split _ _ hk2)
    where
    handle : (HasKV' k1 v r1 ⊎ HasKV' k1 v r2) ->
             (HasKV' k2 v r1 ⊎ HasKV' k2 v r2) ->
             k1 == k2
    handle (inj-l hkv1) (inj-l hkv2) = fst is-r1 hkv1 hkv2
    handle (inj-l hkv1) (inj-r hkv2) = 
      CompatibleRenamings.domain c hkv1 hkv2
    handle (inj-r hkv1) (inj-l hkv2) =
      sym (CompatibleRenamings.domain c hkv2 hkv1)
    handle (inj-r hkv1) (inj-r hkv2) = fst is-r2 hkv1 hkv2

  isFun : isFunctionalFinMap' fm
  isFun {k} {v1} {v2} hk1 hk2 = handle (HasKV-fm'-union/split _ _ hk1) (HasKV-fm'-union/split _ _ hk2)
    where
    handle : (HasKV' k v1 r1 ⊎ HasKV' k v1 r2) ->
             (HasKV' k v2 r1 ⊎ HasKV' k v2 r2) ->
             v1 == v2
    handle (inj-l hkv1) (inj-l hkv2) = snd is-r1 hkv1 hkv2
    handle (inj-l hkv1) (inj-r hkv2) = 
      CompatibleRenamings.range c hkv1 hkv2
    handle (inj-r hkv1) (inj-l hkv2) =
      sym (CompatibleRenamings.range c hkv2 hkv1)
    handle (inj-r hkv1) (inj-r hkv2) = snd is-r2 hkv1 hkv2

  ren : Renaming
  ren = (fm , isInj , isFun)
  ru : RenamingUnion ren1 ren2 ren
  ru .RenamingUnion.forward-left = HasKV-fm'-union/left
  ru .RenamingUnion.forward-right = HasKV-fm'-union/right
  ru .RenamingUnion.backward hk = HasKV-fm'-union/split _ _ hk


retractions-compatible : (r1 r2 r3 : Renaming) -> 
                         RenamingExtension r1 r3 ->
                         RenamingExtension r2 r3 ->
                         CompatibleRenamings r1 r2
retractions-compatible r1 r2 r3 ext13 ext23 = record { range = range ; domain = domain }
  where
  range : {k v1 v2 : Atom} -> HasKV' k v1 ⟨ r1 ⟩ -> HasKV' k v2 ⟨ r2 ⟩ -> v1 == v2
  range hkv1 hkv2 = (snd (snd r3)) (ext13 hkv1) (ext23 hkv2)
  domain : {k1 k2 v : Atom} -> HasKV' k1 v ⟨ r1 ⟩ -> HasKV' k2 v ⟨ r2 ⟩ -> k1 == k2
  domain hkv1 hkv2 = (fst (snd r3)) (ext13 hkv1) (ext23 hkv2)

retractions-union : (r1 r2 r3 r4 : Renaming) -> 
                    RenamingExtension r1 r3 ->
                    RenamingExtension r2 r3 ->
                    RenamingUnion r1 r2 r4 ->
                    RenamingExtension r4 r3
retractions-union r1 r2 r3 r4 ext13 ext23 u124 hkv4 = 
  either ext13 ext23 (RenamingUnion.backward u124 hkv4)

-- Try to do recursion over singular entries

renaming-remove : Atom -> Renaming -> Renaming
renaming-remove k (m , r) = m' , r'
  where
  m' = finmap'-remove k m 
  r' = isBijective-fm⊆ (fm⊆-finmap'-remove k m) r

module RenamingRec where

  module _ {ℓ : Level} {R : Type ℓ} 
           (base : R) (step : (Atom -> Atom -> R -> R))
    where
    private
      sized-entry-rec : (n : Nat) (r : Renaming) -> fm'-size ⟨ r ⟩ ≤ n -> R
      sized-entry-rec n ([] , _) _ = base
      sized-entry-rec zero (fm-cons k v _ , _) lt = bot-elim (zero-≮ lt)
      sized-entry-rec (suc n) (fm-cons k v m , isBij) lt = 
        step k v (sized-entry-rec n (m' , isBij') (trans-≤ (fm'-size-finmap'-remove k m) (pred-≤ lt)))
        where
        m' = finmap'-remove k m 
        isBij' = isBijective-fm⊆ (fm⊆-finmap'-remove k m) (isBijectiveFinMap'-rest _ isBij)

    entry-rec : Renaming -> R
    entry-rec r = sized-entry-rec (fm'-size ⟨ r ⟩) r refl-≤

  private
    renaming-entries : Renaming -> List (Atom × Atom)
    renaming-entries = entry-rec [] (\k v -> (k , v) ::_)
    
  data EntryStructure (r : Renaming) : Type₀ where
    entries-empty : ¬(Σ[ k ∈ Atom ] HasKey' k ⟨ r ⟩) -> EntryStructure r
    entries-cons : (k v : Atom) -> HasKV' k v ⟨ r ⟩ ->
                   EntryStructure (renaming-remove v r) ->
                   EntryStructure r
    
  -- renaming-entry-structure : (r : Renaming) -> EntryStructure r
  -- renaming-entry-structure r = handle (fm'-size ⟨ r ⟩) r refl-≤
  --   where
  --   handle : (n : Nat) (r : Renaming) -> fm'-size ⟨ r ⟩ ≤ n -> EntryStructure r
  --   handle _ ([] , _) _ = entries-empty (\())
  --   handle zero      (fm-cons _ _ _ , _) lt = bot-elim (zero-≮ lt)
  --   handle (suc n) r@(fm-cons k v m , _) lt = 
  --     entries-cons k v (has-kv-here refl refl m) 
  --       (handle n (renaming-remove v r) (pred-≤ lt'))
  --     where
  --     lt' : (fm'-size ⟨ renaming-remove v r ⟩) < suc n
  --     lt' = ?



