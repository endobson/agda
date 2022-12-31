{-# OPTIONS --cubical --safe --exact-split #-}

open import additive-group
open import additive-group.instances.nat
open import base
open import category.base
open import category.instances.quiver
open import category.set
open import cubical
open import equality-path
open import equivalence
open import fin
open import fin-algebra
open import functions
open import hlevel
open import isomorphism
open import list
open import maybe
open import nat
open import order
open import order.instances.nat
open import ordered-semiring
open import ordered-semiring.instances.nat
open import sigma.base
open import type-algebra

module category.instances.free where

module _ {ℓ : Level} (Q : Quiver ℓ) where
  private
    module Q = Functor Q
    V' : hSet ℓ
    V' = Q.F-obj wq-vertices
    V : Type ℓ
    V = ⟨ V' ⟩
    E' : hSet ℓ
    E' = Q.F-obj wq-edges
    E : Type ℓ
    E = ⟨ E' ⟩
    source : E -> V
    source = SetFunction.f (Q.F-mor wq-source)
    target : E -> V
    target = SetFunction.f (Q.F-mor wq-source)

  data Edge : V -> V -> Type ℓ where
    edge : (e : E) -> Edge (source e) (target e)

  data EPath (v1 : V) : V -> Type ℓ where
    empty-path : EPath v1 v1
    edge-path : {v2 v3 : V} -> Edge v1 v2 -> EPath v2 v3 -> EPath v1 v3

  private
    ΣEdge≃E : (Σ[ v1 ∈ V ] Σ[ v2 ∈ V ] Edge v1 v2) ≃ E
    ΣEdge≃E = isoToEquiv (iso f g (\_ -> refl) gf)
      where
      f : (Σ[ v1 ∈ V ] Σ[ v2 ∈ V ] Edge v1 v2) -> E
      f (_ , _ , edge e) = e
      g : E -> (Σ[ v1 ∈ V ] Σ[ v2 ∈ V ] Edge v1 v2)
      g e = (source e , target e , edge e)
      gf : ∀ e -> g (f e) == e
      gf (_ , _ , edge _) = refl

    Edge≃ΣE : ∀ {v1} {v2} -> (Edge v1 v2) ≃ (Σ[ e ∈ E ] (source e == v1 × target e == v2))
    Edge≃ΣE = isoToEquiv (iso f g fg gf)
      where
      f : ∀ {v1} {v2} -> Edge v1 v2 -> (Σ[ e ∈ E ] (source e == v1 × target e == v2))
      f (edge e) = e , refl , refl

      g : ∀ {v1} {v2} -> (Σ[ e ∈ E ] (source e == v1 × target e == v2)) -> Edge v1 v2
      g (e , p1 , p2) = transport (\i -> Edge (p1 i) (p2 i)) (edge e)

      fib : ∀ {v1} {v2} i -> fiber (f {v1} {v2}) i
      fib {v1} {v2} (e , p1 , p2) = ans , ans-path 
        where
        ans : Edge v1 v2
        ans = transport (\i -> Edge (p1 i) (p2 i)) (edge e)
        ans-path : f ans == (e , p1 , p2)
        ans-path = p8
          where
          p4' : I -> Type ℓ 
          p4' i = (Σ[ e ∈ E ] (source e == (p1 (~ i)) × target e == (p2 (~ i))))

          p4 : PathP (\i -> p4' i) (e , p1 , p2) (e , refl , refl) 
          p4 i = e , (\j -> p1 (j ∧ (~ i))) , (\j -> p2 (j ∧ (~ i)))

          p5 : PathP (\i -> p4' i) (f ans) (e , refl , refl) 
          p5 i = f (transport-filler (\i -> Edge (p1 i) (p2 i)) (edge e) (~ i))

          p8 : (f ans) == (e , p1 , p2)
          p8 = transP-sym p5 (symP p4) 

      fg : ∀ {v1} {v2} (i : (Σ[ e ∈ E ] (source e == v1 × target e == v2))) -> f (g i) == i
      fg i = (snd (fib i))

      gf : ∀ {v1} {v2} (e : Edge v1 v2) -> g (f e) == e
      gf (edge e) = transportRefl _

    isSet-Edge : ∀ {v1} {v2} -> isSet (Edge v1 v2)
    isSet-Edge = 
      ≃-isSet (equiv⁻¹ Edge≃ΣE) 
              (isSetΣ (snd E') (\_ -> isProp->isSet (isProp× (snd V' _ _) (snd V' _ _))))
      

    id-EPath : {v : V} -> EPath v v
    id-EPath = empty-path

    compose-EPath : {v1 v2 v3 : V} -> EPath v1 v2 -> EPath v2 v3 -> EPath v1 v3
    compose-EPath (empty-path) ep = ep
    compose-EPath (edge-path e1 ep1) ep2 = 
      edge-path e1 (compose-EPath ep1 ep2)

    compose-EPath-leftId : {v1 v2 : V} -> (ep : EPath v1 v2) -> (compose-EPath id-EPath ep) == ep
    compose-EPath-leftId ep = refl

    compose-EPath-rightId : {v1 v2 : V} -> (ep : EPath v1 v2) -> (compose-EPath ep id-EPath) == ep
    compose-EPath-rightId (empty-path) = refl
    compose-EPath-rightId (edge-path e ep) = cong (edge-path e) (compose-EPath-rightId ep)

    compose-EPath-assoc : {v1 v2 v3 v4 : V} -> 
                          (ep1 : EPath v1 v2) (ep2 : EPath v2 v3) (ep3 : EPath v3 v4) ->
                          (compose-EPath (compose-EPath ep1 ep2) ep3) ==
                          (compose-EPath ep1 (compose-EPath ep2 ep3))
    compose-EPath-assoc empty-path ep2 ep3 = refl
    compose-EPath-assoc (edge-path e ep1) ep2 ep3 = 
      cong (edge-path e) (compose-EPath-assoc ep1 ep2 ep3)

  FreeCat : PreCategory ℓ ℓ
  FreeCat = record
    { Obj = V
    ; Mor = EPath
    ; id = id-EPath
    ; _⋆_ = compose-EPath
    ; ⋆-left-id = compose-EPath-leftId
    ; ⋆-right-id = compose-EPath-rightId
    ; ⋆-assoc = compose-EPath-assoc
    }
  private
    
  
    data EPath' (v1 v2 : V) : Type ℓ where
      empty-path : v1 == v2 -> EPath' v1 v2
      edge-path : {v3 : V} -> Edge v1 v3 -> EPath' v3 v2 -> EPath' v1 v2
  
    EPath->EPath' : {v1 v2 : V} -> EPath v1 v2 -> EPath' v1 v2
    EPath->EPath' empty-path = empty-path refl
    EPath->EPath' (edge-path e ep) = edge-path e (EPath->EPath' ep)
  
    EPath'->EPath : {v1 v2 : V} -> EPath' v1 v2 -> EPath v1 v2
    EPath'->EPath {v1} (empty-path p) = transport (\i -> EPath v1 (p i)) empty-path 
    EPath'->EPath (edge-path e ep) = edge-path e (EPath'->EPath ep)
  
    EPath->EPath'->EPath : {v1 v2 : V} -> (e : EPath v1 v2) -> EPath'->EPath (EPath->EPath' e) == e
    EPath->EPath'->EPath empty-path = transportRefl empty-path
    EPath->EPath'->EPath (edge-path e ep) = cong (edge-path e) (EPath->EPath'->EPath ep)
  
  
    EPath-length : {v1 v2 : V} -> EPath v1 v2 -> Nat
    EPath-length empty-path = 0
    EPath-length (edge-path _ ep) = suc (EPath-length ep)
  
    EPathN : (v1 v2 : V) (n : Nat) -> Type ℓ
    EPathN v1 v2 n = Σ[ e ∈ EPath v1 v2 ] (EPath-length e == n)
  
    EPath'-length : {v1 v2 : V} -> EPath' v1 v2 -> Nat
    EPath'-length (empty-path _) = 0
    EPath'-length (edge-path _ ep) = suc (EPath'-length ep)
  
    EPath'N : (v1 v2 : V) (n : Nat) -> Type ℓ
    EPath'N v1 v2 n = Σ[ e ∈ EPath' v1 v2 ] (EPath'-length e == n)
  
    ZeroPath-eq : {v1 v2 : V} -> (EPath'N v1 v2 0) ≃ (v1 == v2)
    ZeroPath-eq {v1} {v2} = isoToEquiv (iso to-path to-EPath0 to-path-to-EPath0 to-EPath0-to-path)
      where
      to-path : (EPath'N v1 v2 0) -> v1 == v2
      to-path (empty-path p , _) = p
      to-path (edge-path _ _ , p) = zero-suc-absurd (sym p)
  
      to-EPath0 : v1 == v2 -> (EPath'N v1 v2 0)
      to-EPath0 vp = empty-path vp , refl
  
      to-path-to-EPath0 : ∀ p -> to-path (to-EPath0 p) == p
      to-path-to-EPath0 _ = refl
  
      to-EPath0-to-path : ∀ p -> to-EPath0 (to-path p) == p
      to-EPath0-to-path (empty-path p , _) = ΣProp-path (isSetNat _ _) refl
      to-EPath0-to-path (edge-path _ _ , p) = zero-suc-absurd (sym p)
  
    SucPath-eq : {v1 v2 : V} (n : Nat) -> 
                 (EPath'N v1 v2 (suc n) ≃ (Σ[ v3 ∈ V ] (Edge v1 v3 × EPath'N v3 v2 n)))
    SucPath-eq {v1} {v2} n = isoToEquiv (iso f g fg gf)
      where
      f : EPath'N v1 v2 (suc n) -> (Σ[ v3 ∈ V ] (Edge v1 v3 × EPath'N v3 v2 n))
      f (empty-path _ , p) = zero-suc-absurd p
      f (edge-path {v3} e ep , p) = v3 , e , (ep , suc-injective p)
      g : (Σ[ v3 ∈ V ] (Edge v1 v3 × EPath'N v3 v2 n)) -> EPath'N v1 v2 (suc n)
      g (v , e , (ep , p)) = edge-path e ep , cong suc p
  
      fg : ∀ p -> f (g p) == p
      fg (v , e , (ep , p)) i = v , e , (ep , isSetNat _ _ (suc-injective (cong suc p)) p i)
  
      gf : ∀ p -> g (f p) == p
      gf (empty-path _ , p) = zero-suc-absurd p
      gf (edge-path {v3} e ep , p) i = edge-path e ep , isSetNat _ _ (cong suc (suc-injective p)) p i
  
    isSet-EPath'N : {v1 v2 : V} (n : Nat) -> isSet (EPath'N v1 v2 n)
    isSet-EPath'N {v1} {v2} zero = ≃-isSet (equiv⁻¹ ZeroPath-eq) (isProp->isSet (snd V' _ _))
    isSet-EPath'N {v1} {v2} (suc n) = 
      ≃-isSet (equiv⁻¹ (SucPath-eq n)) 
        (isSetΣ (snd V') (\v -> isSet× isSet-Edge (isSet-EPath'N n)))
  
    EPath'≃ΣEPath'N : {v1 v2 : V} -> EPath' v1 v2 ≃ Σ Nat (EPath'N v1 v2)
    EPath'≃ΣEPath'N {v1} {v2} = isoToEquiv (iso f g fg (\_ -> refl))
      where
      f : EPath' v1 v2 -> Σ Nat (EPath'N v1 v2)
      f e = (EPath'-length e , (e , refl))
  
      g : Σ Nat (EPath'N v1 v2) -> EPath' v1 v2 
      g (_ , (e , _)) = e
  
      fg : ∀ e -> f (g e) == e
      fg (n , (e , p)) = \i -> p i , e , (\j -> p (i ∧ j))

  abstract
    isSet-EPath : {v1 v2 : V} -> isSet (EPath v1 v2)
    isSet-EPath {v1} {v2} = 
      isSet-Retract EPath->EPath' EPath'->EPath EPath->EPath'->EPath
        (≃-isSet (equiv⁻¹ EPath'≃ΣEPath'N) 
          (isSetΣ isSetNat isSet-EPath'N))
    
module _ {ℓ : Level} {Q : Quiver ℓ} where
  instance
    isCategory-FreeCat : isCategory (FreeCat Q)
    isCategory-FreeCat .isCategory.isSet-Mor = isSet-EPath Q
