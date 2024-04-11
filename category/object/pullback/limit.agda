{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.pullback.limit where

open import base
open import category.base
open import category.constructions.cone
open import category.functor
open import category.limits
open import category.object.pullback
open import category.object.pullback.limit-category
open import category.object.terminal
open import equality-path
open import hlevel
open import isomorphism
open import relation
open import sigma
open import truncation
open import univalence

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  open CategoryHelpers C

  module _ {a b c : Obj C} (f : C [ a , c ]) (g : C [ b , c ]) where
    PullbackDiagram : Diagram PullbackC C
    PullbackDiagram = record
      { obj =
        \{ nodeA -> a
         ; nodeB -> b
         ; nodeC -> c
         }
      ; mor =
        \{ {nodeA} {nodeA} (pmor pathAA) -> id C
         ; {nodeA} {nodeC} (pmor pathAC) -> f
         ; {nodeB} {nodeB} (pmor pathBB) -> id C
         ; {nodeB} {nodeC} (pmor pathBC) -> g
         ; {nodeC} {nodeC} (pmor pathCC) -> id C
         }
      ; id =
        \{ nodeA -> refl
         ; nodeB -> refl
         ; nodeC -> refl
         }
      ; ⋆ =
        \{ {nodeA} {nodeA} {nodeA} (pmor pathAA) (pmor pathAA) -> sym ⋆-id²
         ; {nodeA} {nodeA} {nodeC} (pmor pathAA) (pmor pathAC) -> sym ⋆-left-id
         ; {nodeA} {nodeC} {nodeC} (pmor pathAC) (pmor pathCC) -> sym ⋆-right-id
         ; {nodeB} {nodeB} {nodeB} (pmor pathBB) (pmor pathBB) -> sym ⋆-id²
         ; {nodeB} {nodeB} {nodeC} (pmor pathBB) (pmor pathBC) -> sym ⋆-left-id
         ; {nodeB} {nodeC} {nodeC} (pmor pathBC) (pmor pathCC) -> sym ⋆-right-id
         ; {nodeC} {nodeC} {nodeC} (pmor pathCC) (pmor pathCC) -> sym ⋆-id²
         }
      }

    private
      PC = PullbackC
      D = PullbackDiagram

      CSquare : Type (ℓ-max ℓO ℓM)
      CSquare = Σ[ o ∈ Obj C ] Σ[ π₁ ∈ C [ o , a ] ] Σ[ π₂ ∈ C [ o , b ] ] (π₁ ⋆ f == π₂ ⋆ g)

      cone->csquare : Cone D -> CSquare
      cone->csquare (o , cs) = o , ConeStr.component cs nodeA , ConeStr.component cs nodeB , comm
        where
        comm = ConeStr.component-compose cs (pmor pathAC) >=>
               sym (ConeStr.component-compose cs (pmor pathBC))

      csquare->cone : CSquare -> Cone D
      csquare->cone (o , π₁ , π₂ , comm) = o , record
        { component = nodes
        ; component-compose = edges _ _
        }
        where
        nodes : (n : Obj PC) -> C [ o , F-obj D n ]
        nodes nodeA = π₁
        nodes nodeB = π₂
        nodes nodeC = π₁ ⋆ f

        edges : (x y : Obj PC) -> (p : PC [ x , y ]) ->
                nodes x ⋆ F-mor D p == nodes y
        edges nodeA nodeA (pmor pathAA) = ⋆-right-id
        edges nodeA nodeC (pmor pathAC) = refl
        edges nodeB nodeB (pmor pathBB) = ⋆-right-id
        edges nodeB nodeC (pmor pathBC) = sym comm
        edges nodeC nodeC (pmor pathCC) = ⋆-right-id

      cone<->csquare : Iso (Cone D) CSquare
      cone<->csquare .Iso.fun = cone->csquare
      cone<->csquare .Iso.inv = csquare->cone
      cone<->csquare .Iso.rightInv cs@(o , π₁ , π₂ , comm)  =
        cong (\c -> o , π₁ , π₂ , c) (isSet-Mor C _ _ _ _)
      cone<->csquare .Iso.leftInv (o , cs) =
        cong (o ,_) (cone-str-path D nodes)
        where
        cs' = snd (csquare->cone (cone->csquare (o , cs)))
        nodes : ∀ j -> ConeStr.component cs' j == ConeStr.component cs j
        nodes nodeA = refl
        nodes nodeB = refl
        nodes nodeC = ConeStr.component-compose cs (pmor pathAC)

      isPullbackSquare : Pred CSquare _
      isPullbackSquare (o , π₁ , π₂ , _) =
        ∀ ((o' , π₁' , π₂' , _) : CSquare) ->
        ∃![ h ∈ C [ o' , o ] ] (h ⋆ π₁ == π₁' × h ⋆ π₂ == π₂')

      isProp-isPullbackSquare : (cs : CSquare) -> isProp (isPullbackSquare cs)
      isProp-isPullbackSquare _ = isPropΠ (\_ -> isProp-isContr)

      module _ (cs@(o , π₁ , π₂ , _) : CSquare) where
        private
          module _ (cs'@(o' , π₁' , π₂' , _) : CSquare) where
            eq : Iso (ConeC D [ (csquare->cone cs') , (csquare->cone cs) ])
                     (Σ[ h ∈ C [ o' , o ] ] (h ⋆ π₁ == π₁' × h ⋆ π₂ == π₂'))
            eq .Iso.fun cm =
              ConeMor.f cm ,
              sym (ConeMor.component cm nodeA) ,
              sym (ConeMor.component cm nodeB)
            eq .Iso.inv (h , p₁ , p₂) = record { f = h ; component = component }
              where
              component : _
              component nodeA = sym p₁
              component nodeB = sym p₂
              component nodeC = ⋆-left (sym p₁) >=> ⋆-assoc
            eq .Iso.rightInv _ = refl
            eq .Iso.leftInv _ = cone-mor-path D refl


        same-pred : Iso (isTerminal (ConeC D) (csquare->cone cs))
                        (isPullbackSquare cs)
        same-pred .Iso.fun term cs'@(o' , π₁' , π₂' , _) =
          iso-isContr (eq cs') (term (csquare->cone cs'))
        same-pred .Iso.inv isPull c' =
          iso-isContr eq' (isPull (cone->csquare c'))
          where
          eq' : Iso _ (ConeC D [ c' , (csquare->cone cs) ])
          eq' = (iso⁻¹ (eq (cone->csquare c'))) >iso>
                pathToIso (\i -> ConeC D [ Iso.leftInv cone<->csquare c' i , (csquare->cone cs) ])

        same-pred .Iso.leftInv _ = isProp-isTerminal (ConeC D) _ _
        same-pred .Iso.rightInv _ = isProp-isPullbackSquare cs _ _

      ΣisTerminal<->PullbackSquare :
        Iso (Σ (Cone D) (isTerminal (ConeC D)))
            (Σ CSquare isPullbackSquare)
      ΣisTerminal<->PullbackSquare =
        reindexΣ-iso (isoToEquiv (iso⁻¹ cone<->csquare)) (isTerminal (ConeC D)) >iso>
        existential-iso same-pred

      PullbackSquare<->Pullback : Iso (Σ CSquare isPullbackSquare) (Pullback C f g)
      PullbackSquare<->Pullback .Iso.fun ((o , π₁ , π₂ , comm) , p) = record
        { obj = o
        ; π₁ = π₁
        ; π₂ = π₂
        ; is-pullback = comm , \ σ₁ σ₂ σ-comm -> p (_ , σ₁ , σ₂ , σ-comm)
        }
      PullbackSquare<->Pullback .Iso.inv p =
        (Pullback.obj p , Pullback.π₁ p , Pullback.π₂ p , Pullback.commutes p) ,
        \(o' , σ₁ , σ₂ , comm) -> Pullback.universal p σ₁ σ₂ comm
      PullbackSquare<->Pullback .Iso.leftInv _ = refl
      PullbackSquare<->Pullback .Iso.rightInv _ = refl


    Limit<->Pullback : Iso (Limit PullbackDiagram) (Pullback C f g)
    Limit<->Pullback =
      (iso⁻¹ (ΣisTerminal<->Terminal (ConeC D))) >iso>
      (ΣisTerminal<->PullbackSquare >iso>
       PullbackSquare<->Pullback)
