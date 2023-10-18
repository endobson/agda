{-# OPTIONS --cubical --safe --exact-split #-}

module category.object.group where

open import base
open import category.base
open import category.monoidal.base
open import category.monoidal.cartesian
open import category.natural-transformation
open import category.object.monoid
open import category.object.product
open import category.object.terminal
open import cubical
open import equality
open import hlevel

module _ {ℓO ℓM} {C : PreCategory ℓO ℓM}
         {M : MonoidalStr C} (Cart : isCartesian M) where
  open MonoidalStrHelpers M
  open CategoryHelpers C
  open CartesianHelpers Cart

  module isUnital-CartesianHelpers
    {g : Obj C} {op : C [ g ⊗₀ g , g ]} (isUnital-op : isUnital M g op) where
    open isUnital isUnital-op

    ε' : {x : Obj C} -> C [ x , g ]
    ε' = ! ⋆ ε

    opaque
      ε'-left-reduce' : ∀ {x : Obj C} -> Path (C [ x ⊗₀ g , g ]) ((ε' ⊗₁ id C) ⋆ op) π₂
      ε'-left-reduce' = ⋆-left split₁ˡ >=> ⋆-assoc >=> ⋆-right ε-left-reduce'

      ε'-right-reduce' : ∀ {x : Obj C} -> Path (C [ g ⊗₀ x , g ]) ((id C ⊗₁ ε') ⋆ op) π₁
      ε'-right-reduce' = ⋆-left split₂ˡ >=> ⋆-assoc >=> ⋆-right ε-right-reduce'

      ε'-left-reduce : ∀ {x y : Obj C} {f : C [ y , g ]} ->
        Path (C [ x ⊗₀ y , g ]) ((ε' ⊗₁ f) ⋆ op) (π₂ ⋆ f)
      ε'-left-reduce {f = f} =
        ⋆-left (⊗₁-right (sym ⋆-right-id) >=> split₂ʳ) >=>
        ⋆-assoc >=>
        ⋆-right ε'-left-reduce' >=>
        sym π₂-swap

      ε'-right-reduce : ∀ {x y : Obj C} {f : C [ x , g ]} ->
        Path (C [ x ⊗₀ y , g ]) ((f ⊗₁ ε') ⋆ op) (π₁ ⋆ f)
      ε'-right-reduce {f = f} =
        ⋆-left (⊗₁-left (sym ⋆-right-id) >=> split₁ʳ) >=>
        ⋆-assoc >=>
        ⋆-right ε'-right-reduce' >=>
        sym π₁-swap


  module _ {g : Obj C} {op : C [ g ⊗₀ g , g ]} (isUnital-op : isUnital M g op) where
    open isUnital-CartesianHelpers isUnital-op

    record hasInverse : Type ℓM where
      field
        inv : C [ g , g ]

        inv-left : (Δ ⋆ (inv ⊗₁ id C)) ⋆ op == ε'
        inv-right : (Δ ⋆ (id C ⊗₁ inv)) ⋆ op == ε'


    module _ (op-assoc : isAssociative M g op) where
      isProp-hasInverse : isProp hasInverse
      isProp-hasInverse
        s₁@(record { inv = inv₁ ; inv-left = inv₁-left ; inv-right = inv₁-right })
        s₂@(record { inv = inv₂ ; inv-left = inv₂-left ; inv-right = inv₂-right }) =
        \i -> record
          { inv = inv-path i
          ; inv-left = isProp->PathPᵉ (\i -> isSet-Mor C (l-path i) ε') inv₁-left inv₂-left i
          ; inv-right = isProp->PathPᵉ (\i -> isSet-Mor C (r-path i) ε') inv₁-right inv₂-right i
          }
        where

        ε-left-id : ∀ {x : Obj C} {f : C [ x , g ]} -> (Δ ⋆ (ε' ⊗₁ f)) ⋆ op == f
        ε-left-id {f = f} =
          ⋆-assoc >=>
          ⋆-right ε'-left-reduce >=>
          sym ⋆-assoc >=>
          ⋆-left Δπ₂-reduce >=>
          ⋆-left-id

        ε-right-id : ∀ {x : Obj C} {f : C [ x , g ]} -> (Δ ⋆ (f ⊗₁ ε')) ⋆ op == f
        ε-right-id {f = f} =
          ⋆-assoc >=>
          ⋆-right ε'-right-reduce >=>
          sym ⋆-assoc >=>
          ⋆-left Δπ₁-reduce >=>
          ⋆-left-id


        lemma1 : Δ ⋆ ( inv₁ ⊗₁ (Δ ⋆ (id C ⊗₁ inv₂) ⋆ op)) ⋆ op == inv₁
        lemma1 = (\i -> (Δ ⋆ (inv₁ ⊗₁ inv₂-right i) ⋆ op)) >=> ε-right-id

        lemma2 : Δ ⋆ ((Δ ⋆ (inv₁ ⊗₁ id C) ⋆ op) ⊗₁ inv₂) ⋆ op == inv₂
        lemma2 = (\i -> (Δ ⋆ (inv₁-left i ⊗₁ inv₂) ⋆ op)) >=> ε-left-id


        lemma3 : Δ ⋆ ( inv₁ ⊗₁ (Δ ⋆ (id C ⊗₁ inv₂) ⋆ op)) ⋆ op ==
                 Δ ⋆ ((Δ ⋆ (inv₁ ⊗₁ id C) ⋆ op) ⊗₁ inv₂) ⋆ op
        lemma3 =
          ⋆-left (⋆-right (⊗₁-right ⋆-assoc >=> split₂ʳ) >=>
                  sym ⋆-assoc >=>
                  ⋆-left (sym ΔΔ-assoc) >=>
                  ⋆-assoc) >=>
          ⋆-assoc >=> ⋆-right lemma3a >=> sym ⋆-assoc >=>
          sym (⋆-left (⋆-right (⊗₁-left ⋆-assoc >=> split₁ʳ) >=>
                       sym ⋆-assoc))
          where
          lemma3a : α⇒ ⋆ (inv₁ ⊗₁ ((id C ⊗₁ inv₂) ⋆ op)) ⋆ op ==
                    (((inv₁ ⊗₁ id C) ⋆ op) ⊗₁ inv₂) ⋆ op
          lemma3a =
            ⋆-left (⋆-right split₂ˡ >=> sym ⋆-assoc >=> ⋆-left α⇒-swap) >=>
            ⋆-assoc >=> ⋆-assoc >=>
            ⋆-right (sym ⋆-assoc >=> op-assoc) >=>
            sym ⋆-assoc >=>
            ⋆-left (sym split₁ˡ)

        inv-path : inv₁ == inv₂
        inv-path = sym lemma1 >=> lemma3 >=> lemma2

        l-path : inv₁-left i0 == inv₂-left i0
        l-path i = Δ ⋆ (inv-path i ⊗₁ id C) ⋆ op
        r-path : inv₁-right i0 == inv₂-right i0
        r-path i = Δ ⋆ (id C ⊗₁ inv-path i) ⋆ op

  record isGroupObject (g : Obj C) (op : C [ (g ⊗₀ g) , g ]) : Type ℓM where
    field
      isAssoc-op : isAssociative M g op
      isUnital-op : isUnital M g op
      hasInverse-op : hasInverse isUnital-op

    open isUnital-CartesianHelpers isUnital-op public
    open hasInverse hasInverse-op public

  opaque
    isProp-isGroupObject : {g : Obj C} {op : C [ (g ⊗₀ g) , g ]} -> isProp (isGroupObject g op)
    isProp-isGroupObject {g} {op}
      (record { isAssoc-op = a1 ; isUnital-op = u1 ; hasInverse-op = inv1 })
      (record { isAssoc-op = a2 ; isUnital-op = u2 ; hasInverse-op = inv2 }) =
      \i -> record
        { isAssoc-op = ap i
        ; isUnital-op = up i
        ; hasInverse-op = invp i
        }
      where
      ap : a1 == a2
      ap = isProp-isAssociative M a1 a2
      up : u1 == u2
      up = isProp-isUnital u1 u2
      invp : PathP (\i -> hasInverse (up i)) inv1 inv2
      invp = isProp->PathP (\i -> isProp-hasInverse (up i) (ap i))

  GroupObject : Type (ℓ-max ℓO ℓM)
  GroupObject = Σ[ g ∈ Obj C ] Σ[ op ∈ C [ (g ⊗₀ g) , g ] ] (isGroupObject g op)

module _ {ℓO ℓM} {C : PreCategory ℓO ℓM}
         {M : MonoidalStr C} {Cart : isCartesian M} where
  open MonoidalStrHelpers M
  open CategoryHelpers C
  open CartesianHelpers Cart

  module _ ((g1 , op1 , isGroup1) (g2 , op2 , isGroup2) : GroupObject Cart) where
    record GroupHomomorphism : Type ℓM where
      field
        mor : C [ g1 , g2 ]
        commutes : op1 ⋆ mor == (mor ⊗₁ mor) ⋆ op2

  module _ {G1@(g1 , op1 , isGroup1) G2@(g2 , op2 , isGroup2) : GroupObject Cart} where
    group-homomorphism-path : {h1 h2 : GroupHomomorphism G1 G2} ->
                              (GroupHomomorphism.mor h1) == (GroupHomomorphism.mor h2) ->
                              h1 == h2
    group-homomorphism-path {h1} {h2} mp i = record
      { mor = mp i
      ; commutes = commutes i
      }
      where
      opaque
        commutes : PathP (\i -> (op1 ⋆ mp i) == ((mp i ⊗₁ mp i) ⋆ op2))
                         (GroupHomomorphism.commutes h1) (GroupHomomorphism.commutes h2)
        commutes = isProp->PathP (\i -> isSet-Mor C _ _)

    opaque
      isSet-GroupHomomorphism : isSet (GroupHomomorphism G1 G2)
      isSet-GroupHomomorphism =
        isSet-Retract f g (\_ -> refl) (isSetΣ (isSet-Mor C) (\_ -> isProp->isSet (isSet-Mor C _ _)))
        where
        f : GroupHomomorphism G1 G2 -> Σ[ m ∈ C [ g1 , g2 ] ] (op1 ⋆ m == (m ⊗₁ m) ⋆ op2)
        f (record { mor = mor ; commutes = commutes }) = mor , commutes
        g : Σ[ m ∈ C [ g1 , g2 ] ] (op1 ⋆ m == (m ⊗₁ m) ⋆ op2) -> GroupHomomorphism G1 G2
        g (mor , commutes) = record { mor = mor ; commutes = commutes }
