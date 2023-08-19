{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.factor where

open import category.monoidal.formal.base
open import category.monoidal.base
open import category.monoidal.semicartesian
open import category.base
open import category.functor
open import category.monoidal.formal.directed
open import category.monoidal.formal.clean-mor
open import base
open import cubical
open import equality-path
open import relation
open import sum


isForwardMor : {a b : WObj} -> Pred (BasicMor a b) ℓ-zero
isForwardMor (α⇒' a b c) = Top
isForwardMor (λ⇒' _) = Top
isForwardMor (ρ⇒' _) = Top
isForwardMor (m ⊗ˡ' w) = isForwardMor m
isForwardMor (w ⊗ʳ' m) = isForwardMor m
isForwardMor (α⇐' _ _ _) = Bot
isForwardMor (λ⇐' _) = Bot
isForwardMor (ρ⇐' _) = Bot

ForwardMor : WObj -> WObj -> Type₀
ForwardMor a b = Σ (BasicMor a b) isForwardMor

isForwardPath : {a b : WObj} -> Pred (BasicPath a b) ℓ-zero
isForwardPath (empty p) = Top
isForwardPath (m :: p) = isForwardMor m × isForwardPath p

ForwardPath : WObj -> WObj -> Type₀
ForwardPath a b = Σ (BasicPath a b) isForwardPath

FactorizedPath : WObj -> WObj -> Type₀
FactorizedPath a c = Σ[ b ∈ WObj ] (CleanPath a b × DirectedPath b c)

FactorizedStep : WObj -> WObj -> Type₀
FactorizedStep a c = CleanMor a c ⊎ (Σ[ b ∈ WObj ] (CleanMor a b × DirectedMor b c))


split-isForwardMor : {a b : WObj} -> (m : BasicMor a b) -> isForwardMor m ->
                     isDirectedMor m ⊎ isCleanMor m
split-isForwardMor (α⇒' a b c) _ = inj-l tt
split-isForwardMor (λ⇒' _) _ = inj-r tt
split-isForwardMor (ρ⇒' _) _ = inj-r tt
split-isForwardMor (m ⊗ˡ' w) fwd = split-isForwardMor m fwd
split-isForwardMor (w ⊗ʳ' m) fwd = split-isForwardMor m fwd
split-isForwardMor (α⇐' _ _ _) ()
split-isForwardMor (λ⇐' _) ()
split-isForwardMor (ρ⇐' _) ()

cons-forward-mor : {a b c : WObj} -> ForwardMor a b -> ForwardPath b c -> ForwardPath a c
cons-forward-mor (m , fm) (p , fp) = m :: p , fm , fp

module InMonoidalFactor {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open MonoidalStrHelpers2 MC
  open InMonoidal MC obj
  open InMonoidalDir MC obj
  open InMonoidalClean MC obj

  forward-path->mor : {a b : WObj} -> ForwardPath a b -> C [ inj₀ a , inj₀ b ]
  forward-path->mor (p , _) = basic-path->mor p

  factorized-path->mor : {a b : WObj} -> FactorizedPath a b -> C [ inj₀ a , inj₀ b ]
  factorized-path->mor (_ , cp , dp) =
    clean-path->mor cp ⋆ directed-path->mor dp

  factorized-step->mor : {a b : WObj} -> FactorizedStep a b -> C [ inj₀ a , inj₀ b ]
  factorized-step->mor (inj-l cm) = clean-mor->mor cm
  factorized-step->mor (inj-r (_ , cm , dm)) =
    clean-mor->mor cm ⋆ dm->mor dm

  fs-lift-⊗ˡ : {a b : WObj} -> FactorizedStep a b -> (c : WObj) ->
               FactorizedStep (a ⊗ c) (b ⊗ c)
  fs-lift-⊗ˡ (inj-l cm) c = inj-l (cm-lift-⊗ˡ cm c)
  fs-lift-⊗ˡ (inj-r (o , cm , dm)) c =
    inj-r (o ⊗ c , (cm-lift-⊗ˡ cm c) , (dirmor-lift-⊗ˡ dm c))

  fs-lift-⊗ʳ : (a : WObj) {b c : WObj} -> FactorizedStep b c ->
               FactorizedStep (a ⊗ b) (a ⊗ c)
  fs-lift-⊗ʳ a (inj-l cm) = inj-l (cm-lift-⊗ʳ a cm)
  fs-lift-⊗ʳ a (inj-r (o , cm , dm)) =
    inj-r (a ⊗ o , (cm-lift-⊗ʳ a cm) , (dirmor-lift-⊗ʳ a dm))

  fs-lift-⊗ˡ-path : {a b : WObj} -> (fs : FactorizedStep a b) -> (c : WObj) ->
                    factorized-step->mor (fs-lift-⊗ˡ fs c) ==
                    factorized-step->mor fs ⊗₁ (id C)
  fs-lift-⊗ˡ-path (inj-l cm) c = refl
  fs-lift-⊗ˡ-path (inj-r (o , cm , dm)) c = sym split₁ˡ
  fs-lift-⊗ʳ-path : (a : WObj) {b c : WObj} -> (fs : FactorizedStep b c) ->
                    factorized-step->mor (fs-lift-⊗ʳ a fs) ==
                    (id C) ⊗₁ factorized-step->mor fs
  fs-lift-⊗ʳ-path a (inj-l cm) = refl
  fs-lift-⊗ʳ-path a (inj-r (o , cm , dm)) = sym split₂ˡ


  factor-mor-mor :
    {a b c : WObj} (dm : DirectedMor a b) (cm : CleanMor b c) ->
    Σ[ fp ∈ FactorizedStep a c ]
      (dm->mor dm ⋆ clean-mor->mor cm) ==
      (factorized-step->mor fp)
  factor-mor-mor (m1 ⊗ˡ' o2 , dm1) (λ⇒' o2 , _) =
    bot-elim (dirmor->is⊗₂ (m1 , dm1))
  factor-mor-mor (m1 ⊗ˡ' o2 , dm1) (ρ⇒' o1 , _) =
    inj-r (_ , (ρ⇒' _ , tt) , (m1 , dm1)) , sym ρ⇒-swap
  factor-mor-mor (m1 ⊗ˡ' o2 , dm1) (m2 ⊗ˡ' o2 , cm2) =
    let (fs , p) = (factor-mor-mor (m1 , dm1) (m2 , cm2)) in
    fs-lift-⊗ˡ fs o2 , sym split₁ˡ >=> ⊗₁-left p >=> sym (fs-lift-⊗ˡ-path fs o2)
  factor-mor-mor (m1 ⊗ˡ' o2 , dm1) (o1 ⊗ʳ' m2 , cm2) =
    inj-r (_ , (_ ⊗ʳ' m2 , cm2) , (m1 ⊗ˡ' _ , dm1)) ,
    sym serialize₁₂ >=> serialize₂₁
  factor-mor-mor (o1 ⊗ʳ' m1 , dm1) (ρ⇒' o1 , _) =
    bot-elim (dirmor->is⊗₂ (m1 , dm1))
  factor-mor-mor (o1 ⊗ʳ' m1 , dm1) (m2 ⊗ˡ' o2 , cm2) =
    inj-r (_ , (m2 ⊗ˡ' _ , cm2) ,  (_ ⊗ʳ' m1 , dm1)) ,
    sym serialize₂₁ >=> serialize₁₂
  factor-mor-mor (o1 ⊗ʳ' m1 , dm1) (o1 ⊗ʳ' m2 , cm2) =
    let (fs , p) = (factor-mor-mor (m1 , dm1) (m2 , cm2)) in
    fs-lift-⊗ʳ o1 fs , sym split₂ˡ >=> ⊗₁-right p >=> sym (fs-lift-⊗ʳ-path o1 fs)
  factor-mor-mor (ε ⊗ʳ' m1 , dm1) (λ⇒' o2 , _) =
    inj-r (_ , (λ⇒' _ , tt) , (m1 , dm1)) , sym λ⇒-swap
  factor-mor-mor (α⇒' o1 o2 o3 , _) (m2 ⊗ˡ' (o2 ⊗ o3) , cm2) =
    inj-r (_ , ((m2 ⊗ˡ' o2) ⊗ˡ' o3  , cm2) , (α⇒' _ o2 o3 , tt)) ,
    ⋆-right (⊗₁-right (sym (F-id ⊗F _))) >=> α⇒-swap
  factor-mor-mor (α⇒' ε  o2 o3 , _) (λ⇒' (o2 ⊗ o3) , _) =
    inj-l ((λ⇒' o2) ⊗ˡ' o3 , tt) , α⇒λ⇒-reduce
  factor-mor-mor (α⇒' o1 o2 o3 , _) (o1 ⊗ʳ' (m2 ⊗ˡ' o3) , cm2) =
    inj-r (_ , ((o1 ⊗ʳ' m2) ⊗ˡ' o3  , cm2) , (α⇒' o1 _ o3 , tt)) ,
    α⇒-swap
  factor-mor-mor (α⇒' o1 o2 o3 , _) (o1 ⊗ʳ' (o2 ⊗ʳ' m2) , cm2) =
    inj-r (_ , ((o1 ⊗ o2) ⊗ʳ' m2  , cm2) , (α⇒' o1 o2 _ , tt)) ,
    α⇒-swap >=> ⋆-left (⊗₁-left (F-id ⊗F _))
  factor-mor-mor (α⇒' o1 ε o3 , _) (o1 ⊗ʳ' (λ⇒' o3) , _) =
    inj-l ((ρ⇒' o1) ⊗ˡ' o3 , tt) , triangle
  factor-mor-mor (α⇒' o1 o2 ε , _) (o1 ⊗ʳ' (ρ⇒' o2) , _) =
    inj-l (ρ⇒' (o1 ⊗ o2) , tt) , α⇒ρ⇒-reduce



  factor-mor-path :
    {a b c d : WObj} (m : DirectedMor a b) (cp : CleanPath b c) (dp : DirectedPath c d) ->
    Σ[ fp ∈ FactorizedPath a d ]
      (dm->mor m ⋆ (clean-path->mor cp ⋆ directed-path->mor dp)) ==
      (factorized-path->mor fp)
  factor-mor-path m (p , cp) = factor-mor-path' m p cp
    where
    factor-mor-path' :
      {a b c d : WObj} (m : DirectedMor a b) (p : BasicPath b c) (cp : isCleanPath p)
                       (dp : DirectedPath c d) ->
      Σ[ fp ∈ FactorizedPath a d ]
        (dm->mor m ⋆ (basic-path->mor p ⋆ directed-path->mor dp)) ==
        (factorized-path->mor fp)
    factor-mor-path' {a} {b} {c} {d} m (empty p) _ dp =
      (a , (empty refl , tt) , (cons-dirmor tm dp)) , path-path
      where
      tm : DirectedMor a c
      tm = transport (\ i -> DirectedMor a (p i)) m
      path-path : (dm->mor m ⋆ (basic-path->mor (empty p) ⋆ directed-path->mor dp)) ==
                  basic-path->mor (empty (refl {x = a})) ⋆ (dm->mor tm ⋆ directed-path->mor dp)
      path-path =
        ⋆-left (cong dm->mor (sym (transportRefl m))) >=>
        (\ i -> (dm->mor (transport (\j -> DirectedMor a (p (i ∧ j))) m)) ⋆
                (basic-path->mor (empty (\j -> p (i ∨ j))) ⋆ directed-path->mor dp)) >=>
        ⋆-right (⋆-left (transportRefl (id C)) >=> ⋆-left-id) >=>
        sym ⋆-left-id >=>
        ⋆-left (sym (transportRefl (id C)))
    factor-mor-path' {a} {b} {c} {d} dm (_::_ {o1} m p) (cm , cp) dp =
      fst rec2 ,
      ⋆-right ⋆-assoc >=>
      sym ⋆-assoc >=>
      ⋆-left (snd rec1) >=>
      (snd rec2)
      where

      factor-step-path :
        (s : FactorizedStep a o1) ->
        Σ[ fp ∈ FactorizedPath a d ]
          (factorized-step->mor s ⋆ (clean-path->mor (p , cp) ⋆ directed-path->mor dp)) ==
          (factorized-path->mor fp)
      factor-step-path (inj-l cm) =
        (_ , (cm-cons cm (p , cp)) , dp) , sym ⋆-assoc
      factor-step-path (inj-r (_ , cm , dm)) =
        let ((_ , rc , rd) , p) = factor-mor-path' dm p cp dp in
        (_ , (cm-cons cm rc) , rd) , ⋆-assoc >=> ⋆-right p >=> sym ⋆-assoc

      rec1 : Σ[ s ∈ FactorizedStep a o1 ]
               (dm->mor dm ⋆ clean-mor->mor (m , cm)) ==
               (factorized-step->mor s)
      rec1 = factor-mor-mor dm (m , cm)

      rec2 : Σ[ fp ∈ FactorizedPath a d ]
               (factorized-step->mor (fst rec1) ⋆ (clean-path->mor (p , cp) ⋆ directed-path->mor dp)) ==
               (factorized-path->mor fp)
      rec2 = factor-step-path (fst rec1)


  factor-path-path :
    {a b c d : WObj} (p : DirectedPath a b) (cp : CleanPath b c) (dp : DirectedPath c d) ->
    Σ[ fp ∈ FactorizedPath a d ]
      (directed-path->mor p ⋆ (clean-path->mor cp ⋆ directed-path->mor dp)) ==
      (factorized-path->mor fp)
  factor-path-path {a} {b} {c} (empty p , _) cp dp =
    (_ , transport (\i -> CleanPath (p (~ i)) c) cp , dp) ,
    (\i -> (basic-path->mor (empty p) ⋆
             (clean-path->mor (transportRefl cp (~ i)) ⋆ directed-path->mor dp))) >=>
    (\i -> (basic-path->mor (empty (\j -> p ((~ i) ∧ j))) ⋆
             (clean-path->mor (transport (\j -> CleanPath (p ((~ i) ∨ (~ j))) c) cp) ⋆
              directed-path->mor dp))) >=>
    ⋆-left (transportRefl (id C)) >=>
    ⋆-left-id
  factor-path-path {a} {b} {c} (m :: p , idm , idp) cp dp =
    let ((_ , rc , rd) , rp) = factor-path-path (p , idp) cp dp in
    let (rf2 , rp2) = factor-mor-path (m , idm) rc rd in
    (rf2 , ⋆-assoc >=> ⋆-right rp >=> rp2)


  factorize : {a b : WObj} -> (p1 : ForwardPath a b) ->
              Σ[ p2 ∈ FactorizedPath a b ] (forward-path->mor p1 == factorized-path->mor p2)
  factorize (empty p , _) =
    (_ , (empty p , tt) , (empty refl , tt)) ,
    sym ⋆-right-id >=> ⋆-right (sym (transportRefl _))
  factorize {a} {b} (m :: p , fwd-m , fwd-p) =
    handle (split-isForwardMor m fwd-m) (factorize (p , fwd-p))
    where
    handle : (isDirectedMor m ⊎ isCleanMor m) ->
             Σ[ p2 ∈ FactorizedPath _ b ] (basic-path->mor p == factorized-path->mor p2) ->
             Σ[ p2 ∈ FactorizedPath a b ] (basic-path->mor (m :: p) == factorized-path->mor p2)
    handle (inj-l dm) ((_ , rc , rd) , rp) =
      let (rf2 , rp2) = factor-mor-path (m , dm) rc rd in
      (rf2 , ⋆-right rp >=> rp2)
    handle (inj-r cm) ((_ , rc , rd) , rp) =
      (_ , (cm-cons (m , cm) rc) , rd) , ⋆-right rp >=> sym ⋆-assoc
