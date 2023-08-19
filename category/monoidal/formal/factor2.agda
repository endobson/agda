{-# OPTIONS --cubical --safe --exact-split -WnoUnsupportedIndexedMatch #-}

module category.monoidal.formal.factor2 where

open import category.monoidal.formal.base
open import category.monoidal.formal.factor
open import category.monoidal.formal.directed
open import category.monoidal.formal.clean
open import category.monoidal.formal.clean-mor
open import category.monoidal.base
open import category.base
open import base
open import sum
open import equality-path


clean-mid-point⁺ : {a b : WObj} -> (fp : FactorizedPath a b) -> isRTree b -> Clean a (fst fp)
clean-mid-point⁺ {a} {b} (c , cp , dp) rt-b = transport (\i -> Clean a (d=c i)) (snd Σd)
  where
  εF-b : isεFree b
  εF-b = isRTree->isεFree b rt-b

  εF-c : isεFree c
  εF-c = dirpath-reflects-isεFree dp εF-b

  Σd : Σ WObj (Clean a)
  Σd = Σclean a
  d = fst Σd

  C-cd : Clean c d
  C-cd = clean-path-preserves-Clean cp (snd Σd)


  d=c : d == c
  d=c = sym (Clean-isεFree->path C-cd εF-c)

clean-mid-point⁰ : {a b : WObj} -> (fp : FactorizedPath a b) -> isε b -> Clean a (fst fp)
clean-mid-point⁰ {a} {b} (c , cp , dp) ib = handle c ic (snd Σd) C-cd
  where
  ic : isε c
  ic = dirpath-reflects-isε dp ib

  Σd : Σ WObj (Clean a)
  Σd = Σclean a
  d = fst Σd

  C-cd : Clean c d
  C-cd = clean-path-preserves-Clean cp (snd Σd)

  handle : {a d : WObj} (c : WObj) -> isε c -> Clean a d -> Clean c d -> Clean a c
  handle ε _ c-ad (clean-zero oε) = c-ad

clean-mid-point : {a b : WObj} -> (fp : FactorizedPath a b) -> isCanon b -> Clean a (fst fp)
clean-mid-point fp cb = either (clean-mid-point⁰ fp) (clean-mid-point⁺ fp) (split-isCanon _ cb)

module InMonoidalFactor2 {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} (MC : MonoidalStr C)
         (obj : Obj C) where
  open CategoryHelpers C
  open MonoidalStrHelpers MC renaming (⊗ to ⊗F)
  open InMonoidal MC obj
  open InMonoidalDir MC obj
  open InMonoidalClean MC obj
  open InMonoidalFactor MC obj

  parallel-factorized-paths-to-canon-εF :
    ∀ {a b} -> (fp1 fp2 : FactorizedPath a b) ->
      isεFree b -> isCanon b ->
      factorized-path->mor fp1 == factorized-path->mor fp2
  parallel-factorized-paths-to-canon-εF {a} {b}
    fp1@(c1 , cp1 , dp1) fp2@(c2 , cp2 , dp2) εF-b canon-b =
    (\i -> cp1=cp2 i ⋆ dp1=dp2 i)
    where
    C-a-c1 : Clean a c1
    C-a-c1 = clean-mid-point fp1 canon-b
    C-a-c2 : Clean a c2
    C-a-c2 = clean-mid-point fp2 canon-b

    c1=c2 : c1 == c2
    c1=c2 i = fst (isProp-ΣClean a (c1 , C-a-c1) (c2 , C-a-c2) i)

    εF-c2 : isεFree c2
    εF-c2 = dirpath-reflects-isεFree dp2 εF-b

    dp1=dp2' : directed-path->mor (transport (\i -> DirectedPath (c1=c2 i) b) dp1) ==
               directed-path->mor dp2
    dp1=dp2' = parallel-dirpaths-to-canon
                 c2 b εF-c2 canon-b (transport (\i -> DirectedPath (c1=c2 i) b) dp1) dp2

    dp1=dp2 : PathP (\i -> C [ inj₀ (c1=c2 i) , inj₀ b ])
               (directed-path->mor dp1)
               (directed-path->mor dp2)
    dp1=dp2 =
      transP-left (\i -> directed-path->mor (transport-filler
                           (\i -> DirectedPath (c1=c2 i) b) dp1 i))
                  dp1=dp2'

    cp1=cp2' : clean-path->mor (transport (\i -> CleanPath a (c1=c2 i)) cp1) ==
               clean-path->mor cp2
    cp1=cp2' = parallel-clean-paths-to-clean a c2 C-a-c2
                 (transport (\i -> CleanPath a (c1=c2 i)) cp1) cp2


    cp1=cp2 : PathP (\i -> C [ inj₀ a , inj₀ (c1=c2 i) ])
               (clean-path->mor cp1)
               (clean-path->mor cp2)
    cp1=cp2 =
      transP-left (\i -> clean-path->mor (transport-filler
                           (\i -> CleanPath a (c1=c2 i)) cp1 i))
                  cp1=cp2'

  ¬dirmor-from-ε : {a : WObj} -> ¬ (DirectedMor ε a)
  ¬dirmor-from-ε (λ⇐' _ , bot) = bot
  ¬dirmor-from-ε (ρ⇐' _ , bot) = bot

  parallel-directed-paths-from-ε :
    ∀ {b} -> (dp1 dp2 : DirectedPath ε b) ->
      directed-path->mor dp1 == directed-path->mor dp2
  parallel-directed-paths-from-ε {b} (m :: _ , dm , _) _ =
    bot-elim (¬dirmor-from-ε (m , dm))
  parallel-directed-paths-from-ε (empty p1 , _) (m :: _ , dm , _) =
    bot-elim (¬dirmor-from-ε (m , dm))
  parallel-directed-paths-from-ε (empty p1 , _) (empty p2 , _) =
    (\i -> directed-path->mor (empty (isSet-WObj _ _ p1 p2 i) , tt))

  parallel-factorized-paths-to-canon-ε :
    ∀ {a b} -> (fp1 fp2 : FactorizedPath a b) ->
      isε b -> isCanon b ->
      factorized-path->mor fp1 == factorized-path->mor fp2
  parallel-factorized-paths-to-canon-ε
    {a} {b} fp1@(c1 , cp1 , dp1) fp2@(c2 , cp2 , dp2) isε-b canon-b =
    (\i -> cp1=cp2 i ⋆ dp1=dp2 i)
    where
    C-a-c1 : Clean a c1
    C-a-c1 = clean-mid-point fp1 canon-b
    C-a-c2 : Clean a c2
    C-a-c2 = clean-mid-point fp2 canon-b

    isε-c1 : isε c1
    isε-c1 = dirpath-reflects-isε dp1 isε-b
    C-a-ε : Clean a ε
    C-a-ε = handle c1 isε-c1 C-a-c1
      where
      handle : (c1 : WObj) -> isε c1 -> Clean a c1 -> Clean a ε
      handle ε _ Clean-a-ε = Clean-a-ε

    c1=ε : c1 == ε
    c1=ε i = fst (isProp-ΣClean a (c1 , C-a-c1) (ε , C-a-ε) i)
    c2=ε : c2 == ε
    c2=ε i = fst (isProp-ΣClean a (c2 , C-a-c2) (ε , C-a-ε) i)
    c1=c2 : c1 == c2
    c1=c2 = c1=ε >=> sym c2=ε

    cp1=cp2' : clean-path->mor (transport (\i -> CleanPath a (c1=c2 i)) cp1) ==
               clean-path->mor cp2
    cp1=cp2' = parallel-clean-paths-to-clean a c2 C-a-c2
                 (transport (\i -> CleanPath a (c1=c2 i)) cp1) cp2


    cp1=cp2 : PathP (\i -> C [ inj₀ a , inj₀ (c1=c2 i) ])
               (clean-path->mor cp1)
               (clean-path->mor cp2)
    cp1=cp2 =
      transP-left (\i -> clean-path->mor (transport-filler
                           (\i -> CleanPath a (c1=c2 i)) cp1 i))
                  cp1=cp2'

    tdp1 : DirectedPath ε b
    tdp1 = transport (\i -> DirectedPath (c1=ε i) b) dp1
    tdp2 : DirectedPath ε b
    tdp2 = transport (\i -> DirectedPath (c2=ε i) b) dp2

    tdp1=tdp2 : directed-path->mor tdp1 == directed-path->mor tdp2
    tdp1=tdp2 = parallel-directed-paths-from-ε tdp1 tdp2

    dp1=tdp1 : PathP (\i -> C [ inj₀ (c1=ε i) , inj₀ b ])
                (directed-path->mor dp1)
                (directed-path->mor tdp1)
    dp1=tdp1 j = directed-path->mor (transport-filler (\i -> DirectedPath (c1=ε i) b) dp1 j)
    dp2=tdp2 : PathP (\i -> C [ inj₀ (c2=ε i) , inj₀ b ])
                (directed-path->mor dp2)
                (directed-path->mor tdp2)
    dp2=tdp2 j = directed-path->mor (transport-filler (\i -> DirectedPath (c2=ε i) b) dp2 j)

    dp1=dp2 : PathP (\i -> C [ inj₀ (c1=c2 i) , inj₀ b ])
               (directed-path->mor dp1)
               (directed-path->mor dp2)
    dp1=dp2 =
      transport (\k -> PathP (\i -> index-path k i) (directed-path->mor dp1) (directed-path->mor dp2))
                (transP dp1=tdp1 (transP-right tdp1=tdp2 (symP dp2=tdp2)))
      where
      index-path : ((\j -> (C [ inj₀ (c1=ε j) , inj₀ b ])) >=>
                    (\j -> (C [ inj₀ (c2=ε (~ j)) , inj₀ b ]))) ==
                   (\j -> (C [ inj₀ (c1=c2 j) , inj₀ b ]))
      index-path = cong-trans (\a -> (C [ inj₀ a , inj₀ b ])) c1=ε (sym c2=ε)


  parallel-factorized-paths-to-canon :
    ∀ {a b} -> (fp1 fp2 : FactorizedPath a b) ->
      isCanon b ->
      factorized-path->mor fp1 == factorized-path->mor fp2
  parallel-factorized-paths-to-canon fp1 fp2 canon-b =
    either
      (\isε-b -> parallel-factorized-paths-to-canon-ε fp1 fp2 isε-b canon-b)
      (\rt-b -> parallel-factorized-paths-to-canon-εF fp1 fp2 (isRTree->isεFree _ rt-b) canon-b)
      (split-isCanon _ canon-b)

  parallel-forward-paths-to-canon :
    ∀ {a b} -> (fp1 fp2 : ForwardPath a b) -> isCanon b ->
      forward-path->mor fp1 == forward-path->mor fp2
  parallel-forward-paths-to-canon fp1 fp2 cb =
    let (fp1 , q1) = factorize fp1 in
    let (fp2 , q2) = factorize fp2 in
    q1 >=> parallel-factorized-paths-to-canon fp1 fp2 cb >=> sym q2
