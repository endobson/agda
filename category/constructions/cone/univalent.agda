{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.cone.univalent where

open import base
open import category.base
open import category.functor
open import category.univalent
open import equality-path renaming (J to eqJ)
open import equivalence
open import hlevel
open import isomorphism

module _ {ℓOJ ℓMJ ℓOC ℓMC}
         {J : PreCategory ℓOJ ℓMJ} {C : PreCategory ℓOC ℓMC}
         (D : Diagram J C)
         (univ : isUnivalent C) where

  open import category.constructions.cone D

  private
    reduce-iso : {c1 c2 : Obj ConeC} -> CatIso ConeC c1 c2 -> CatIso C (fst c1) (fst c2)
    reduce-iso ciso .CatIso.mor = ConeMor.f (CatIso.mor ciso)
    reduce-iso ciso .CatIso.inv = ConeMor.f (CatIso.inv ciso)
    reduce-iso ciso .CatIso.sec = cong ConeMor.f (CatIso.sec ciso)
    reduce-iso ciso .CatIso.ret = cong ConeMor.f (CatIso.ret ciso)

    module inner where
      abstract
        catIsoToPath : (c1 c2 : Obj ConeC) -> CatIso ConeC c1 c2 -> c1 == c2
        catIsoToPath c1 c2 ciso = cone-path op cps
          where
          module _ where
            module s1 = ConeStr (snd c1)
            module s2 = ConeStr (snd c2)
            module ciso = CatIso ciso
            o1 : Obj C
            o1 = fst c1
            o2 : Obj C
            o2 = fst c2

            ciso2 : CatIso C o1 o2
            ciso2 = reduce-iso ciso

            module ciso2 = CatIso ciso2

            op : o1 == o2
            op = isEqInv (isUnivalent.isEquiv-pathToCatIso univ _ _) ciso2

            check-op : pathToCatIso C _ _ op == ciso2
            check-op = isEqSec (isUnivalent.isEquiv-pathToCatIso univ _ _) ciso2

            check-ptoi : PathP (\i -> C [ op i , o2 ]) (CatIso.mor (pathToCatIso C _ _ op)) (id C)
            check-ptoi =
              eqJ (\ o1' o2=o1' -> PathP (\i -> C [ o2=o1' (~ i) , o2 ])
                                         (CatIso.mor (pathToCatIso C _ _ (sym o2=o1'))) (id C))
                  refl-case
                  (sym op)
              where
              refl-case : (CatIso.mor (pathToCatIso C _ _ refl)) == (id C)
              refl-case = cong CatIso.mor (pathToCatIso-refl C o2)

            mor-path1 : (CatIso.mor (pathToCatIso C _ _ op)) == ciso2.mor
            mor-path1 = cong CatIso.mor check-op

            mor-path2 : PathP (\i -> C [ op i , o2 ]) ciso2.mor (id C)
            mor-path2 = transP-right (sym mor-path1) check-ptoi

            module _ (j : Obj J) where
              mor-path3 : PathP (\i -> C [ op i , F-obj D j ])
                                (ciso2.mor ⋆⟨ C ⟩ s2.component j)
                                (id C ⋆⟨ C ⟩ s2.component j)
              mor-path3 i = mor-path2 i ⋆⟨ C ⟩ s2.component j

              cps : PathP (\i -> C [ op i , F-obj D j ]) (s1.component j) (s2.component j)
              cps = transP-mid (ConeMor.component ciso.mor j)
                               mor-path3
                               (PreCategory.⋆-left-id C _)

        catIsoToPath-inv1 : (c1 c2 : Obj ConeC) -> (p : c1 == c2) ->
                            catIsoToPath c1 c2 (pathToCatIso ConeC _ _ p) == p
        catIsoToPath-inv1 c1 c2 p = cone-path-path _ _ ans
          where
          refl-case : (reduce-iso (pathToCatIso ConeC c1 c1 refl)) ==
                      (pathToCatIso C (fst c1) (fst c1) refl)
          refl-case =
            cong reduce-iso (pathToCatIso-refl ConeC c1) >=>
            sym (pathToCatIso-refl C (fst c1))

          ans2 : (reduce-iso (pathToCatIso ConeC _ _ p)) == (pathToCatIso C _ _ (cong fst p))
          ans2 =
            eqJ (\ c2' p' -> (reduce-iso (pathToCatIso ConeC _ _ p')) ==
                             (pathToCatIso C _ _ (cong fst p')))
                refl-case
                p

          ans : isEqInv (isUnivalent.isEquiv-pathToCatIso univ _ _)
                        (reduce-iso (pathToCatIso ConeC _ _ p)) ==
                (cong fst p)
          ans =
            cong (isEqInv (isUnivalent.isEquiv-pathToCatIso univ _ _)) ans2 >=>
            isEqRet (isUnivalent.isEquiv-pathToCatIso univ _ _) (cong fst p)

        cone-mor-path : {c1 c2 : Obj ConeC} -> {f g : ConeC [ c1 , c2 ]} ->
                        ConeMor.f f == ConeMor.f g ->
                        f == g
        cone-mor-path p i .ConeMor.f = p i
        cone-mor-path {c1} {c2} {f} {g} p i .ConeMor.component j =
          isProp->PathPᵉ (\i -> isSet-Mor C (ConeStr.component (snd c1) j)
                                            (p i ⋆⟨ C ⟩ (ConeStr.component (snd c2) j)))
            (ConeMor.component f j) (ConeMor.component g j) i

        catIsoToPath-inv2 : (c1 c2 : Obj ConeC) -> (ciso : CatIso ConeC c1 c2) ->
                            pathToCatIso ConeC _ _ (catIsoToPath c1 c2 ciso) == ciso
        catIsoToPath-inv2 c1 c2 ciso =
          cat-iso-path (cone-mor-path (ans2 (catIsoToPath c1 c2 ciso) >=> ans3))
          where
          refl-case : ConeMor.f (CatIso.mor (pathToCatIso ConeC c1 c1 refl)) ==
                      CatIso.mor (pathToCatIso C (fst c1) (fst c1) refl)
          refl-case =
            cong (\i -> ConeMor.f (CatIso.mor i)) (pathToCatIso-refl ConeC c1) >=>
            sym (cong CatIso.mor (pathToCatIso-refl C (fst c1)))

          ans2 : ∀ {c2'} p -> ConeMor.f (CatIso.mor (pathToCatIso ConeC c1 c2' p)) ==
                              CatIso.mor (pathToCatIso C (fst c1) (fst c2') (cong fst p))
          ans2 = eqJ (\ c2' p -> ConeMor.f (CatIso.mor (pathToCatIso ConeC c1 c2' p)) ==
                                 CatIso.mor (pathToCatIso C (fst c1) (fst c2') (cong fst p)))
                     refl-case

          ans3 : CatIso.mor (pathToCatIso C (fst c1) (fst c2) (cong fst (catIsoToPath c1 c2 ciso))) ==
                 ConeMor.f (CatIso.mor ciso)
          ans3 = cong CatIso.mor (isEqSec (isUnivalent.isEquiv-pathToCatIso univ _ _) _)

  abstract
    isUnivalent-ConeC : isUnivalent ConeC
    isUnivalent-ConeC .isUnivalent.isEquiv-pathToCatIso x y =
      isoToIsEquiv record
        { fun = pathToCatIso ConeC x y
        ; inv = inner.catIsoToPath x y
        ; leftInv = inner.catIsoToPath-inv1 x y
        ; rightInv = inner.catIsoToPath-inv2 x y
        }
