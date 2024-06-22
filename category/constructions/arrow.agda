{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.arrow where

open import base
open import category.base
open import category.univalent
open import equality-path
open import equality.identity-system
open import hlevel

module _ {ℓO ℓM : Level} (C : PreCategory ℓO ℓM) where
  open CategoryHelpers C

  private
    ArrowSorts : CategorySorts (ℓ-max ℓO ℓM) ℓM
    ArrowSorts = record
      { Obj = Σ[ c1 ∈ Obj C ] Σ[ c2 ∈ Obj C ] (C [ c1 , c2 ])
      ; Mor = \ (c1 , c2 , m12) (c3 , c4 , m34) ->
         Σ[ m13 ∈ C [ c1 , c3 ] ] Σ[ m24 ∈ C [ c2 , c4 ] ] (m13 ⋆⟨ C ⟩ m34 == m12 ⋆⟨ C ⟩ m24)
      }

    ArrowOps : CategoryOps ArrowSorts
    ArrowOps .CategoryOps.id = id C , id C , ⋆-left-id >=> sym ⋆-right-id
    ArrowOps .CategoryOps._⋆_ {(_ , _ , mx)} {(_ , _ , my)} {(_ , _ , mz)} (m1 , m2 , s1) (m3 , m4 , s2) =
      m1 ⋆ m3 , m2 ⋆ m4 , p
      where
      opaque
        p : (m1 ⋆ m3) ⋆ mz == mx ⋆ (m2 ⋆ m4)
        p = ⋆-assoc >=>
            ⋆-right s2 >=>
            sym ⋆-assoc >=>
            ⋆-left s1 >=>
            ⋆-assoc

    module S = CategorySorts ArrowSorts
    module O = CategoryOps ArrowOps

    opaque
      mor-path : {o1 o2 : S.Obj} {m1 m2 : S.Mor o1 o2} ->
                 (fst m1) == (fst m2) ->
                 (fst (snd m1)) == (fst (snd m2)) ->
                 m1 == m2
      mor-path {_ , _ , n1} {_ , _ , n2} {m1 = m1} {m2 = m2} p1 p2 = \i -> p1 i , p2 i , p3 i
        where
        p3 : PathP (\i -> (p1 i) ⋆ n2 == n1 ⋆ (p2 i)) (snd (snd m1)) (snd (snd m2))
        p3 = isProp->PathP (\_ -> isSet-Mor C _ _)

      ArrowLaws : CategoryLaws ArrowOps
      ArrowLaws .CategoryLaws.⋆-left-id (m1 , m2 , s1) = mor-path ⋆-left-id ⋆-left-id
      ArrowLaws .CategoryLaws.⋆-right-id (m1 , m2 , s1) = mor-path ⋆-right-id ⋆-right-id
      ArrowLaws .CategoryLaws.⋆-assoc _ _ _ = mor-path ⋆-assoc ⋆-assoc
      ArrowLaws .CategoryLaws.isSet-Mor =
        isSetΣ (isSet-Mor C) (\_ -> (isSetΣ (isSet-Mor C) (\_ -> (isProp->isSet (isSet-Mor C _ _)))))

  ArrowC : PreCategory (ℓ-max ℓO ℓM) ℓM
  ArrowC = Laws->Category ArrowLaws

module _ {ℓO ℓM : Level} {C : PreCategory ℓO ℓM} where
  open CategoryHelpers C
  open isIdentitySystem

  opaque
    isUnivalent-ArrowC : isUnivalent' C -> isUnivalent' (ArrowC C)
    isUnivalent-ArrowC univC = record { to-path = base-path ; to-path-over = over-path }
      where
      module _ {a1@(x1 , y1 , m1) : Obj (ArrowC C)}
               {a2@(x2 , y2 , m2) : Obj (ArrowC C)}
               (iso-arr : CatIso (ArrowC C) a1 a2) where
        iso-x : CatIso C x1 x2
        iso-x = record
          { mor = fst (CatIso.mor iso-arr)
          ; inv = fst (CatIso.inv iso-arr)
          ; sec = \i -> fst (CatIso.sec iso-arr i)
          ; ret = \i -> fst (CatIso.ret iso-arr i)
          }

        iso-y : CatIso C y1 y2
        iso-y = record
          { mor = fst (snd (CatIso.mor iso-arr))
          ; inv = fst (snd (CatIso.inv iso-arr))
          ; sec = \i -> fst (snd (CatIso.sec iso-arr i))
          ; ret = \i -> fst (snd (CatIso.ret iso-arr i))
          }

        module iso-x = CatIso iso-x
        module iso-y = CatIso iso-y

        inv-swap : (iso-x.inv ⋆ m1) == (m2 ⋆ iso-y.inv)
        inv-swap = snd (snd (CatIso.inv iso-arr))

        px : x1 == x2
        px = univC .to-path iso-x
        py : y1 == y2
        py = univC .to-path iso-y

        pm : PathP (\i -> C [ px i , py i ]) m1 m2
        pm = transP-mid (sym reduce-left) inner-path reduce-right
          where
          inner-path : PathP (\i -> C [ px i , py i ]) (id C ⋆ m1 ⋆ id C) (iso-x.inv ⋆ m1 ⋆ iso-y.mor)
          inner-path i = (CatIso.inv (univC .to-path-over iso-x i)) ⋆
                         m1 ⋆
                         (CatIso.mor (univC .to-path-over iso-y i))

          reduce-right : (CatIso.inv iso-x ⋆ m1 ⋆ CatIso.mor iso-y) == m2
          reduce-right = ⋆-left inv-swap >=> ⋆-assoc >=> ⋆-right iso-y.sec >=> ⋆-right-id
          reduce-left : (id C ⋆ m1 ⋆ id C) == m1
          reduce-left = ⋆-right-id >=> ⋆-left-id

        base-path : Path (Obj (ArrowC C)) a1 a2
        base-path i = px i , py i , pm i

        over-path : PathP (\i -> CatIso (ArrowC C) a1 (base-path i)) (idCatIso (ArrowC C) a1) iso-arr
        over-path = cat-iso-pathp refl base-path check2
          where
          check2 : PathP (\i -> (ArrowC C) [ a1 , (base-path i) ])
                     (CatIso.mor (idCatIso (ArrowC C) a1)) (CatIso.mor iso-arr)
          check2 i = p-m3 i , p-m4 i , p-s i
            where
            p-m3 : PathP (\i -> C [ x1 , (px i) ]) (id C) iso-x.mor
            p-m3 i = CatIso.mor (univC .to-path-over iso-x i)
            p-m4 : PathP (\i -> C [ y1 , (py i) ]) (id C) iso-y.mor
            p-m4 i = CatIso.mor (univC .to-path-over iso-y i)
            p-s : PathP (\i -> p-m3 i ⋆ pm i == m1 ⋆ p-m4 i)
                    (snd (snd (id (ArrowC C)))) (snd (snd (CatIso.mor iso-arr)))
            p-s = isProp->PathP (\i -> isSet-Mor C _ _)
