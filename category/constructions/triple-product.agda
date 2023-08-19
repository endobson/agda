{-# OPTIONS --cubical --safe --exact-split #-}

module category.constructions.triple-product where

open import base
open import category.base
open import hlevel

record Triple {ℓA ℓB ℓC : Level} (A : Type ℓA) (B : Type ℓB) (C : Type ℓC) :
       Type (ℓ-max* 3 ℓA ℓB ℓC) where
  constructor triple
  field
    a : A
    b : B
    c : C

isSet-Triple :
  {ℓA ℓB ℓC : Level} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} ->
  isSet A -> isSet B -> isSet C -> isSet (Triple A B C)
isSet-Triple hA hB hC (triple a1 b1 c1) (triple a2 b2 c2) p1 p2 i j =
  triple (hA a1 a2 (\i -> Triple.a (p1 i)) (\i -> Triple.a (p2 i)) i j)
         (hB b1 b2 (\i -> Triple.b (p1 i)) (\i -> Triple.b (p2 i)) i j)
         (hC c1 c2 (\i -> Triple.c (p1 i)) (\i -> Triple.c (p2 i)) i j)

module _ {ℓCo ℓCm ℓDo ℓDm ℓEo ℓEm : Level}
         (C : PreCategory ℓCo ℓCm) (D : PreCategory ℓDo ℓDm) (E : PreCategory ℓEo ℓEm) where
  private
    module C = PreCategory C
    module D = PreCategory D
    module E = PreCategory E
    ℓo = ℓ-max* 3 ℓCo ℓDo ℓEo
    ℓm = ℓ-max* 3 ℓCm ℓDm ℓEm

  TripleCat : PreCategory ℓo ℓm
  TripleCat = record
    { Obj = TripleObj
    ; Mor = TripleMor
    ; id = triple C.id D.id E.id
    ; _⋆_ = \ (triple cf df ef) (triple cg dg eg) ->
              triple (cf ⋆⟨ C ⟩ cg) (df ⋆⟨ D ⟩ dg) (ef ⋆⟨ E ⟩ eg)
    ; ⋆-left-id = \ (triple f g h) i -> triple (C.⋆-left-id f i) (D.⋆-left-id g i) (E.⋆-left-id h i)
    ; ⋆-right-id = \ (triple f g h) i -> triple (C.⋆-right-id f i) (D.⋆-right-id g i) (E.⋆-right-id h i)
    ; ⋆-assoc = \ (triple cf df ef) (triple cg dg eg) (triple ch dh eh) i ->
                  triple (C.⋆-assoc cf cg ch i) (D.⋆-assoc df dg dh i) (E.⋆-assoc ef eg eh i)
    ; isSet-Mor = isSet-Triple (isSet-Mor C) (isSet-Mor D) (isSet-Mor E)
    }
    where
    TripleObj : Type ℓo
    TripleObj = Triple C.Obj D.Obj E.Obj

    TripleMor : (s t : TripleObj) -> Type ℓm
    TripleMor (triple s-c s-d s-e) (triple t-c t-d t-e) =
      Triple (C [ s-c , t-c ]) (D [ s-d , t-d ]) (E [ s-e , t-e ])
