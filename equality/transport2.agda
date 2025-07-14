{-# OPTIONS --cubical --safe --exact-split #-}

module equality.transport2 where

open import base
open import cubical
open import hlevel.base
open import equality-path
open import equality.square
open import equivalence.base
open import equivalence
open import isomorphism

-- record isHAEquiv {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : Type (ℓ-max ℓ ℓ') where
--   field
--     g : B → A
--     linv : ∀ a → g (f a) ≡ a
--     rinv : ∀ b → f (g b) ≡ b
--     com : ∀ a → cong f (linv a) ≡ rinv (f a)



isHalfAdjoint : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} -> Iso A B -> Type (ℓ-max ℓA ℓB)
isHalfAdjoint {A = A} (iso fun inv linv rinv) =
  ∀ (a : A) -> cong fun (rinv a) == linv (fun a)


module _ {ℓ : Level} {A B : Type ℓ} (p : A == B) where

  transport-Iso : Iso A B
  transport-Iso .Iso.fun = transport p
  transport-Iso .Iso.inv = transport (sym p)
  transport-Iso .Iso.rightInv = transport-sym (sym p)
  transport-Iso .Iso.leftInv = transport-sym p



module _ where
  isHalfAdjoint-transport-refl : {ℓ : Level} -> (A : Type ℓ) -> isHalfAdjoint (transport-Iso (reflᵉ A))
  isHalfAdjoint-transport-refl {ℓ} A a = \k i -> ans (~ k) i
    where
    p = reflᵉ A
    v = a
    T : Type ℓ
    T = transport refl (transport refl (transport refl v)) == transport refl v

    left-v : T
    left-v = transport-sym (sym p) (transport p v)
    left-check : left-v ==
      (\i ->
        transp (\j -> p (j ∨ i)) i
          (transp (\j -> p (~ j ∨ i)) i
            (transp (\j -> p j) i0 v)))
    left-check = refl
    left-check' : left-v ==
      (\i ->
        transp (\j -> A) i
          (transp (\j -> A) i
            (transp (\j -> A) i0 v)))
    left-check' = refl


    right-v : T
    right-v = (\i -> transport p (transport-sym p v i))
    right-check : right-v ==
      (\i ->
        transp (\j -> p j) i0
          (transp (\j -> p (~ j ∧ ~ i)) i
            (transp (\j -> p (j ∧ ~ i)) i v)))
    right-check = refl
    right-check' : right-v ==
      (\i ->
        transp (\j -> A) i0
          (transp (\j -> A) i
            (transp (\j -> A) i v)))
    right-check' = refl

    mid-v : T
    mid-v =
      (\i ->
        transp (\j -> A) i
          (transp (\j -> A) i0
            (transp (\j -> A) i v)))

    base : (transport refl (transport refl v)) == v
    base = transport-sym p v

    ans : I -> I -> A
    ans k i =
      hcomp (\l -> \{ (k = i0) -> transp (\j -> A) (i ∨ ~ l)
                                    (transp (\j -> A) (i ∨ ~ l)
                                      (transp (\j -> A) (~ l) v))
                    ; (k = i1) -> transp (\j -> A) (~ l)
                                    (transp (\j -> A) (i ∨ ~ l)
                                      (transp (\j -> A) (i ∨ ~ l) v))
                    ; (i = i0) -> transp (\j -> A) (~ l)
                                    (transp (\j -> A) (~ l)
                                      (transp (\j -> A) (~ l) v))
                    ; (i = i1) -> transp (\j -> A) (~ l) v
                    })
        v


    check-ans₁ : (i : I) -> ans i0 i == left-v i
    check-ans₁ _ = refl
    check-ans₂ : (i : I) -> ans i1 i == right-v i
    check-ans₂ _ = refl
    check-ans₃ : (k : I) -> ans k i0 ==
      (transport p (transport (sym p) (transport p v)))
    check-ans₃ _ = refl
    check-ans₄ : (k : I) -> ans k i1 == transport p v
    check-ans₄ _ = refl

    {-


    module attempt₁ where
      ans : I -> I -> A -- left-v == right-v
      -- ans : left-v == right-v
      ans k i =
        transp (\j -> A) (~ k ∧ i)
          (transp (\j -> A) i
            (transp (\j -> A) (k ∧ i) v))

      ans₂ : (k : I) -> ans k i1 == (transport p v)
      ans₂ k l =
        transp (\j -> A) (~ k ∧ ~ l)
          (transp (\j -> A) (k ∨ l) v)

      ans₃ : (k i : I) -> A
      ans₃ k i =
        hcomp (\l -> \{ (k = i0) -> ans k i
                      ; (k = i1) -> ans k i
                      ; (i = i0) -> ans k i
                      -- ; (i = i1) -> ans₂ k l
                      })
          (ans k i)



      check-ans₁ : (i : I) -> ans i0 i == left-v i
      check-ans₁ _ = refl
      check-ans₂ : (i : I) -> ans i1 i == right-v i
      check-ans₂ _ = refl
      check-ans₄ : (k : I) -> ans k i0 ==
        (transport p (transport (sym p) (transport p v)))
      check-ans₄ _ = refl

      check-ans₃ : (k : I) -> ans k i1 ==
        transp (\j -> A) (~ k)
          (transp (\j -> A) k v)
      check-ans₃ _ = refl

    -}


  isHalfAdjoint-transport : {ℓ : Level} -> (A B : Type ℓ) (p : A == B) ->
     isHalfAdjoint (transport-Iso p)
  isHalfAdjoint-transport {ℓ} A B p =
    transport (\i -> isHalfAdjoint (transport-Iso (\j -> p (i ∧ j))))
      (isHalfAdjoint-transport-refl A)




module _ {ℓ : Level} {A B : Type ℓ} (v : A) (p : A == B) where
  trans-sym-mess :
     transport-sym (sym p) (transport p v) ==
     (\j -> transport p (transport-sym p v j))
  trans-sym-mess = sym (isHalfAdjoint-transport A B p v)





{-
  isHAEquiv-id : isHAEquiv (\ (x : A) -> x)
  isHAEquiv-id = record
    { g = \x -> x
    ; linv = \_ -> refl
    ; rinv = \_ -> refl
    ; com = \_ -> refl
    }

  isHAEquiv-trans : isHAEquiv (transport p)
  isHAEquiv-trans =
    transport (\i -> isHAEquiv (\x -> transp (\j -> p (i ∧ j)) (~ i) x))
      isHAEquiv-id

  check-g : isHAEquiv.g isHAEquiv-trans == transport (sym p)
  check-g = ?



module _ {ℓ : Level} {A B : Type ℓ} (v : A) (p : A == B) (magic : Magic) where



  trans-sym-mess :
     transport-sym (sym p) (transport p v) ==
     (\j -> transport p (transport-sym p v j))
  trans-sym-mess = magic
    where
    T : Type ℓ
    T = (transport p (transport (sym p) (transport p v)) == transport p v)
    left-f : (a : A) -> (transport p (transport (sym p) (transport p a)) == transport p a)
    left-f a = transport-sym (sym p) (transport p a)

    left-v : T
    left-v = transport-sym (sym p) (transport p v)
    left-check : left-v ==
      (\i ->
        transp (\j -> p (j ∨ i)) i
          (transp (\j -> p (~ j ∨ i)) i
            (transp (\j -> p j) i0 v)))
    left-check = refl


    right-v : T
    right-v = (\i -> transport p (transport-sym p v i))
    right-check : right-v ==
      (\i ->
        transp (\j -> p j) i0
          (transp (\j -> p (~ j ∧ ~ i)) i
            (transp (\j -> p (j ∧ ~ i)) i v)))
    right = refl


    up : A -> B
    up = transp (\j -> p j) i0
    down : B -> A
    down = transp (\j -> p (~ j)) i0

    u-α : (i : I) -> A -> p i
    u-α i = transp (\j -> p (j ∧ i)) (~ i)
    u-β : (i : I) -> p i -> B
    u-β i = transp (\j -> p (j ∨ i)) i
    d-α : (i : I) -> B -> p i
    d-α i = transp (\j -> p (~ j ∨ i)) i
    d-β : (i : I) -> p i -> A
    d-β i = transp (\j -> p (~ j ∧ i)) (~ i)


    left-check₂ : left-v == (\i -> u-β i (d-α i (up v)))
    left-check₂ = refl
    right-check₂ : right-v == (\i -> up (d-β (~ i) (u-α (~ i) v)))
    right-check₂ = refl


    combined : (i j : I) -> B
    combined i j = u-β i (d-α i (up (d-β (~ j) (u-α (~ j) v))))

    combined-i-1 : (i : I) -> combined i  i1 == left-v i
    combined-i-1 _ = refl
    combined-1-j : (j : I) -> combined i1 j  == right-v j
    combined-1-j _ = refl

    combined-i-0 : (i : I) -> combined i  i0 == left-f (down (up v)) i
    combined-i-0 _ = refl
    combined-0-j : (j : I) -> combined i0 j  == up (down (right-v j))
    combined-0-j _ = refl




  -- base : v == v
  -- base = reflᵉ A
  -- roof : B == B
  -- roof = reflᵉ B
  -- up : A == B
  -- up = p
  -- down : B == A
  -- down = sym p
-}
