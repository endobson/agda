{-# OPTIONS --cubical --safe --exact-split #-}

module programming-languages.stx where

open import Agda.Builtin.String
open import base
open import relation
open import set-quotient



module _ (Discrete-String : Discrete String) where

  data STLCType : Type₀ where
    nat-type : STLCType
    fun-type : STLCType -> STLCType -> STLCType
  
  
  data RawTerm : Type₀ where
    nat : Nat -> RawTerm
    var : String -> RawTerm
    lam : String -> RawTerm -> RawTerm
    app : RawTerm -> RawTerm -> RawTerm
    if0 : RawTerm -> RawTerm -> RawTerm -> RawTerm

  data Context : Type₀ where
    hole : Context
    lam : String -> Context -> Context
    app-1 : Context -> RawTerm -> Context
    app-2 : RawTerm -> Context -> Context
    if0-1 : Context -> RawTerm -> RawTerm -> Context
    if0-2 : RawTerm -> Context -> RawTerm -> Context
    if0-3 : RawTerm -> RawTerm -> Context -> Context

  fill-context : Context -> RawTerm -> RawTerm
  fill-context hole t = t
  fill-context (lam v c) t = lam v (fill-context c t)
  fill-context (app-1 c a) t = app (fill-context c t) a
  fill-context (app-2 f c) t = app f (fill-context c t)
  fill-context (if0-1 c t f) rt = if0 (fill-context c rt) t f
  fill-context (if0-2 c t f) rt = if0 c (fill-context t rt) f
  fill-context (if0-3 c t f) rt = if0 c t (fill-context f rt)
  

  string-swap : String -> String -> String -> String
  string-swap s1 s2 v = handle (Discrete-String s1 v) (Discrete-String s2 v)
      where
      handle : Dec (s1 == v) -> Dec (s2 == v) -> String
      handle (yes _) _ = s2 
      handle (no _) (yes _) = s1 
      handle (no _) (no _) = v

  name-swap : String -> String -> RawTerm -> RawTerm
  name-swap s1 s2 = rec
    where
    rec : RawTerm -> RawTerm
    rec (nat n) = (nat n)
    rec (app f e) = (app (rec f) (rec e))
    rec (if0 c t f) = (if0 (rec c) (rec t) (rec f))
    rec (var v) = var (string-swap s1 s2 v)
    rec (lam v b) = lam (string-swap s1 s2 v) (rec b)

  subst : String -> RawTerm -> RawTerm -> RawTerm
  subst s m = rec
    where
    rec : RawTerm -> RawTerm
    rec (nat n) = (nat n)
    rec (app f e) = (app (rec f) (rec e))
    rec (if0 c t f) = (if0 (rec c) (rec t) (rec f))
    rec (var v) = handle (Discrete-String s v)
      where
      handle : Dec (s == v) -> RawTerm
      handle (yes _) = m
      handle (no _) = (var v)
    rec (lam v b) = handle (Discrete-String s v)
      where
      handle : Dec (s == v) -> RawTerm
      handle (yes _) = (lam v b)
      handle (no _) = (lam v (rec b))


  data α-equiv : RawTerm -> RawTerm -> Type₀ where
    nat-α : {n : Nat} -> α-equiv (nat n) (nat n)
    var-α : {s : String} -> α-equiv (var s) (var s)
    app-α : {f1 f2 a1 a2 : RawTerm} -> α-equiv f1 f2 -> α-equiv a1 a2 -> 
            α-equiv (app f1 a1) (app f2 a2)
    if0-α : {c1 c2 t1 t2 f1 f2 : RawTerm} -> 
            α-equiv c1 c2 -> α-equiv t1 t2 ->  α-equiv f1 f2 -> 
            α-equiv (if0 c1 t1 f1) (if0 c2 t2 f2)
    lam-α : {s1 s2 : String} {b1 b2 : RawTerm} -> α-equiv b1 (name-swap s1 s2 b2) ->
            α-equiv (lam s1 b1) (lam s2 b2)

  αEqTerm : Type₀
  αEqTerm = RawTerm / α-equiv

  data β-Step : Rel RawTerm ℓ-zero where
    β-step : (v : String) (b a : RawTerm) -> β-Step (app (lam v b) a) (subst v a b)

  data δ-Step : Rel RawTerm ℓ-zero where
    δ-step-if0-zero : (a b : RawTerm) -> δ-Step (if0 (nat 0) a b) a
    δ-step-if0-suc : (n : Nat) (a b : RawTerm) -> δ-Step (if0 (nat (suc n)) a b) b

  βδ-Step : Rel RawTerm ℓ-zero
  βδ-Step a b = β-Step a b ⊎ δ-Step a b

  
  data βδ-Reduce₁ : Rel RawTerm ℓ-zero where
    βδ-reduce : {a b : RawTerm} (c : Context) (r : βδ-Step a b) -> 
                βδ-Reduce₁ (fill-context c a) (fill-context c b)


  data isValue : Pred RawTerm ℓ-zero where
    isValue-lam : {s : String} {b : RawTerm} -> isValue (lam s b)
    isValue-nat : {n : Nat} -> isValue (nat n)
