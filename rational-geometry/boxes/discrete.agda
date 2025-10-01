{-# OPTIONS --cubical --safe --exact-split #-}

module rational-geometry.boxes.discrete where

open import base
open import decision
open import discrete
open import equality-path
open import rational
open import rational-geometry.boxes.box

private
  Discrete-Box : Discrete Box
  Discrete-Box b₁ b₂ = handle (decide-= _ _) (decide-= _ _) (decide-= _ _) (decide-= _ _)
    where
    module b₁ = Box b₁
    module b₂ = Box b₂
    handle : Dec (b₁.left == b₂.left) ->
             Dec (b₁.right == b₂.right) ->
             Dec (b₁.bottom == b₂.bottom) ->
             Dec (b₁.top == b₂.top) ->
             Dec (b₁ == b₂)
    handle (no ¬pl) _        _        _        = no (\p -> ¬pl (cong Box.left p))
    handle (yes pl) (no ¬pr) _        _        = no (\p -> ¬pr (cong Box.right p))
    handle (yes pl) (yes pr) (no ¬pb) _        = no (\p -> ¬pb (cong Box.bottom p))
    handle (yes pl) (yes pr) (yes pb) (no ¬pt) = no (\p -> ¬pt (cong Box.top p))
    handle (yes pl) (yes pr) (yes pb) (yes pt) = yes (Box-coord-path _ _ pl pr pb pt)

instance
  Discrete'-Box : Discrete' Box
  Discrete'-Box = record { f = Discrete-Box }
