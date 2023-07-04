module Playground.Torus where

open import Playground.Prelude

data T : Type where
  pt : T
  l₁ l₂ : pt ≡ pt
  sq : l₁ ∙ l₂ ≡ l₂ ∙ l₁

elim : {P : T → Type}
  → (pt* : P pt)
  → (l₁* : PathP (λ i → P (l₁ i)) pt* pt*)
  → (l₂* : PathP (λ i → P (l₂ i)) pt* pt*)
  → (sq* : PathP
      (λ i → PathP (λ j → P (sq i j)) pt* pt*)
      (compPathP' {B = P} l₁* l₂*)
      (compPathP' {B = P} l₂* l₁*))
  → (t : T) → P t
elim pt* l₁* l₂* sq* pt = pt*
elim pt* l₁* l₂* sq* (l₁ i) = l₁* i
elim pt* l₁* l₂* sq* (l₂ i) = l₂* i
elim pt* l₁* l₂* sq* (sq i j) = sq* i j
