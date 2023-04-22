module Playground.PathReasoning where

open import Playground.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ

≡-end : (x y : A) → (p : x ≡ y) → _
≡-end = ?

syntax ≡-end x y p =
  x ≡ y by p ∎
