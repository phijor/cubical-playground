module Playground.Universe.Base where

open import Playground.Prelude

record Universe (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Code : Type ℓ
    El : Code → Type ℓ
