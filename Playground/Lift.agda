module Playground.Lift where

open import Playground.Prelude

open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Foundations.Equiv using (LiftEquiv ; invEquiv ; invIsEq ; secIsEq)
open import Cubical.Functions.Embedding using (isEmbedding ; universeEmbedding ; liftEmbedding)

module _ {ℓ₀ ℓ₁ : Level} where
  unliftPath : (X Y : Type ℓ₀) → Lift {j = ℓ₁} X ≡ Lift {j = ℓ₁} Y → X ≡ Y
  unliftPath X Y = invIsEq (liftEmbedding ℓ₀ ℓ₁ X Y)

  congLift-unliftPath-section : {X Y : Type ℓ₀} → section (cong {x = X} {y = Y} Lift) (unliftPath X Y)
  congLift-unliftPath-section {X} {Y} = secIsEq (liftEmbedding ℓ₀ ℓ₁ X Y)
