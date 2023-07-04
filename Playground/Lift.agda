module Playground.Lift where

open import Playground.Prelude

open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Foundations.Equiv using (LiftEquiv ; invEquiv ; invIsEq ; secIsEq)
open import Cubical.Functions.Embedding using (isEmbedding ; universeEmbedding)

module _ {ℓ₀ ℓ₁ : Level} where
  isEmbeddingLift : isEmbedding (Lift {ℓ₀} {ℓ₁})
  isEmbeddingLift = universeEmbedding Lift (λ X → invEquiv LiftEquiv)

  unlift : (X Y : Type ℓ₀) → Lift {j = ℓ₁} X ≡ Lift {j = ℓ₁} Y → X ≡ Y
  unlift X Y = invIsEq (isEmbeddingLift X Y)

  congLift-unlift-section : {X Y : Type ℓ₀} → section (cong {x = X} {y = Y} Lift) (unlift X Y)
  congLift-unlift-section {X} {Y} = secIsEq (isEmbeddingLift X Y)
