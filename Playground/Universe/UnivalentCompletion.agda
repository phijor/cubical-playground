module Playground.Universe.UnivalentCompletion where

open import Playground.Prelude
open import Playground.Lift using (unlift ; congLift-unlift-section ; isEmbeddingLift)

open import Playground.Universe.Base
open import Playground.Universe.Embedding

open import Playground.EquivToFamily using (module EquivToFamily)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁)

module Completion {ℓ} (V : Universe ℓ) where
  open EquivToFamily using (Connected ; Connected≡)

  open Universe

  U : Universe (ℓ-suc ℓ)
  U .Code = Connected (V .El)
  U .El = Lift ∘ ⟨_⟩

  uaU : (s t : U .Code) → U .El s ≃ U .El t → s ≡ t
  uaU s t α = Connected≡ (V .El) (unlift ⟨ s ⟩ ⟨ t ⟩ (ua α))

  uaU-β : (s t : U .Code) (α : U .El s ≃ U .El t) → cong (U .El) (uaU s t α) ≡ ua α
  uaU-β s t α = congLift-unlift-section {X = ⟨ s ⟩} {Y = ⟨ t ⟩} (ua α)

  open import Playground.Universe.Univalence using (isUnivalent ; module Univalence)

  isUnivalentCompletion : isUnivalent U
  isUnivalentCompletion = Univalence.hasUA→isUnivalent U uaU (λ {s} {t} → uaU-β s t)

  embedding : V ↪ U
  embedding = ι , {! !} where
    ι : V .Code → Connected (V .El)
    ι s = V .El s , ∣ s , idEquiv _ ∣₁

    ι-embstr : UniverseEmbeddingStr V U ι
    ι-embstr .UniverseEmbeddingStr.is-emb = {! !}
    ι-embstr .UniverseEmbeddingStr.decode-equiv = goal where
      goal : (s : V .Code) → Lift ⟨ ι s ⟩ ≃ V .El s
      goal s = invEquiv (LiftEquiv {A = ⟨ ι s ⟩})

open Completion
  renaming (U to Completion)
  using (isUnivalentCompletion)
  public

module UniversalProperty where
  open import Playground.Universe.Univalence
  open import Playground.Universe.Embedding
  open Universe

  isMinimal : ∀ {ℓ}
    → (V : Universe ℓ)
    → (U : Universe (ℓ-suc ℓ))
    → isUnivalent U
    → V ↪ U
    → Completion V ↪ U
  isMinimal V U uniU (ι , ι-emb) = γ , {! !} where
    γ : Completion V .Code → U .Code
    γ x = {! !}

