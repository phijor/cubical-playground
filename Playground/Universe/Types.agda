module Playground.Universe.Types where

open import Playground.Prelude
open import Playground.Lift using (unliftPath ; congLift-unliftPath-section)

open import Playground.Universe.Base
open import Playground.Universe.Univalence

open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Univalence

-- Lifting a Type into the successor universe
Lift⁺ : ∀ {ℓ : Level} → Type ℓ → Type (ℓ-suc ℓ)
Lift⁺ {ℓ} = Lift {i = ℓ} {j = ℓ-suc ℓ}

-- The universe of ℓ-small types
𝓤 : (ℓ : Level) → Universe (ℓ-suc ℓ)
𝓤 ℓ .Universe.Code = Type ℓ
𝓤 ℓ .Universe.El = Lift⁺

-- The decoding function (Lift⁺) determines paths in the type of codes
ua𝓤 : ∀ {ℓ} → (A B : Type ℓ) → Lift⁺ A ≃ Lift⁺ B → A ≡ B
ua𝓤 A B α = unliftPath A B (ua α)

-- The action of the decoding on paths (cong Lift⁺) has a section,
-- namely unliftPath.  This characterizes the univalence function in the universe.
ua𝓤-β : ∀ {ℓ} → (A B : Type ℓ) (α : Lift⁺ A ≃ Lift⁺ B) → cong Lift⁺ (unliftPath A B (ua α)) ≡ ua α
ua𝓤-β A B α = congLift-unliftPath-section (ua α)

-- The universe of ℓ-small types is univalent, with the equivalence derived from `ua𝓤`
isUnivalent𝓤 : ∀ {ℓ} → isUnivalent (𝓤 ℓ)
isUnivalent𝓤 = Univalence.hasUA→isUnivalent _ ua𝓤 (λ {A} {B} → ua𝓤-β A B)
