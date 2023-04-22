module Playground.FinSet where

open import Playground.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
import Cubical.Foundations.Univalence.Universe as UniverseUnivalence

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary.Base

private
  variable
    ℓ : Level

un : ∀ (s t : FinSet ℓ) → ⟨ s ⟩ ≃ ⟨ t ⟩ → s ≡ t
un s t e = Σ≡Prop (λ _ → isPropIsFinSet) (ua e)

comp' : ∀ {s t} (e : ⟨ s ⟩ ≃ ⟨ t ⟩) → cong ⟨_⟩ (un s t e) ≡ ua e
comp' e = refl
