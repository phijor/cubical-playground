module Playground.UniverseTruncation where

open import Playground.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary.Base

private
  variable
    ℓ : Level

TruncType→hProp : ∥ Type ℓ ∥₂ → hProp ℓ
-- TruncType→hProp = ST.elim (λ _ → isSetHProp) λ X → ∥ X ∥₁ , isPropPropTrunc
TruncType→hProp = ST.elim (λ _ → isSetHProp) λ X → (X → ⊥) , isProp→ isProp⊥

hProp→TruncType : hProp ℓ → ∥ Type ℓ ∥₂
-- hProp→TruncType (P , isPropP) = ∣ P ∣₂
hProp→TruncType (P , isPropP) = ∣ (P → ⊥) ∣₂

TruncTypeHPropIso : Iso ∥ Type ℓ ∥₂ (hProp ℓ)
TruncTypeHPropIso .Iso.fun = TruncType→hProp
TruncTypeHPropIso .Iso.inv = hProp→TruncType
TruncTypeHPropIso .Iso.rightInv (P , isPropP) = Σ≡Prop (λ _ → isPropIsProp) {! !} -- (propTruncIdempotent isPropP)
TruncTypeHPropIso .Iso.leftInv = ST.elim (λ ∣X∣₂ → isProp→isSet (isSetSetTrunc _ ∣X∣₂)) λ X → cong ∣_∣₂ {! !}

TruncTypeHPropIso→LEM : ∥ Type ℓ ∥₂ ≡ (hProp ℓ) → (P : Type ℓ) → isProp P → (¬ ¬ P) ≡ P
TruncTypeHPropIso→LEM teq P propP = {! cong₂ _≡_ teq teq!}
