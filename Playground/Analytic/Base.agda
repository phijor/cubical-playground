module Playground.Analytic.Base where

open import Playground.Prelude

open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma.Base
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥₁)
open import Cubical.Relation.Binary.Base using (Rel)

record Container (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Shape : Type ℓ
    Pos : Shape → Type ℓ
    Symm : {s : Shape} → (σ : Pos s ≃ Pos s) → Type ℓ

    isSetShape : isSet Shape
    isSetPos : (s : Shape) → isSet (Pos s)
    isPropSymm : ∀ {s} {σ : Pos s ≃ Pos s} → isProp (Symm σ)
    reflSymm : ∀ s → Symm (idEquiv $ Pos s)
    invSymm : ∀ {s} {σ : Pos s ≃ Pos s} → Symm σ → Symm (invEquiv σ)
    compSymm : ∀ {s} {σ τ : Pos s ≃ Pos s} → Symm σ → Symm τ → Symm (σ ∙ₑ τ)

  _∼∞_ : ∀ {ℓX} {s : Shape} {X : Type ℓX} → Rel (Pos s → X) (Pos s → X) (ℓ-max ℓ ℓX)
  _∼∞_ {s = s} u v = Σ[ σ ∈ (Pos s ≃ Pos s) ] Symm σ × (u ≡ v ∘ equivFun σ)

  _∼_ : ∀ {ℓX} {s : Shape} {X : Type ℓX} → Rel (Pos s → X) (Pos s → X) (ℓ-max ℓ ℓX)
  u ∼ v = ∥ u ∼∞ v ∥₁

record Analytic {ℓ ℓX} (C : Container ℓ) (X : Type ℓX) : Type (ℓ-max ℓ ℓX) where
  private
    open module C = Container C

  field
    shape : Shape

  Label : Type (ℓ-max ℓ ℓX)
  Label = (Pos shape → X) / _∼_

  field
    label : Label

AnalyticΣ : ∀ {ℓ ℓX} (C : Container ℓ) (X : Type ℓX) → Type (ℓ-max ℓ ℓX)
AnalyticΣ C X = Σ[ shape ∈ Shape ] ((Pos shape → X) / _∼_)
  where open Container C
