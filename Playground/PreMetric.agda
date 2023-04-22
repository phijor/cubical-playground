module Playground.PreMetric where

open import Playground.Prelude
open import Playground.PosRat

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming (_/_ to _/₂_)

record IsPreMetric {ℓ ℓ'} {A : Type ℓ} (_≈[_]_ : A → ℚ⁺ → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  open BinaryRelation

  field
    ≈IsProp : ∀ {ε} → isPropValued (_≈[ ε ]_)
    ≈refl : ∀ {ε} → isRefl (_≈[ ε ]_)
    ≈sym : ∀ {ε} → isSym (_≈[ ε ]_)
    ≈separated : ∀ {a b : A} → ((ε : ℚ⁺) → a ≈[ ε ] b) → a ≡ b
    ≈triangular : ∀ {a b c : A} ε δ → a ≈[ ε ] b → b ≈[ δ ] c → a ≈[ ε + δ ] c
    ≈round : ∀ {ε} {a b : A} → a ≈[ ε ] b ≃ (∃[ δ ∈ ℚ⁺ ] (δ < ε) × a ≈[ δ ] b)

record PreMetricStr {ℓ} ℓ' (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    _≈[_]_ : A → ℚ⁺ → A → Type ℓ'
    isPreMetric : IsPreMetric _≈[_]_

  open IsPreMetric isPreMetric public

PreMetric : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
PreMetric ℓ ℓ' = TypeWithStr ℓ (PreMetricStr ℓ')

module _ {ℓ ℓ'} (A : PreMetric ℓ ℓ') where
  open module A = PreMetricStr (str A)

  Approximation : Type _
  Approximation = Σ[ x ∈ (ℚ⁺ → ⟨ A ⟩) ] ∀ ε δ → x ε ≈[ ε + δ ] x δ

  IsLimit : (x : Approximation) (l : ⟨ A ⟩) → Type _
  IsLimit (x , _) l = ∀ ε δ → x ε ≈[ ε + δ ] l

  isPropIsLimit : ∀ x l → isProp (IsLimit x l)
  isPropIsLimit (x , _) l = isPropΠ2 λ ε δ → ≈IsProp (x ε) l

  Limit : (x : Approximation) → Type _
  Limit x = Σ[ l ∈ ⟨ A ⟩ ] IsLimit x l

  isPropLimit : (x : Approximation) → isProp (Limit x)
  isPropLimit x (l₁ , islim₁) (l₂ , islim₂) = Σ≡Prop (isPropIsLimit x) goal where
    approx : ∀ ε → l₁ ≈[ ε ] l₂
    approx ε = ≈triangular (ε /2) (ε /2) {!islim₁ !} {! !}

    goal : l₁ ≡ l₂
    goal = ≈separated approx

