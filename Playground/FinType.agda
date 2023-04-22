{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Playground.FinType where

open import Playground.Prelude

open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.FinType
open import Cubical.Data.SumFin.Base using (Fin ; fzero ; fsuc ; _⊎_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST

private
  variable
    ℓ : Level

card : {n : ℕ} (k : Fin n) → FinType ℓ n → ℕ
card {n = suc n} fzero (X , fin-∥X∥₂ , _) = fin-∥X∥₂ .fst
card {n = suc n} (fsuc k) (X , (zero , ∣α∣) , fin-path) = PT.elim→Set (λ _ → isSetℕ) {! !} {! !} ∣α∣ where
  absurd : ∥ X ∥₂ ≃ ⊥ → ℕ
  absurd α = Empty.rec {! !}
card {n = suc n} (fsuc k) (X , (suc sz , ∣α∣) , fin-path) = PT.elim→Set (λ _ → isSetℕ) card' {! !} ∣α∣
  where
    card₀ : ∥ X ∥₂ → ℕ
    card₀ = ST.rec isSetℕ (λ (x : X) → card k ((x ≡ x) , fin-path x x))

    -- Does not work, since loop-spaces Ω(x) ≠ Ω(y), in general.
    well-defined : (x y : ∥ X ∥₂) → card₀ x ≡ card₀ y
    well-defined = ST.elim2 (λ x y → isProp→isSet (isSetℕ (card₀ x) (card₀ y))) {! !}

    card' : (α : ∥ X ∥₂ ≃ Unit ⊎ Fin sz) → ℕ
    card' α = card₀ (invEq α fzero)

--     well-defined : (α β : ∥ X ∥₂ ≃ Unit ⊎ Fin sz) → card' α ≡ card' β
--     well-defined α β = ST.rec2 (isProp→isSet (isSetℕ (card' α) (card' β))) {! !}
--       (invEq α fzero)
--       (invEq β fzero)
