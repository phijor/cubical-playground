module Playground.Universe.Base where

open import Playground.Prelude

open import Cubical.Foundations.Equiv.Base

record Universe (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Code : Type ℓ
    El : Code → Type ℓ

  idElEquiv : (s : Code) → El s ≃ El s
  idElEquiv s = idEquiv (El s)

open Universe

UniversePath : ∀ {ℓ} {U V : Universe ℓ}
  → (p : U .Code ≡ V .Code)
  → (q : PathP (λ i → p i → Type ℓ) (U .El) (V .El))
  → U ≡ V
UniversePath p q i .Code = p i
UniversePath p q i .El = q i
