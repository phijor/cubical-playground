module Playground.Cost where

open import Playground.Prelude

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Monoid

Cost : ∀ {ℓ ℓ'} → (R : Type ℓ') → Type ℓ → Type _
Cost R A = A × ∥ R ∥₁

module _ {ℓ'} {R : Type ℓ'} (_⊕_ : R → R → R) (ε : R) where
  private
    variable
      ℓ : Level
      A B C : Type ℓ


  Cost≡ : {x y : Cost R A} → x .fst ≡ y .fst → x ≡ y
  Cost≡ = Σ≡Prop λ _ → isPropPropTrunc

  return : A → Cost R A
  return = _, ∣ ε ∣₁

  _>>=_ : Cost R A → (A → Cost R B) → Cost R B
  (x , r) >>= g =
    let (y , s) = g x
    in y , PT.map2 _⊕_ r s

  >>=-return : {f : Cost R A} → (f >>= return) ≡ f
  >>=-return = Cost≡ refl

  return->>= : {a : A} {f : A → Cost R B} → (return a >>= f) ≡ (f a)
  return->>= = Cost≡ refl

  >>=-assoc : (f : Cost R A) (g : A → Cost R B) (h : B → Cost R C)
    → (f >>= g) >>= h ≡ f >>= (λ x → g x >>= h)
  >>=-assoc f g h = Cost≡ refl
