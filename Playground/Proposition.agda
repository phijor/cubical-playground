module Playground.Proposition where

open import Playground.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (lCancel)

open import Cubical.Functions.Image
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

isProp' : ∀ {ℓ} (X : Type ℓ) → Type ℓ
isProp' X = (x y : X) → isContr (x ≡ y)

isPropIsProp' : ∀ {ℓ} {X : Type ℓ} → isProp (isProp' X)
isPropIsProp' = isPropΠ2 λ x y → isPropIsContr

module _ {ℓ} {X : Type ℓ} where

  private
    α : isProp' X → isContr (X → X)
    α p = (λ x → x) , λ f → funExt λ x → p x (f x) .fst

    β : isContr (X → X) → isProp' X
    β ctr x y = funExt⁻ p x , J (λ z (q : x ≡ z) → funExt⁻ p x ≡ q) (lCancel (funExt⁻ (const≡ x) x)) where
      f : X → X
      f = ctr .fst

      const≡ : ∀ z → f ≡ (λ _ → z)
      const≡ z = ctr .snd (λ _ → z)

      p : ∀ {x y} → (λ _ → x) ≡ (λ _ → y)
      p {x} {y} = sym (const≡ x) ∙ const≡ y

  isProp'≃isContrEndo : isProp' X ≃ isContr (X → X)
  isProp'≃isContrEndo = propBiimpl→Equiv isPropIsProp' isPropIsContr α β

propImageElim : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
  → (P : B → Type ℓ'')
  → (propP : isProp (Σ[ b ∈ B ] P b))
  → (f : A → B)
  → (Pf : ∀ a → P (f a))
  → ∥ A ∥₁ → B
propImageElim {A = A} {B} P propP f Pf = fst ∘ f* where
  f*P : A → Σ[ b ∈ B ] (P b)
  f*P a = f a , Pf a

  f* : ∥ A ∥₁ → Σ[ b ∈ B ] (P b)
  f* = PT.rec propP f*P

propImageElim' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B)
  → isProp (Image f)
  → ∥ A ∥₁ → B
propImageElim' {A = A} f propIm = fst ∘ restrict-f where
  restrict-f : ∥ A ∥₁ → Image f
  restrict-f = PT.rec propIm (restrictToImage f)
