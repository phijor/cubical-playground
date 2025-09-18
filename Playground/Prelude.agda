-- {-# OPTIONS --safe #-}

module Playground.Prelude where

open import Cubical.Foundations.Prelude as C hiding (_∙_)
  public
open import Cubical.Foundations.Function
  public
open import Cubical.Foundations.Equiv
  renaming (_■ to _≃∎)
  public

_∙_ : {ℓ : Level} → {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
_∙_ = C._∙_

refl′ : ∀ {ℓ} {A : Type ℓ} → (a : A) → a ≡ a
refl′ a i = a

the : ∀ {ℓ} (A : Type ℓ) → (a : A) → A
the A a = a

module PathReasoning where
  private
    variable
      ℓ : Level
      A : Type ℓ

  ≡⟨⟩∎-syntax : ∀ (x y : A) → x ≡ y → x ≡ y
  ≡⟨⟩∎-syntax _ _ p = p
  {-# INLINE ≡⟨⟩∎-syntax #-}

  infixr 3 ≡⟨⟩∎-syntax
  syntax ≡⟨⟩∎-syntax x y p = x ≡⟨ p ⟩∎ y ∎

open PathReasoning using (≡⟨⟩∎-syntax) public

module _ where
  infixr 0 _≃⟨⟩_
  _≃⟨⟩_ : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} → A ≃ B → A ≃ B
  A ≃⟨⟩ e = e

ℓ-of : ∀ {ℓ} (A : Type ℓ) → Level
ℓ-of {ℓ} _ = ℓ

private
  variable
    ℓ : Level
    A B C : Type ℓ

_⨟_ : (f : A → B) (g : B → C) → A → C
f ⨟ g = λ a → g (f a)

_→⟨_⟩_ : (A : Type ℓ) → (A → B) → (B → C) → (A → C)
_ →⟨ f ⟩ g = f ⨟ g

_→≃⟨_⟩_ : (A : Type ℓ) → (A ≃ B) → (B → C) → (A → C)
_ →≃⟨ e ⟩ g = equivFun e ⨟ g

_→∎ : (A : Type ℓ) → A → A
A →∎ = λ a → a
{-# INLINE _→∎ #-}

infixr 0 _→⟨_⟩_
infixr 0 _→≃⟨_⟩_
infix 1 _→∎
