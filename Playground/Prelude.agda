-- {-# OPTIONS --safe #-}

module Playground.Prelude where

open import Cubical.Foundations.Prelude as C hiding (_∙_)
  public
open import Cubical.Foundations.Function
  public

_∙_ : {ℓ : Level} → {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
_∙_ = C._∙_

-- _$_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
--   → (f : A → B)
--   → (a : A)
--   → B
-- f $ a = f a
-- {-# INLINE _$_ #-}

-- infixr 3 _$_

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
