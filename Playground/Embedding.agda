module Playground.Embedding where

open import Playground.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma

-- This is isEmbedding→hasPropFibers
isContrEmbSingleton : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → {f : A → B}
  → isEmbedding f
  → (b : B) → isProp (Σ[ a ∈ A ] b ≡ f a)
isContrEmbSingleton {A = A} {B = B} {f} emb-f b (a , p) (a' , q) = ΣPathP (a≡a' , {! !}) where
  r : f a ≡ f a'
  r = sym p ∙ q

  a≡a' : a ≡ a'
  a≡a' = isEmbedding→Inj emb-f a a' r

  -- isContrRetract {B = singl b} toSingl ofSingl {! !} (isContrSingl b) where
  -- toSingl : Σ[ a ∈ A ] b ≡ f a → singl b
  -- toSingl (a , p) = f a , p

  -- ofSingl : singl b → Σ[ a ∈ A ] b ≡ f a
  -- ofSingl (b' , p) = {! !} , {!  !}

