{-# OPTIONS --lossy-unification #-}

module Playground.Combinatorics where

open import Playground.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩ ; str)
open import Cubical.Data.Nat as Nat hiding (_choose_)
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin as Fin
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Cubical.Structures.TypeEqvTo


private
  variable
    ℓA ℓB : Level

module _
  {A : Type ℓA}
  {B : Type ℓB}
  where

  hasDecFibers : (f : A → B) → Type (ℓ-max ℓA ℓB)
  hasDecFibers f = (b : B) → Dec $ fiber f b

  isPropHasDecFibers : {f : A → B} → hasPropFibers f → isProp (hasDecFibers f)
  isPropHasDecFibers propFib = isPropΠ λ b → isPropDec (propFib b)

  isEmbedding→isPropHasDecFibers : {f : A → B} → isEmbedding f → isProp (hasDecFibers f)
  isEmbedding→isPropHasDecFibers embF = isPropHasDecFibers (isEmbedding→hasPropFibers embF)

  isDecidableEmbedding : (f : A → B) → Type (ℓ-max ℓA ℓB)
  isDecidableEmbedding f = isEmbedding f × hasDecFibers f

  isPropIsDecidableEmbedding : {f : A → B} → isProp (isDecidableEmbedding f)
  isPropIsDecidableEmbedding = isPropΣ isPropIsEmbedding isEmbedding→isPropHasDecFibers

  isFinSetHasDecFibers : {f : A → B} → isEmbedding f → isFinSet B → isFinSet (hasDecFibers f)
  isFinSetHasDecFibers {f = f} emb-f finB = isFinSetΠ (_ , finB) λ b → Dec (fiber f b) , isDecProp→isFinSet (propDecFib b) (decDecFib b) where
    propDecFib : ∀ b → isProp (Dec (fiber f b))
    propDecFib b = isPropDec (isEmbedding→hasPropFibers emb-f b)

    decDecFib : ∀ b → Dec (Dec (fiber f b))
    decDecFib b = {! !}

Dec[_↪_] : (A : Type ℓA) (B : Type ℓB) → Type (ℓ-max ℓA ℓB)
Dec[ A ↪ B ] = Σ[ f ∈ (A → B) ] isDecidableEmbedding f

Choose : (A : Type ℓA) (B : Type ℓB) → Type (ℓ-max ℓA (ℓ-suc ℓB))
Choose {ℓB = ℓB} A B = Σ[ X ∈ TypeEqvTo ℓB B ] Dec[ ⟨ X ⟩ ↪ A ]

Permute : (A : Type ℓA) (B : Type ℓB) → Type (ℓ-max ℓA ℓB)
Permute A B = B ↪ A

isFinSetPermute : {A : Type ℓA} {B : Type ℓB}
  → isFinSet A
  → isFinSet B
  → isFinSet (Permute A B)
isFinSetPermute finA finB = isFinSet↪ (_ , finB) (_ , finA)

private
  [_] : (n : ℕ) → FinSet ℓ-zero
  [ n ] = Fin n , isFinSetFin

_permute_ : (n k : ℕ) → ℕ
n permute k = card (Permute (Fin n) (Fin k) , isFinSetPermuteFin) where
  isFinSetPermuteFin : isFinSet $ Permute (Fin n) (Fin k)
  isFinSetPermuteFin = isFinSetPermute (isFinSetFin {n}) (isFinSetFin {k})

abstract
  _ : 4 permute 2 ≡ 12
  _ = refl

permute-0 : ∀ n → n permute 0 ≡ 1
permute-0 n = refl

permute-rec : ∀ n k → (suc n) permute (suc k) ≡ (suc n) · (n permute k)
permute-rec n k = {! !}

permute-1 : ∀ n → n permute 1 ≡ n
permute-1 0 = refl
permute-1 (suc n) =
  (suc n permute 1) ≡⟨ ? ⟩
  {! permute-rec n 0 !} ∎

-- diag-⦅,⦆≡1 : ∀ n → ⦅ n , n ⦆ ≡ 1
-- diag-⦅,⦆≡1 zero = refl
-- diag-⦅,⦆≡1 (suc n) = {! !}
--
-- Permute : (A : Type ℓA) (B : Type ℓB) → Type (ℓ-max ℓA ℓB)
-- Permute A B = Dec[ B ↪ A ]

-- _del_ : (A : Type ℓA) {B : Type ℓB} (p : Permute A B) → Type _
-- A del p = {! !}

-- Permute⊎ : (A : Type ℓA) (B₁ B₂ : Type ℓB) → Permute A (B₁ ⊎ B₂) ≃ (Σ[ p ∈ Permute A B₁ ] {! !})
-- Permute⊎ A B₁ B₂ = {! !}

-- isFinSetPermute : (A : FinSet ℓA) (B : FinSet ℓB)
--   → isFinSet (Permute ⟨ A ⟩ ⟨ B ⟩)
-- isFinSetPermute A B =
--   isFinSetΣ
--     (_ , isFinSet→ B A)
--     λ f → _ , isFinSetΣ
--       ((isEmbedding _) , isFinSetIsEmbedding B A f)
--       λ emb-f → ((hasDecFibers _) , isFinSetHasDecFibers emb-f (str A))
