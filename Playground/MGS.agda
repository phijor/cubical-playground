module Playground.MGS where

open import Playground.Prelude

open import Cubical.Data.Nat.Base
open import Cubical.Data.Unit.Base
open import Cubical.Data.Sigma.Base
-- open import Cubical.Foundation.Equiv
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    Y : Type ℓ'

J' : (P : (x y : X) → (p : x ≡ y) → Type ℓ')
    → (d : {x : X} → P x x refl)
    → {x y : X} → (p : x ≡ y) → P x y p
J' P d {x} {y} p = {!transport !}

J* : ∀ {x : X}
  → (P : (y : X) → (p : x ≡ y) → Type ℓ')
  → (d : P x refl)
  → {y : X} → (p : x ≡ y) → P y p
J* {x = x} P d {y} p = transport q d where
  q : P x refl ≡ P y p
  q = λ { i → P (p i) (λ { j → p (φ i j) }) } where
    φ : (i j : I) → I
    φ i j = j ∧ i
    -- Task:
    -- Boundary:
    -- j = i0 ⊢ x
    -- j = i1 ⊢ p i
    --
    -- Find φ : (i j : I) → I such that
    -- φ i (j = i0) = x
    -- φ i (j = i1) = i

ap : (f : X → Y) → ∀ {x y} → x ≡ y → f x ≡ f y
ap f p = λ { i → f (p i) }

n-bdry : ℕ → Type → Type
n-disk : (n : ℕ) → (X : Type) → n-bdry n X → Type

n-bdry zero X = Unit
n-bdry (suc n) X = Σ[ b ∈ n-bdry n X ] n-disk n X b × n-disk n X b

n-disk zero X tt = X
n-disk (suc n) X (b , p , q) = p ≡ q

thm : ∀ n X → Iso (Σ[ b ∈ n-bdry n X ] n-disk n X b) X
thm zero X = {! !}
thm (suc n) X = {! !}

Boundary : ℕ → (X : Type ℓ) → Type ℓ
Disk : (n : ℕ) → (X : Type ℓ) → Boundary n X → Type ℓ

Boundary zero X = X × X
Boundary (suc n) X = Σ[ b ∈ Boundary n X ] Disk n X b × Disk n X b

Disk zero X (x , y) = x ≡ y
Disk (suc n) X (_ , α , β) = α ≡ β

Π^ : (n : ℕ) → (X : Type ℓ) → Type ℓ
Π^ zero X = X
Π^ (suc n) X = Σ (X × X) λ (x , y) → Π^ n (x ≡ y)

ap-bdry : {n : ℕ} → (f : X → Y) → Boundary n X → Boundary n Y
ap-disk : (n : ℕ) → (f : X → Y) → {b : Boundary n X} → Disk n X b → Disk n Y (ap-bdry f b)

ap-bdry {n = zero} f (x , y) = f x , f y
ap-bdry {n = suc n} f (b , α , β) = ap-bdry f b , ap-disk n f α , ap-disk n f β

ap-disk {X = X} zero f d = {! !}
ap-disk (suc n) f d = {! !}

-- ap^ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
--   → (f : X → Y)
--   → 

ap' : (f : X → Y)
  → ∀ {x y} → x ≡ y → f x ≡ f y
ap' f p = J' (λ x y (p : x ≡ y) → f x ≡ f y) refl p
