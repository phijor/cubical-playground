module Playground.PosRat where

open import Playground.Prelude

open import Cubical.Data.Unit.Base using (Unit)
open import Cubical.Data.Empty.Base using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat as Nat hiding (_+_ ; _·_)
open import Cubical.Data.NatPlusOne using (ℕ₊₁)
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming (_/_ to _/₂_)
open import Cubical.HITs.Rationals.QuoQ as Q using (ℚ)

open import Cubical.Data.Nat.Literals public

-- module Old where
--   record ℕ⁺ : Type where
--     field
--       nat : ℕ
--       pos : ¬ (nat ≡ 0)

--   open ℕ⁺

--   suc⁺ : ℕ → ℕ⁺
--   suc⁺ n .nat = suc n
--   suc⁺ n .pos = snotz

--   instance
--     fromNatℕ⁺ : HasFromNat ℕ⁺
--     fromNatℕ⁺ .HasFromNat.Constraint zero = ⊥
--     fromNatℕ⁺ .HasFromNat.Constraint (suc n) = Unit
--     fromNatℕ⁺ .HasFromNat.fromNat (suc n) = suc⁺ n

--   _·₊_ : ℕ⁺ → ℕ⁺ → ℕ⁺
--   (m ·₊ n) .nat = m .nat Nat.· n .nat
--   (m ·₊ n) .pos = Nat.integral-domain-· (m .pos) (n .pos)

--   data ℚ⁺ : Type where
--     _/_ : (a b : ℕ⁺) → ℚ⁺
--     path : ∀ a b c d → a ·₊ d ≡ c ·₊ b → a / b ≡ c / d
--     isSetℚ⁺ : isSet ℚ⁺

--   module _ {ℓ} (A : Type ℓ) where
--     record ℚRec : Type ℓ where
--       field
--         _/*_ : (p q : ℕ⁺) → A
--         path* : ∀ a b c d → a ·₊ d ≡ c ·₊ b → a /* b ≡ c /* d
--         isSet* : isSet A

--       rec : ℚ⁺ → A
--       rec (p / q) = p /* q
--       rec (path a b c d a·c≡b·d i) = path* a b c d a·c≡b·d i
--       rec (isSetℚ⁺ q₁ q₂ pth₁ pth₂ i j) = isSet* (rec q₁) (rec q₂) (cong rec pth₁) (cong rec pth₂) i j

--     open ℚRec using (rec) public


--   instance
--     fromNatℚ⁺ : HasFromNat ℚ⁺
--     fromNatℚ⁺ .HasFromNat.Constraint zero = ⊥
--     fromNatℚ⁺ .HasFromNat.Constraint (suc n) = Unit
--     fromNatℚ⁺ .HasFromNat.fromNat (suc n) = suc⁺ n / 1

--   infixl 6 _+_
--   _+_ : ℚ⁺ → ℚ⁺ → ℚ⁺
--   _+_ = {! !}

--   infixl 7 _·_
--   _·_ : ℚ⁺ → ℚ⁺ → ℚ⁺
--   _·_ = {! !}
--     -- rec go where
--     -- module _ (a b : ℕ⁺) where
--     --   goʳ : ℚRec ℚ⁺
--     --   goʳ .ℚRec._/*_ c d = (a ·₊ c) / (b ·₊ d)
--     --   goʳ .ℚRec.path* = {! !}
--     --   goʳ .ℚRec.isSet* = isSetℚ⁺

--     --   [_,_]·_ : ℚ⁺ → ℚ⁺
--     --   [_,_]·_ = {! !}

--     -- go : ℚRec (ℚ⁺ → ℚ⁺)
--     -- go .ℚRec._/*_ = [_,_]·_
--     -- go .ℚRec.path* = {! !}
--     -- go .ℚRec.isSet* = isSet→ isSetℚ⁺

--   -- _/2 : ℚ⁺ → ℚ⁺
--   -- _/2 = _· (1 / 2)

--   -- _<_ : ℚ⁺ → ℚ⁺ → Type
--   -- _<_ = {! !}

data IsPos : ℚ → Type where
  ispos : (p q : ℕ₊₁) → IsPos Q.[ Q.ℕ₊₁→ℤ p / q ]

ℚ⁺ : Type
ℚ⁺ = Σ ℚ IsPos

infixl 6 _+_
_+_ : ℚ⁺ → ℚ⁺ → ℚ⁺
_+_ = {! !}

infixl 7 _·_
_·_ : ℚ⁺ → ℚ⁺ → ℚ⁺
_·_ = {! !}

_/2 : ℚ⁺ → ℚ⁺
_/2 = ? -- _· (1 / 2)

_<_ : ℚ⁺ → ℚ⁺ → Type
_<_ = {! !}
