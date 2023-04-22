module Playground.SmallFin where

open import Playground.Prelude
open import Playground.Proposition

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
import Cubical.Foundations.Univalence.Universe as UU
open import Cubical.Foundations.Isomorphism

open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet
open import Cubical.Data.Nat.Base
open import Cubical.HITs.PropositionalTruncation as PT

data F : Type
El : F → Type

data F where
  fin : (n : ℕ) → F
  fun : ∀ x y → El x ≃ El y → x ≡ y

El (fin n) = Fin n
El (fun x y α i) = ua α i


module FU = UU F El fun (λ _ → refl)

-- rec : ∀ {ℓ} {A : Type ℓ}
--   → (fin* : (n : ℕ) → A)
--   → (fun* : (x y : F) → El x ≡ El y → {! !})
--   → F → A
-- rec fin* fun* (fin n) = fin* n
-- rec fin* fun* (fun x y α i) = {! fun x y α!}

isEmbeddingEl : isEmbedding El
isEmbeddingEl = FU.isEmbeddingEl

isFinSetEl : (x : F) → isFinSet (El x)
isFinSetEl (fin n) = isFinSetFin {n}
isFinSetEl (fun x y α i) = isProp→PathP (λ i → isPropIsFinSet {A = ua α i}) (isFinSetEl x) (isFinSetEl y) i

isPropIsSetEl : isOfHLevelDep 1 (λ (x : F) → isSet (El x))
isPropIsSetEl {x} {y} = isOfHLevel→isOfHLevelDep 1 (λ x → isPropIsSet) {x} {y}

isSetEl : ∀ x → isSet (El x)
isSetEl x = isFinSet→isSet (isFinSetEl x)

isGroupoidF : isGroupoid F
isGroupoidF x y = isOfHLevelRetractFromIso 2 ι sub where
  sub : isSet (El x ≡ El y)
  sub = isOfHLevel≡ 2 (isSetEl x) (isSetEl y)

  ι : Iso (x ≡ y) (El x ≡ El y)
  ι = FU.pathIso x y

F→FinSet : F → FinSet ℓ-zero
F→FinSet x = El x , isFinSetEl x

FinSet→F : FinSet ℓ-zero → F
FinSet→F (Y , n , ∣α∣) = fin n

F-FinSet-Iso : Iso F (FinSet ℓ-zero)
F-FinSet-Iso .Iso.fun = F→FinSet
F-FinSet-Iso .Iso.inv = FinSet→F
F-FinSet-Iso .Iso.rightInv (Y , n , ∣α∣) = rinv where
  rinv : (Fin n , isFinSetFin {n}) ≡ (Y , n , ∣α∣)
  rinv = PT.rec→Set (isGroupoidFinSet _ _) (λ α → Σ≡Prop (λ _ → isPropIsFinSet) (ua (invEquiv α))) (λ { α β i j → {! !} }) ∣α∣
F-FinSet-Iso .Iso.leftInv (fin n) = refl
F-FinSet-Iso .Iso.leftInv (fun x y α i) = {!fun !}
