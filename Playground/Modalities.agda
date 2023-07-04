module Playground.Modalities where

open import Playground.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Modalities.Modality
open import Cubical.Relation.Nullary.Base using (Discrete)

FinSetModality : Modality ℓ-zero
FinSetModality .Modality.isModal = isFinSet
FinSetModality .Modality.isPropIsModal = isPropIsFinSet
FinSetModality .Modality.◯ = {! !}
FinSetModality .Modality.◯-isModal = {! !}
FinSetModality .Modality.η = {! !}
FinSetModality .Modality.◯-elim = {! !}
FinSetModality .Modality.◯-elim-β = {! !}
FinSetModality .Modality.◯-=-isModal = {! !}
