module Playground.LevelModality where

open import Playground.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Modalities.Modality
open import Cubical.HITs.Truncation as TT using (∥_∥_ ; ∣_∣ₕ)

private
  variable
    ℓ : Level

module _ (k : HLevel) where
  ofLevel : Modality ℓ
  ofLevel .Modality.isModal = isOfHLevel k
  ofLevel .Modality.isPropIsModal = isPropIsOfHLevel k
  ofLevel .Modality.◯ = ∥_∥ k
  ofLevel .Modality.◯-isModal = TT.isOfHLevelTrunc k
  ofLevel .Modality.η = ∣_∣ₕ
  ofLevel .Modality.◯-elim = TT.elim
  ofLevel .Modality.◯-elim-β isOfLevel = {! TT.elimₕ k {hB =  !}
  ofLevel .Modality.◯-=-isModal = {! !}
