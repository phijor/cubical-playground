module Playground.Analytic.Properties where

open import Playground.Prelude
open import Playground.Proposition using (propImageElim' ; propImageElim)

open import Playground.Analytic.Base

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Reflection.RecordEquiv using (declareRecordIsoΣ)

open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)
open import Cubical.Relation.Binary.Base using (module BinaryRelation ; Rel)
open import Cubical.Functions.Image as Image using (Image)


private
  variable
    ℓ ℓX : Level
    C : Container ℓ
    X : Type ℓX

unquoteDecl AnalyticIsoΣ = declareRecordIsoΣ AnalyticIsoΣ (quote Analytic)

isSetAnalyticΣ : isSet (AnalyticΣ C X)
isSetAnalyticΣ {C = C} = isSetΣ isSetShape λ shape → SQ.squash/ where
  open Container C

isSetAnalytic : isSet (Analytic C X)
isSetAnalytic {C = C} = isOfHLevelRetractFromIso 2 AnalyticIsoΣ (isSetAnalyticΣ {C = C})

SetTruncIdempotentIso : Iso ∥ Analytic C X ∥₂ (Analytic C X)
SetTruncIdempotentIso = ST.setTruncIdempotentIso isSetAnalytic

hasInjectivePos : Container ℓ → Type _
hasInjectivePos C = (s t : Shape) → Pos s ≡ Pos t → s ≡ t where
  open Container C

hasAllSymmetries : Container ℓ → Type _
hasAllSymmetries C =  ∀ {s} σ → isContr (Symm {s} σ) where
  open Container C

module _ (C : Container ℓ) {s : C .Container.Shape} (X : Type ℓ) where
  open Container C hiding (_∼_)

  private
    _∼_ : Rel (Pos s → X) (Pos s → X) ℓ
    _∼_ = Container._∼_ C {s = s} {X = X}

  open BinaryRelation using (isRefl ; isSym ; isTrans ; isEquivRel ; isEffective ; isPropValued)
  open isEquivRel using (reflexive ; symmetric ; transitive)

  isRefl-∼ : isRefl _∼_
  isRefl-∼ u = ∣ idEquiv (Pos s) , reflSymm s , refl {x = u} ∣₁

  isSym-∼ : isSym _∼_
  isSym-∼ u v = PT.map goal where
    module _ ((σ , σ-has-P , u≡v∘σ) : Σ[ σ ∈ Pos s ≃ Pos s ] Symm σ × (u ≡ v ∘ equivFun σ)) where
      σ⁺ : _ → _
      σ⁺ = equivFun σ

      σ⁻ : _ → _
      σ⁻ = invEq σ

      v≡u∘σ : v ≡ u ∘ σ⁻
      v≡u∘σ = funExt λ pos →
        v pos           ≡⟨ cong v (sym $ secEq σ pos) ⟩
        v (σ⁺ $ σ⁻ pos) ≡⟨ funExt⁻ (sym u≡v∘σ) $ σ⁻ pos ⟩∎
        u (σ⁻ pos) ∎

      goal : v ∼∞ u
      goal = invEquiv σ , invSymm σ-has-P , v≡u∘σ


  isEquivRel-∼ : isEquivRel _∼_
  isEquivRel-∼ .reflexive = isRefl-∼
  isEquivRel-∼ .symmetric = isSym-∼
  isEquivRel-∼ .transitive = {! !}

  isPropValued-∼ : isPropValued _∼_
  isPropValued-∼ u v = PT.isPropPropTrunc

  isEffective-∼ : isEffective _∼_
  isEffective-∼ = SQ.isEquivRel→isEffective isPropValued-∼ isEquivRel-∼

module Fibered {ℓ} (C : Container ℓ) where
  open Container C

  FiberedLabel : (X : Type ℓ) → (shape : Shape) → Type (ℓ-suc ℓ)
  FiberedLabel X shape = ∥ Σ[ P ∈ Type ℓ ] ∥ Pos shape ≃ P ∥₁ × (P → X) ∥₂

  module _ {X : Type ℓ} {shape : Shape} where
    FiberedLabel→Label : FiberedLabel X shape → ((Pos shape → X) / _∼_)
    FiberedLabel→Label = ST.rec SQ.squash/ λ { (P , ∣Pos≃P∣ , label) → label∼ P ∣Pos≃P∣ label } where
      module _ (P : Type ℓ) where
        label∞ : (α : Pos shape ≃ P) (label : P → X) → (Pos shape → X) / _∼_
        label∞ α label = SQ.[ label ∘ equivFun α ]

        isPropImage-label∞ : isProp (Image label∞)
        isPropImage-label∞ (f , f∈im) (g , g∈im) = Σ≡Prop (Image.isPropIsInImage _)
          (funExt λ u → {! !})

        label∼ : (pos-equiv : ∥ Pos shape ≃ P ∥₁) (label : P → X) → (Pos shape → X) / _∼_
        label∼ = propImageElim {! !} {! !} label∞ {! !} -- PT.elim {! !} {! !}


    FiberedLabelIso : Iso (FiberedLabel X shape) ((Pos shape → X) / _∼_)
    FiberedLabelIso = go where
      go : Iso _ _
      go .Iso.fun = {! !}
      go .Iso.inv = {! !}
      go .Iso.rightInv = {! !}
      go .Iso.leftInv = {! !}

  FiberedAnalytic : (X : Type ℓ) → Type (ℓ-suc ℓ)
  FiberedAnalytic X = Σ Shape (FiberedLabel X)
