module Playground.Analytic.Completion where

open import Playground.Prelude
open import Playground.EquivToFamily using (module EquivToFamily)
open import Playground.Analytic.Base
open import Playground.Analytic.Properties
open import Playground.Universe.Base
open import Playground.Universe.UnivalentCompletion
  using (module Completion)

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (_∎Iso to _Iso∎)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Embedding using (injEmbedding)

module _ {ℓ} (C : Container ℓ) where
  open Container C using (Shape ; Pos ; Symm ; isSetShape ; isSetPos ; _∼_)
  open Universe using (Code ; El)

  U : Universe ℓ
  U .Code = Shape
  U .El = Pos

  module UU = Completion U

  U˘ : Universe (ℓ-suc ℓ)
  U˘ = UU.U

  U˘CodeEquiv : (injEl : hasInjectivePos C) → (EquivToFamily.FiberConnected (U .El) ≃ U˘ .Code)
  U˘CodeEquiv = EquivToFamily.InjFam.FiberConnected≃Connected (U .El) isSetShape

  Poly : (X : Type (ℓ-suc ℓ)) → Type (ℓ-suc ℓ)
  Poly X = Σ[ a ∈ U˘ .Code ] ((U˘ .El a) → X)

  isOfHLevelPoly : ∀ {X} (n : HLevel) → isOfHLevel (3 + n) X → isOfHLevel (3 + n) (Poly X)
  isOfHLevelPoly {X = X} n ofLvlX =
    isOfHLevelΣ (3 + n)
      (UU.isOfHLevelCompletionCode (2 + n) isOfHLevelEl)
      isOfHLevelLabel where

    isSetEl : (a : U .Code) → isSet (U .El a)
    isSetEl = isSetPos

    isOfHLevelEl : (a : U .Code) → isOfHLevel (2 + n) (U .El a)
    isOfHLevelEl a = isOfHLevelPlus' 2 (isSetEl a)

    isOfHLevelLabel : (s : U˘ .Code) → isOfHLevel (3 + n) (U˘ .El s → X)
    isOfHLevelLabel _ = isOfHLevelΠ (3 + n) λ _ → ofLvlX

  isGroupoidPoly : ∀ {X} → isGroupoid X → isGroupoid (Poly X)
  isGroupoidPoly = isOfHLevelPoly 0

  module ContrSymm
    (contrSymm : ∀ {s} σ → isContr (Symm {s} σ))
    (injPos : hasInjectivePos C)
    where

    open import Cubical.Foundations.Univalence using (ua ; ua→)
    open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
    open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
    open import Cubical.HITs.SetQuotients as SQ using (_/_)

    open EquivToFamily Pos using (FiberConnected ; isConnectedInFiber ; isConnectedTo)

    private
      variable
        ℓX : Level

    Poly∞ : Type ℓX → Type (ℓ-max (ℓ-suc ℓ) ℓX)
    Poly∞ X = Σ[ (P , conn) ∈ FiberConnected ] (P → X)

    _≈_ : {s : Shape} {X : Type ℓX} → (u v : Pos s → X) → Type _
    _≈_ {s = s} u v = ∃[ σ ∈ (Pos s ≃ Pos s) ] u ≡ v ∘ equivFun σ

    Analytic≈ : (X : Type ℓX) → Type (ℓ-max ℓ ℓX)
    Analytic≈ X = Σ[ shape ∈ Shape ] (Pos shape → X) / _≈_

    LabelRelIso : {X : Type ℓX} (s : Shape) → Iso ((Pos s → X) / _∼_) ((Pos s → X) / _≈_)
    LabelRelIso s = SQ.relBiimpl→TruncIso
      (PT.map (λ a∼b → a∼b .fst , a∼b .snd .snd))
      (PT.map (λ a≈b → a≈b .fst , contrSymm _ .fst , a≈b .snd))

    AnalyticIsoAnalytic≈ : {X : Type ℓX} → Iso (Analytic C X) (Analytic≈ X)
    AnalyticIsoAnalytic≈ = compIso AnalyticIsoΣ (Σ-cong-iso-snd LabelRelIso)

    isSetAnalytic≈ : {X : Type ℓX} → isSet (Analytic≈ X)
    isSetAnalytic≈ = isOfHLevelRetractFromIso 2 (invIso AnalyticIsoAnalytic≈) isSetAnalytic

    module _ (X : Type ℓ) where
      Poly∞IsoPoly : Iso (Poly∞ X) (Poly (Lift X))
      Poly∞IsoPoly =
        Poly∞ X                                             Iso⟨ Σ-cong-iso-snd (λ _ → equiv→Iso LiftEquiv LiftEquiv) ⟩
        Σ[ (P , conn) ∈ FiberConnected ] (Lift P → Lift X)  Iso⟨ Σ-cong-iso-fst $ (equivToIso $ U˘CodeEquiv injPos) ⟩
        Poly (Lift X) Iso∎

    module _ (X : Type ℓ) where
      Poly∞→Analytic≈ : Poly∞ X → Analytic≈ X
      Poly∞→Analytic≈ ((P , shape , isConnY) , label) = shape , label' where
        from-equiv : Pos shape ≃ P → (Pos shape → X) / _≈_
        from-equiv α = SQ.[ label ∘ equivFun α ]

        is2Const : (α β : Pos shape ≃ P) → from-equiv α ≡ from-equiv β
        is2Const α β = SQ.eq/ {R = _≈_} _ _ rel where
          α⁺ = equivFun α
          β⁺ = equivFun β
          α⁻ = invEq α
          β⁻ = invEq β

          σ : Pos shape ≃ Pos shape
          σ = α ∙ₑ invEquiv β

          σ-rel : label ∘ α⁺ ≡ label ∘ β⁺ ∘ β⁻ ∘ α⁺
          σ-rel = cong (λ — → label ∘ — ∘ α⁺) (sym $ funExt (secEq β))

          rel : (label ∘ α⁺) ≈ (label ∘ β⁺)
          rel = PT.∣ σ , σ-rel ∣₁

        label' : (Pos shape → X) / _≈_
        label' = PT.rec→Set SQ.squash/ from-equiv is2Const isConnY

      ∥Poly∞∥₂→Analytic≈ : ∥ Poly∞ X ∥₂ → Analytic≈ X
      ∥Poly∞∥₂→Analytic≈ = ST.rec isSetAnalytic≈ Poly∞→Analytic≈

      Analytic≈→∥Poly∞∥₂ : Analytic≈ X → ∥ Poly∞ X ∥₂
      Analytic≈→∥Poly∞∥₂ = uncurry goal where
        module _ (shape : Shape) where
          connPos : FiberConnected
          connPos = Pos shape , shape , PT.∣ idEquiv _ ∣₁

          connPosLoop : Pos shape ≃ Pos shape → connPos ≡ connPos
          connPosLoop σ = ΣPathP (ua σ , ΣPathP (refl {x = shape} , isProp→PathP (λ i → PT.isPropPropTrunc) _ _))

          labelPath : {l₁ l₂ : Pos shape → X}
            → {σ : Pos shape ≃ Pos shape}
            → (l₁ ≡ l₂ ∘ equivFun σ)
            → PathP (λ i → ⟨ connPosLoop σ i ⟩ → X) l₁ l₂
          labelPath σ-rel = ua→ (funExt⁻ σ-rel)

          from-label : (Pos shape → X) → ∥ Poly∞ X ∥₂
          from-label label = ST.∣ connPos , label ∣₂

          well-defined : (l₁ l₂ : Pos shape → X) → l₁ ≈ l₂ → from-label l₁ ≡ from-label l₂
          well-defined l₁ l₂ = PT.elim
            (λ _ → ST.isSetSetTrunc _ _)
            λ { (σ , σ-rel) → cong ST.∣_∣₂ (ΣPathP (connPosLoop σ , labelPath σ-rel)) }

          goal : (Pos shape → X) / _≈_ → ∥ Poly∞ X ∥₂
          goal = SQ.rec ST.isSetSetTrunc from-label well-defined

      rinv : (x : Analytic≈ X) → ∥Poly∞∥₂→Analytic≈ (Analytic≈→∥Poly∞∥₂ x) ≡ x
      rinv = uncurry λ shape → SQ.elimProp (λ _ → isSetAnalytic≈ _ _) λ label → refl {x = (shape , SQ.[ label ])}

    SetTruncPoly∞IsoAnalytic≈ : ∀ {X : Type ℓ} → Iso ∥ Poly∞ X ∥₂ (Analytic≈ X)
    SetTruncPoly∞IsoAnalytic≈ .Iso.fun = ∥Poly∞∥₂→Analytic≈ _
    SetTruncPoly∞IsoAnalytic≈ .Iso.inv = Analytic≈→∥Poly∞∥₂ _
    SetTruncPoly∞IsoAnalytic≈ .Iso.rightInv = rinv _
    SetTruncPoly∞IsoAnalytic≈ .Iso.leftInv = {! !}

    SetTruncPolyIsoAnalytic : (X : Type ℓ) → Iso ∥ Poly (Lift X) ∥₂ (Analytic C X)
    SetTruncPolyIsoAnalytic X =
      ∥ Poly (Lift X) ∥₂  Iso⟨ ST.setTruncIso $ invIso (Poly∞IsoPoly X) ⟩
      ∥ Poly∞ X ∥₂        Iso⟨ SetTruncPoly∞IsoAnalytic≈ ⟩
      Analytic≈ X         Iso⟨ invIso AnalyticIsoAnalytic≈ ⟩
      Analytic C X        Iso∎

    SetTruncPolyEquivAnalytic : ∀ X → ∥ Poly (Lift X) ∥₂ ≃ Analytic C X
    SetTruncPolyEquivAnalytic = isoToEquiv ∘ SetTruncPolyIsoAnalytic
