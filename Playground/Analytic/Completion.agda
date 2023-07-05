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
open import Cubical.Foundations.Structure using (⟨_⟩ ; str)
open import Cubical.Functions.Embedding using (injEmbedding)

module _ {ℓ} (C : Container ℓ) where
  open Container C using (Shape ; Pos ; Symm ; isSetShape ; isSetPos ; _∼_)
  open Universe using (Code ; El)

  open EquivToFamily Pos using (Connected ; FiberConnected ; FiberConnected≡ ; module InjFam)

  U : Universe ℓ
  U .Code = Shape
  U .El = Pos

  module UU = Completion U

  GroupoidContainer : Universe (ℓ-suc ℓ)
  GroupoidContainer = UU.U

  Poly : (X : Type (ℓ-suc ℓ)) → Type (ℓ-suc ℓ)
  Poly X = Σ[ a ∈ GroupoidContainer .Code ] ((GroupoidContainer .El a) → X)

  isOfHLevelPoly : ∀ {X} (n : HLevel) → isOfHLevel (3 + n) X → isOfHLevel (3 + n) (Poly X)
  isOfHLevelPoly {X = X} n ofLvlX =
    isOfHLevelΣ (3 + n)
      (UU.isOfHLevelCompletionCode (2 + n) isOfHLevelEl)
      isOfHLevelLabel where

    isSetEl : (a : U .Code) → isSet (U .El a)
    isSetEl = isSetPos

    isOfHLevelEl : (a : U .Code) → isOfHLevel (2 + n) (U .El a)
    isOfHLevelEl a = isOfHLevelPlus' 2 (isSetEl a)

    isOfHLevelLabel : (s : GroupoidContainer .Code) → isOfHLevel (3 + n) (GroupoidContainer .El s → X)
    isOfHLevelLabel _ = isOfHLevelΠ (3 + n) λ _ → ofLvlX

  isGroupoidPoly : ∀ {X} → isGroupoid X → isGroupoid (Poly X)
  isGroupoidPoly = isOfHLevelPoly 0

  -- Assuing `C` has an injective family of positions, we can extract
  -- shapes of `C` for all codes in the derived `GroupoidContainer`.
  --
  -- We do this by using the equivalence of types
  --
  --  Σ (Type _) Σ Shape _ ≃ FiberConnected ≃ Connected ≃ GroupoidContainer .Code
  --
  -- when `Pos` is injective.
  _ : FiberConnected ≡ Σ (Type ℓ) λ X → Σ (C .Container.Shape) _
  _ = refl

  _ : Connected ≡ GroupoidContainer .Code
  _ = refl

  GroupoidContainerCodeEquiv : (injEl : hasInjectivePos C) → (FiberConnected ≃ GroupoidContainer .Code)
  GroupoidContainerCodeEquiv = InjFam.FiberConnected≃Connected isSetShape


  {- Under the assumption that the container C (1) does not restrict the
  -- type of symmetries of its positions, and assuming (2) that the family
  -- of positions is injective, show the following:
  --
  -- The set-truncation of the associate polynomial functors in groupoids
  -- (`Poly`) is equivalent to its type of associated analytic functors.
  --
  -- (1) is necessary because `PolyContainer` currently selects the wrong
  --      groupoid of shapes; we need to restrict its shapes to a subgroupoid
  --      as given by `Symm`.
  -- (2) is necessary to conclude that for any shape in `PolyContainer`,
  --      one can extract from which shape in `Container` it originated.
  --      See `GroupoidContainerCodeEquiv`.
  -}
  module ContrSymm
    (allSymmetries : hasAllSymmetries C)
    (injPos : hasInjectivePos C)
    where

    open import Cubical.Foundations.Univalence using (ua ; ua→)
    open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
    open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
    open import Cubical.HITs.SetQuotients as SQ using (_/_)

    private
      variable
        ℓX : Level

    Poly∞ : Type ℓX → Type (ℓ-max (ℓ-suc ℓ) ℓX)
    Poly∞ X = Σ[ (P , conn) ∈ FiberConnected ] (P → X)

    Poly∞≡ : {X : Type ℓX} {x y : Poly∞ X}
      → (shape-path : Path Shape (str (x .fst) .fst) (str (y .fst) .fst))
      → (pos-path : Path (Type _) ⟨ x .fst ⟩ ⟨ y .fst ⟩)
      → (label-path : PathP (λ i → pos-path i → X) (x .snd) (y .snd))
      → x ≡ y
    Poly∞≡ shape-path pos-path label-path = ΣPathP (FiberConnected≡ pos-path shape-path , label-path)

    ShapeEquiv→Poly∞≡ : {X : Type ℓX} {x y : Poly∞ X}
      → (shape-path : Path Shape (str (x .fst) .fst) (str (y .fst) .fst))
      → (shape-equiv : ⟨ x .fst ⟩ ≃ ⟨ y .fst ⟩)
      → (label-path : (pos : ⟨ x .fst ⟩) → x .snd pos ≡ y .snd (equivFun shape-equiv pos))
      → x ≡ y
    ShapeEquiv→Poly∞≡ shape-path shape-equiv label-path = Poly∞≡ shape-path (ua shape-equiv) (ua→ label-path)

    _≈_ : {s : Shape} {X : Type ℓX} → (u v : Pos s → X) → Type _
    _≈_ {s = s} u v = ∃[ σ ∈ (Pos s ≃ Pos s) ] u ≡ v ∘ equivFun σ

    Analytic≈ : (X : Type ℓX) → Type (ℓ-max ℓ ℓX)
    Analytic≈ X = Σ[ shape ∈ Shape ] (Pos shape → X) / _≈_

    LabelRelIso : {X : Type ℓX} (s : Shape) → Iso ((Pos s → X) / _∼_) ((Pos s → X) / _≈_)
    LabelRelIso s = SQ.relBiimpl→TruncIso
      (PT.map (λ a∼b → a∼b .fst , a∼b .snd .snd))
      (PT.map (λ a≈b → a≈b .fst , allSymmetries _ .fst , a≈b .snd))

    AnalyticIsoAnalytic≈ : {X : Type ℓX} → Iso (Analytic C X) (Analytic≈ X)
    AnalyticIsoAnalytic≈ = compIso AnalyticIsoΣ (Σ-cong-iso-snd LabelRelIso)

    isSetAnalytic≈ : {X : Type ℓX} → isSet (Analytic≈ X)
    isSetAnalytic≈ = isOfHLevelRetractFromIso 2 (invIso AnalyticIsoAnalytic≈) isSetAnalytic

    module _ (X : Type ℓ) where
      Poly∞IsoPoly : Iso (Poly∞ X) (Poly (Lift X))
      Poly∞IsoPoly =
        Poly∞ X                                             Iso⟨ Σ-cong-iso-snd (λ _ → equiv→Iso LiftEquiv LiftEquiv) ⟩
        Σ[ (P , conn) ∈ FiberConnected ] (Lift P → Lift X)  Iso⟨ Σ-cong-iso-fst $ (equivToIso $ GroupoidContainerCodeEquiv injPos) ⟩
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

    SetTruncPoly∞IsoAnalytic≈ : ∀ {X : Type ℓ} → Iso ∥ Poly∞ X ∥₂ (Analytic≈ X)
    SetTruncPoly∞IsoAnalytic≈ .Iso.fun = ∥Poly∞∥₂→Analytic≈ _
    SetTruncPoly∞IsoAnalytic≈ .Iso.inv = Analytic≈→∥Poly∞∥₂ _
    SetTruncPoly∞IsoAnalytic≈ {X = X} .Iso.rightInv = rinv where
      rinv : (x : Analytic≈ X) → ∥Poly∞∥₂→Analytic≈ _ (Analytic≈→∥Poly∞∥₂ _ x) ≡ x
      rinv = uncurry λ shape → SQ.elimProp (λ _ → isSetAnalytic≈ _ _) λ label → refl {x = (shape , SQ.[ label ])}
    SetTruncPoly∞IsoAnalytic≈ {X = X} .Iso.leftInv = linv where

      roundtrip : ∥ Poly∞ X ∥₂ → ∥ Poly∞ X ∥₂
      roundtrip = Analytic≈→∥Poly∞∥₂ _ ∘ ∥Poly∞∥₂→Analytic≈ _

      module _ (P : Type _) (shape : Shape) (α : Pos shape ≃ P) (label : P → X) where
        x : Poly∞ X
        x = (P , shape , PT.∣ α ∣₁) , label

        shape-loop : shape ≡ shape
        shape-loop = refl

        label-path : (pos : Pos shape) → label (equivFun α pos) ≡ label (equivFun α pos)
        label-path _ = refl

        goal : roundtrip ST.∣ x ∣₂ ≡ ST.∣ x ∣₂
        goal = cong ST.∣_∣₂ (ShapeEquiv→Poly∞≡ shape-loop α label-path)

      lemma : (x : Poly∞ X) → Analytic≈→∥Poly∞∥₂ _ (Poly∞→Analytic≈ _ x) ≡ ST.∣ x ∣₂
      lemma = uncurry
        λ { (P , shape , ∣Pos≃∣)
          → PT.elim
            {P = λ ∣Pos≃∣ → (label : P → X) → let x = ST.∣ (P , shape , ∣Pos≃∣) , label ∣₂ in roundtrip x ≡ x}
            (λ ∣Pos≃∣ → isPropΠ λ _ → ST.isSetSetTrunc _ _)
            (goal P shape)
            ∣Pos≃∣
          }

      linv : (x : ∥ Poly∞ X ∥₂) → roundtrip x ≡ x
      linv = ST.elim (λ _ → ST.isSetPathImplicit) lemma

    SetTruncPolyIsoAnalytic : (X : Type ℓ) → Iso ∥ Poly (Lift X) ∥₂ (Analytic C X)
    SetTruncPolyIsoAnalytic X =
      ∥ Poly (Lift X) ∥₂  Iso⟨ ST.setTruncIso $ invIso (Poly∞IsoPoly X) ⟩
      ∥ Poly∞ X ∥₂        Iso⟨ SetTruncPoly∞IsoAnalytic≈ ⟩
      Analytic≈ X         Iso⟨ invIso AnalyticIsoAnalytic≈ ⟩
      Analytic C X        Iso∎

    SetTruncPolyEquivAnalytic : ∀ X → ∥ Poly (Lift X) ∥₂ ≃ Analytic C X
    SetTruncPolyEquivAnalytic = isoToEquiv ∘ SetTruncPolyIsoAnalytic
