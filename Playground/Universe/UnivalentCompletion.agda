{-# OPTIONS --lossy-unification #-}

module Playground.Universe.UnivalentCompletion where

open import Playground.Prelude
open import Playground.Lift using (unlift ; congLift-unlift-section ; isEmbeddingLift)
open import Playground.Square

open import Playground.Universe.Base
open import Playground.Universe.Embedding

open import Playground.EquivToFamily using (module EquivToFamily)

open import Cubical.Data.Nat.Base
open import Cubical.Data.Sigma.Properties using (Σ≡Prop ; ΣPathP)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (invEq≡→equivFun≡)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua ; uaβ ; EquivContr ; EquivJ ; Glue ; ua-ungluePath)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Embedding using (isEmbedding ; hasPropFibersOfImage→isEmbedding ; hasPropFibers→isEmbedding)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

module Completion {ℓ} (V : Universe ℓ) where
  open EquivToFamily using (Connected ; Connected≡)

  open Universe

  U : Universe (ℓ-suc ℓ)
  U .Code = Connected (V .El)
  U .El = Lift ∘ ⟨_⟩

  uaU : (s t : U .Code) → U .El s ≃ U .El t → s ≡ t
  uaU s t α = Connected≡ (V .El) (unlift ⟨ s ⟩ ⟨ t ⟩ (ua α))

  uaU-β : (s t : U .Code) (α : U .El s ≃ U .El t) → cong (U .El) (uaU s t α) ≡ ua α
  uaU-β s t α = congLift-unlift-section {X = ⟨ s ⟩} {Y = ⟨ t ⟩} (ua α)

  open import Playground.Universe.Univalence using (isUnivalent ; module Univalence)

  isUnivalentCompletion : isUnivalent U
  isUnivalentCompletion = Univalence.hasUA→isUnivalent U uaU (λ {s} {t} → uaU-β s t)

  open Univalence U uaU (λ {s} {t} → uaU-β s t) public

  module _ (n : HLevel) (lvlEl : (a : V .Code) → isOfHLevel n (V .El a)) where
    isOfHLevelEl : (s : U .Code) → isOfHLevel n (U .El s)
    isOfHLevelEl = EquivToFamily.ConnectedElimProp (V .El) (λ _ → isPropIsOfHLevel n) isOfHLevelLiftEl where
      isOfHLevelLiftEl : (a : V .Code) → isOfHLevel n (Lift (V .El a))
      isOfHLevelLiftEl = isOfHLevelLift n ∘ lvlEl

    isOfHLevelElEquiv : {s t : U .Code} → isOfHLevel n (U .El s ≃ U .El t)
    isOfHLevelElEquiv {s} {t} = isOfHLevel≃ n (isOfHLevelEl s) (isOfHLevelEl t)

    isOfHLevelCompletionCodePath : (s t : U .Code) → isOfHLevel n (s ≡ t)
    isOfHLevelCompletionCodePath s t = isOfHLevelRespectEquiv n
      pathEquiv
      isOfHLevelElEquiv where

      pathEquiv : (U .El s ≃ U .El t) ≃ (s ≡ t)
      pathEquiv = invEquiv (minivalence {s} {t})

    isOfHLevelCompletionCode : isOfHLevel (suc n) (U .Code)
    isOfHLevelCompletionCode = isOfHLevelPath'⁻ n isOfHLevelCompletionCodePath

  embedding : V ↪ U
  embedding = ι , ι-embstr where
    ι : V .Code → Connected (V .El)
    ι s = V .El s , ∣ s , idEquiv _ ∣₁

    ι-embstr : UniverseEmbeddingStr V U ι
    ι-embstr .UniverseEmbeddingStr.is-emb = hasPropFibers→isEmbedding propImFib where
      propImFib' : ∀ (S : Connected (V .El)) → isProp (Σ[ s ∈  V .Code ] ι s ≡ S)
      propImFib' = EquivToFamily.ConnectedElimProp (V .El) (λ _ → isPropIsProp) goal where
        goal : (s : V .Code) → isProp (Σ[ t ∈ V .Code ] ι t ≡ ι s)
        goal s (t₀ , p₀) (t₁ , p₁)= ΣPathP ({! !} , {! !}) where
          code-path : V .El t₀ ≡ V .El t₁
          code-path = cong fst p₀ ∙ sym (cong fst p₁)

      propImFib : ∀ (S : Connected (V .El)) → isProp (Σ[ s ∈  V .Code ] ι s ≡ S)
      propImFib = uncurry λ X → PT.elim (λ _ → isPropIsProp) (uncurry goal) where
        module _ {X} (x : V .Code) (α : V .El x ≃ X) where
          goal : isProp (Σ[ s ∈ V .Code ] ι s ≡ (X , ∣ x , α ∣₁))
          goal (s₀ , p₀) (s₁ , p₁) = ΣPathP ({! !} , ΣSquarePProp (EquivToFamily.isPropIsConnectedTo (V .El)) {! !}) where
            lem : ∥ Path (singl x) ({! !} , {! !}) {! !} ∥₁
            lem = PT.map2 {! !} {!cong snd p₀ !} {! !}

    ι-embstr .UniverseEmbeddingStr.decode-equiv = goal where
      goal : (s : V .Code) → Lift ⟨ ι s ⟩ ≃ V .El s
      goal s = invEquiv (LiftEquiv {A = ⟨ ι s ⟩})

open Completion
  renaming (U to Completion)
  using (isUnivalentCompletion)
  public

module UniversalProperty where
  open import Playground.Universe.Univalence
  open import Playground.Universe.Embedding
  open import Playground.Proposition using (propImageElim ; propImageElim')

  open import Cubical.Functions.Image using (Image ; isPropIsInImage)
  open import Cubical.Functions.FunExtEquiv using (funExtDep)

  open Universe
  open UniverseEmbeddingStr

  extension : ∀ {ℓ ℓ′} (V : Universe ℓ)
    → {U : Universe ℓ′} → isUnivalent U
    → (ι : V ↪ U)
    → (Completion V .Code → U .Code)
  extension {ℓ} {ℓ′} V {U} uniU (f , f-emb) = uncurry λ (X : Type _) → propImageElim (P {X}) (propP {X}) f* (uncurry P[f]) where
    module _ {X : Type ℓ} where
      P : U .Code → Type (ℓ-max ℓ ℓ′)
      P s = U .El s ≃ X

      propP : isProp (Σ (U .Code) P)
      propP (s , α) (t , β) = ΣPathP (p , q) where
        δ : U .El s ≃ U .El t
        δ = α ∙ₑ invEquiv β

        p : s ≡ t
        p = uaU U uniU δ

        cong-p : cong (U .El) p ≡ ua δ
        cong-p = uaU-β U uniU (α ∙ₑ invEquiv β)

        equivFunPath : PathP (λ i → ua δ i → X) (equivFun α) (equivFun β)
        equivFunPath = funExtDep goal where
          module _ {Y : U .El s} {Z : U .El t} (Y≡Z : PathP (λ i → ua δ i) Y Z) where
            funPath : invEq β (equivFun α Y) ≡ Z
            funPath = ua-ungluePath δ Y≡Z

            goal : equivFun α Y ≡ equivFun β Z
            goal = sym (invEq≡→equivFun≡ β {a = Z} {b = equivFun α Y} funPath)

        equivPath : PathP (λ i → ua δ i ≃ X) α β
        equivPath = λ i → equivFunPath i , isProp→PathP (λ i → isPropIsEquiv (equivFunPath i)) (α .snd) (β .snd) i

        q : PathP (λ i → cong (U .El) p i ≃ X) α β
        q = subst (λ p' → PathP (λ i → p' i ≃ X) α β) (sym cong-p) equivPath

      f* : EquivToFamily.fiber≃ (V .El) X → U .Code
      f* (a , α) = f a

      P[f] : (a : V .Code) → (α : V .El a ≃ X) → P (f a)
      P[f] a α = f-emb .decode-equiv a ∙ₑ α

  module _ {ℓ ℓ′} {V : Universe ℓ} {U : Universe ℓ′} {uniU : isUnivalent U} {ι : V ↪ U} where
    private
      ext : Completion V .Code → U .Code
      ext = extension V uniU ι

    isEmbeddingExtension : isEmbedding (extension V uniU ι)
    isEmbeddingExtension = hasPropFibersOfImage→isEmbedding goal where
      lemma : ∀ (x : V .Code) → isProp (Σ[ y ∈ EquivToFamily.Connected (V .El) ] ext y ≡ ι .fst x)
      lemma x (y₀ , p₀) (y₁ , p₁) = ΣPathP (p , λ i → {! !}) where
        p : y₀ ≡ y₁
        p = EquivToFamily.Connected≡ (V .El) {! p₀!}

      goal : ∀ (Y : EquivToFamily.Connected (V .El)) → isProp (fiber ext (ext Y))
      goal = EquivToFamily.ConnectedElimProp (V .El) (λ _ → isPropIsProp) lemma

    universeEmbeddingStrExtension : UniverseEmbeddingStr (Completion V) U (extension V uniU ι)
    universeEmbeddingStrExtension .is-emb = isEmbeddingExtension
    universeEmbeddingStrExtension .decode-equiv (Y , ∣α∣) = goal where
      goal : U .El (extension V uniU ι (Y , _)) ≃ Lift Y
      goal = {! !}

  isMinimal : ∀ {ℓ}
    → (V : Universe ℓ)
    → (U : Universe (ℓ-suc ℓ))
    → isUnivalent U
    → (ι : V ↪ U)
    → Completion V ↪ U
  isMinimal V U uniU ι = extension V uniU ι , universeEmbeddingStrExtension {V = V}

