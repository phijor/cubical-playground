module Playground.Universe.Embedding where

open import Playground.Prelude
open import Playground.Universe.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding hiding (_↪_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Reflection.RecordEquiv

open Universe

-- XXX: Should decode-equiv be truncated?
-- Then UniverseEmbeddingStr would be a proposition.
-- If not, what is the SIP for this structure?

record UniverseEmbeddingStr
  {ℓU ℓV} (V : Universe ℓV) (U : Universe ℓU) (f : V .Code → U .Code)
  : Type (ℓ-max ℓV ℓU) where
  no-eta-equality
  field
    is-emb : isEmbedding f
    decode-equiv : ∀ (A : V .Code) → U .El (f A) ≃ V .El A

unquoteDecl UniverseEmbeddingStrIsoΣ = declareRecordIsoΣ UniverseEmbeddingStrIsoΣ (quote UniverseEmbeddingStr)

open UniverseEmbeddingStr

universeEmbeddingStrId : ∀ {ℓ} {U : Universe ℓ} → UniverseEmbeddingStr U U (idfun (U .Code))
universeEmbeddingStrId .is-emb = λ s t → idIsEquiv (s ≡ t)
universeEmbeddingStrId .decode-equiv = λ s → idEquiv _

universeEmbeddingStrComp : ∀ {ℓU ℓV ℓW}
  → {U : Universe ℓU}
  → {V : Universe ℓV}
  → {W : Universe ℓW}
  → {f : U .Code → V .Code}
  → {g : V .Code → W .Code}
  → UniverseEmbeddingStr U V f
  → UniverseEmbeddingStr V W g
  → UniverseEmbeddingStr U W (g ∘ f)
universeEmbeddingStrComp emb-f emb-g .is-emb = isEmbedding-∘ (emb-g .is-emb) (emb-f .is-emb)
universeEmbeddingStrComp {U = U} {V} {W} {f} {g} emb-f emb-g .decode-equiv s = goal where
  goal : W .El (g (f s)) ≃ U .El s
  goal = emb-g .decode-equiv (f s) ∙ₑ emb-f .decode-equiv s

_↪_ : ∀ {ℓU ℓV} → (V : Universe ℓV) (U : Universe ℓU) → Type (ℓ-max ℓV ℓU)
V ↪ U = Σ[ f ∈ (V .Code → U .Code) ] UniverseEmbeddingStr V U f

isSubUniverse : ∀ {ℓV ℓU} → (V : Universe ℓV) → (U : Universe ℓU) → Type (ℓ-max ℓV ℓU)
isSubUniverse V U = ∥ V ↪ U ∥₁

idEmbedding : ∀ {ℓ} {U : Universe ℓ} → U ↪ U
idEmbedding = idfun _ , universeEmbeddingStrId

_∙↪_ : ∀ {ℓU ℓV ℓW}
  → {U : Universe ℓU}
  → {V : Universe ℓV}
  → {W : Universe ℓW}
  → (ι : U ↪ V) → (κ : V ↪ W) → U ↪ W
(f , emb-f) ∙↪ (g , emb-g) = g ∘ f , universeEmbeddingStrComp emb-f emb-g
