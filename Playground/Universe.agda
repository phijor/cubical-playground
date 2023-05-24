module Playground.Universe where

open import Playground.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua ; isEquivTransport)
open import Cubical.Data.Unit.Base
open import Cubical.Functions.Embedding

record Universe (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    Code : Type ℓ
    decode : Code → Type ℓ

open Universe
record UniverseEmbeddingStr
  {ℓ} (V U : Universe ℓ) (f : V .Code → U .Code)
  : Type ℓ where
  field
    is-emb : isEmbedding f
    decode-equiv : ∀ (A : V .Code) → U .decode (f A) ≃ V .decode A

_↪ᵤ_ : ∀ {ℓ} → (V U : Universe ℓ) → Type ℓ
V ↪ᵤ U = Σ[ f ∈ (V .Code → U .Code) ] UniverseEmbeddingStr V U f

module _ {ℓ} {U : Type ℓ} (T : U → Type ℓ) where

  module _ {A B : U} where
    transportU : A ≡ B → T A → T B
    transportU p = transport (cong T p)

    pathToEquivU : A ≡ B → T A ≃ T B
    pathToEquivU p .fst = transportU p
    pathToEquivU p .snd = isEquivTransport (cong T p)
    
  isUnivalent : Type ℓ
  isUnivalent = (A B : U) → isEquiv (pathToEquivU {A} {B})

  T-ΣU : (A : U) (B : T A → U) → Type ℓ
  T-ΣU A B = Σ (T A) (T ∘ B)

  T-ΠU : (A : U) (B : T A → U) → Type ℓ
  T-ΠU A B = (a : T A) → T (B a)

  isUSmall : (X : Type ℓ) → Type ℓ
  isUSmall X = Σ[ Y ∈ U ] (T Y ≃ X)

  isΣRegular : Type ℓ
  isΣRegular = (A : U) (B : T A → U) → isUSmall (T-ΣU A B)

  isΠRegular : Type ℓ
  isΠRegular = (A : U) (B : T A → U) → isUSmall (T-ΠU A B)

  hasSingletons : Type ℓ
  hasSingletons = isUSmall (Σ[ A ∈ U ] isContr (T A))

  hasEmpty : Type ℓ
  hasEmpty = isUSmall (Unit* {ℓ})

  hasEquivalences : Type ℓ
  hasEquivalences = (A B : U) → isUSmall (T A ≃ T B)

  module ΣRegularity (reg : isΣRegular) where
    ΣU : (A : U) → (B : T A → U) → U
    ΣU A B = reg A B .fst

    syntax ΣU A (λ a → B) = ΣU[ a ∈ A ] B

  module ΠRegularity (reg : isΠRegular) where
    ΠU : (A : U) → (B : T A → U) → U
    ΠU A B = reg A B .fst

    syntax ΠU A (λ a → B) = ΠU[ a ∈ A ] B

    _→U_ : (A B : U) → U
    A →U B = ΠU A (λ _ → B)

    infixr 9 _→U_

    Π⌜_⌝ : ∀ {A B} → T (ΠU A B) → (a : T A) → T (B a)
    Π⌜_⌝ {A} {B} = reg A B .snd .fst

    ⌜_⌝→ : ∀ {A B} → T (A →U B) → T A → T B
    ⌜_⌝→ = Π⌜_⌝


  module _ (univ : isUnivalent) (Σreg : isΣRegular) (Πreg : isΠRegular) where
    open ΣRegularity Σreg
    open ΠRegularity Πreg

    isContrU : (A : U) → U
    isContrU A = ΠU[ x ∈ A ] ΠU[ y ∈ A ] {! univ!}

    module _ {A B : U} where
      isEquivU : (f : T (A →U B)) → U
      isEquivU f = {!isEquiv ⌜ f ⌝→ !}

      EquivU : U
      EquivU = ΣU[ f ∈ (A →U B)] isEquivU f

    isΣΠRegular→hasEquivalences : hasEquivalences
    isΣΠRegular→hasEquivalences A B = EquivU , TEquivU≃ where
      TEquivU≃ : T EquivU ≃ (T A ≃ T B)
      TEquivU≃ = {! !}
