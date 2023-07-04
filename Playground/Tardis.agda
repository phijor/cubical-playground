-- Tardis
-- ======
--
-- > It's bigger on the inside
--
-- A generic construction of a small universe of types, defined via induction-recursion.

module Playground.Tardis where

open import Playground.Prelude hiding (empty)
open import Playground.Proposition

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎)
open import Cubical.Foundations.Equiv.Properties using (invEquivEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
import Cubical.Foundations.Univalence as Univalence
import Cubical.Foundations.Univalence.Universe as UU

open import Cubical.Functions.Image
open import Cubical.Functions.Embedding
  using
    ( isEmbedding
    ; isEmbedding→Inj
    ; hasPropFibers
    ; isEmbedding→hasPropFibers

    )
open import Cubical.Data.Sigma as Sigma using (Σ≡Prop ; map-snd)
open import Cubical.Data.Nat.Base
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

module Tardis
  {ℓ ℓ'}
  (A : Type ℓ)
  (B : A → Type ℓ')
  where

  data Tardis : Type (ℓ-max ℓ ℓ')
  El : Tardis → Type ℓ'

  data Tardis where
    put : (a : A) → Tardis
    uni : (x y : Tardis) → (α : El x ≃ El y) → x ≡ y

  El (put a) = B a
  El (uni x y α i) = ua α i

  module Uni = UU Tardis El uni (λ _ → refl)

  elimProp : ∀ {ℓP} {P : Tardis → Type ℓP}
    → (propP : (x : Tardis) → isProp (P x))
    → (put* : (a : A) → P (put a))
    → (x : Tardis) → P x
  elimProp propP put* (put a) = put* a
  elimProp propP put* (uni x y α i) = isProp→PathP (λ i → propP (uni x y α i)) (elimProp propP put* x) (elimProp propP put* y) i

  elimElProp : ∀ {ℓ} {P : Type ℓ' → Type ℓ}
    → (propP : (X : Type ℓ') → isProp (P X))
    → (put* : (a : A) → P (B a))
    → (x : Tardis) → P (El x)
  elimElProp propP put* (put a) = put* a
  elimElProp propP put* (uni x y α i) = isProp→PathP (λ i → propP (ua α i)) (elimElProp propP put* x) (elimElProp propP put* y) i

  isEmbeddingEl : isEmbedding El
  isEmbeddingEl = Uni.isEmbeddingEl

  hasPropFibersEl : (Y : Type ℓ') → isProp (fiber El Y)
  hasPropFibersEl = isEmbedding→hasPropFibers isEmbeddingEl

  isOfHLevelEl : {n : HLevel} → (∀ a → isOfHLevel n (B a)) → (x : Tardis) → isOfHLevel n (El x)
  isOfHLevelEl {n} = elimElProp (λ X → isPropIsOfHLevel {A = X} n)

  isPropTardis : (∀ a → isContr (B a)) → isProp Tardis
  isPropTardis ctrB x y = uni x y α where
    α : El x ≃ El y
    α = isContr→Equiv (isOfHLevelEl ctrB x) (isOfHLevelEl ctrB y)

  isOfHLevelTardis : ∀ {n : HLevel} → (∀ a → isOfHLevel n (B a)) → isOfHLevel (suc n) Tardis
  isOfHLevelTardis {n = zero} = isPropTardis
  isOfHLevelTardis {n = suc n} lvlB x y = isOfHLevelRetractFromIso (suc n) ι sub where
    sub : isOfHLevel (suc n) (El x ≡ El y)
    sub = isOfHLevel≡ (suc n) (isOfHLevelEl lvlB x) (isOfHLevelEl lvlB y)

    ι : Iso (x ≡ y) (El x ≡ El y)
    ι = Uni.pathIso x y

  isPropElWitness : {Y : Type ℓ'} → isProp (Σ[ x ∈ Tardis ] Y ≃ El x)
  isPropElWitness {Y = Y} = isOfHLevelRespectEquiv 1 (Sigma.Σ-cong-equiv-snd ElUnivalenceEquiv) (hasPropFibersEl Y) where
    ElUnivalenceEquiv : ∀ x → (El x ≡ Y) ≃ (Y ≃ El x)
    ElUnivalenceEquiv x = isoToEquiv symIso ∙ₑ Univalence.univalence {A = Y} {B = El x}

  tyEquivToWitness : ∀ {a : A}
    → (Y : Type ℓ')
    → ∥ Y ≃ B a ∥₁
    → Σ[ x ∈ Tardis ] Y ≃ El x
  tyEquivToWitness {a = a} Y = PT.rec (isPropElWitness {Y}) (put a ,_)

  SkelStr : (Y : Type ℓ') → Type (ℓ-max ℓ ℓ')
  SkelStr Y = ∥ Σ[ a ∈ A ] Y ≃ B a ∥₁

  SkelStr→Witness : {Y : Type ℓ'} → SkelStr Y → Σ[ x ∈ Tardis ] Y ≃ El x
  SkelStr→Witness = PT.rec isPropElWitness λ { (a , α) → put a , α }

  isPropSkelStr : (Y : Type ℓ') → isProp (SkelStr Y)
  isPropSkelStr Y = PT.isPropPropTrunc

  Skel : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Skel = TypeWithStr ℓ' SkelStr

  SkelPath : {S T : Skel} → ⟨ S ⟩ ≡ ⟨ T ⟩ → S ≡ T
  SkelPath = Σ≡Prop isPropSkelStr

  SkelStr∞ : (Y : Type ℓ') → Type (ℓ-max ℓ ℓ')
  SkelStr∞ Y = Σ[ a ∈ A ] ∥ Y ≃ B a ∥₁

  Skel∞ : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Skel∞ = TypeWithStr ℓ' SkelStr∞

  SkelStr∞→SkelStr : ∀ {Y} → SkelStr∞ Y → SkelStr Y
  SkelStr∞→SkelStr {Y = Y} = uncurry (λ a → PT.map (a ,_))

  module _ (setA : isSet A) (injB : (x y : A) → B x ≡ B y → x ≡ y) where
    isPropSkelStr∞ : (Y : Type ℓ') → isProp (SkelStr∞ Y)
    isPropSkelStr∞ Y (x , ∣α∣) (y , ∣β∣) = Σ≡Prop (λ _ → PT.isPropPropTrunc) goal where
      lem : (α : Y ≃ B x) (β : Y ≃ B y) → x ≡ y
      lem α β = injB x y (ua γ) where
        γ : B x ≃ B y
        γ = invEquiv α ∙ₑ β

      goal : x ≡ y
      goal = PT.rec2 (setA x y) lem ∣α∣ ∣β∣

    SkelStr→SkelStr∞ : ∀ {Y} → SkelStr Y → SkelStr∞ Y
    SkelStr→SkelStr∞ {Y} = PT.rec (isPropSkelStr∞ Y) f where
      f : Σ[ a ∈ A ] Y ≃ B a → SkelStr∞ Y
      f = map-snd ∣_∣₁

    SkelStr∞≃SkelStr : ∀ Y → SkelStr∞ Y ≃ SkelStr Y
    SkelStr∞≃SkelStr Y = propBiimpl→Equiv (isPropSkelStr∞ Y) (isPropSkelStr Y) SkelStr∞→SkelStr SkelStr→SkelStr∞

    Skel∞≃Skel : Skel∞ ≃ Skel
    Skel∞≃Skel = Sigma.Σ-cong-equiv-snd SkelStr∞≃SkelStr

  Tardis→SkelStr : (x : Tardis) → SkelStr (El x)
  Tardis→SkelStr = elimElProp isPropSkelStr λ (a : A) → ∣ a , idEquiv (B a) ∣₁

  Tardis→SkelStrPutWitness : (a : A) → SkelStr→Witness (Tardis→SkelStr (put a)) ≡ (put a , idEquiv (B a))
  abstract
    Tardis→SkelStrPutWitness a = refl

  Tardis→SkelStrWitness : (x : Tardis) → SkelStr→Witness (Tardis→SkelStr x) ≡ (x , idEquiv (El x))
  Tardis→SkelStrWitness = elimProp (λ x → isProp→isSet isPropElWitness _ _) λ a → refl {x = put a , idEquiv (B a)}

  -- Tardis→SkelStrWitness : (x : Tardis) → SkelStr→Witness (Tardis→SkelStr x) ≡ (x , idEquiv (El x))
  -- Tardis→SkelStrWitness (put a) = Tardis→SkelStrPutWitness a
  -- Tardis→SkelStrWitness (uni x y α i) = madness x y α i where
  --   module _ (x y : Tardis) (α : El x ≃ El y) where
  --     Motive : I → Type (ℓ-max ℓ ℓ')
  --     Motive i = SkelStr→Witness (Tardis→SkelStr (uni x y α i)) ≡ (uni x y α i , idEquiv (El (uni x y α i)))

  --     isPropMotive : (i : I) → isProp (Motive i)
  --     isPropMotive i = isProp→isSet (isPropElWitness {Y = ua α i}) (SkelStr→Witness (Tardis→SkelStr (uni x y α i))) (uni x y α i , idEquiv (ua α i))

  --     -- XXX: This requires `--lossy-unification`. Without lossy unification,
  --     -- Agda accepts the term given enought RAM (25GB is enough?)
  --     -- but takes an hour or so to finish on a 7th gen laptop.
  --     madness : PathP (λ i → Motive i) (Tardis→SkelStrWitness x) (Tardis→SkelStrWitness y)
  --     madness = isProp→PathP isPropMotive (Tardis→SkelStrWitness x) (Tardis→SkelStrWitness y)

  Tardis→Skel : Tardis → Skel
  Tardis→Skel x = El x , Tardis→SkelStr x

  Skel→Tardis : Skel → Tardis
  Skel→Tardis (Y , sk) = SkelStr→Witness sk .fst

  module _ where
    skeletonIso : Iso Tardis Skel
    skeletonIso .Iso.fun = Tardis→Skel
    skeletonIso .Iso.inv = Skel→Tardis
    skeletonIso .Iso.rightInv (Y , sk) = Σ≡Prop isPropSkelStr (uncurry rinv witness) where
      witness : Σ[ x ∈ Tardis ] Y ≃ El x
      witness = SkelStr→Witness sk

      module _ (x : Tardis) (α : Y ≃ El x) where
        witnessSkel : (Y , sk) ≡ Tardis→Skel x
        witnessSkel = SkelPath (ua α)

        rinv : Tardis→Skel (Skel→Tardis (Y , sk)) .fst ≡ Y
        rinv =
          El (Skel→Tardis (Y , sk)) ≡⟨ cong (El ∘ Skel→Tardis) witnessSkel ⟩
          El (Skel→Tardis (Tardis→Skel x)) ≡⟨⟩
          El (SkelStr→Witness (Tardis→SkelStr x) .fst) ≡⟨ cong (El ∘ fst) (Tardis→SkelStrWitness x) ⟩
          El x ≡⟨ sym (ua α) ⟩
          Y ∎

    skeletonIso .Iso.leftInv = linv where
      linv : (x : Tardis) → SkelStr→Witness (Tardis→SkelStr x) .fst ≡ x
      linv x = cong fst (Tardis→SkelStrWitness x)

  skeletonEquiv : Tardis ≃ Skel
  skeletonEquiv = isoToEquiv skeletonIso

module FinExample where
  open import Cubical.Foundations.Transport using (substEquiv)
  open import Cubical.Functions.Embedding
  open import Cubical.Data.Empty.Base as Empty using (⊥)
  open import Cubical.Data.SumFin
  open import Cubical.Data.Nat.Properties
  open import Cubical.Data.FinSet

  FinTardis : Type
  FinTardis = Tardis.Tardis ℕ Fin

  open module FinTardis = Tardis ℕ Fin

  -- `Tardis ℕ Fin` is the (small) universe of finite sets.
  -- Since it's generated by a collection of sets, it forms a groupoid.
  isGroupoidFinTardis : isGroupoid FinTardis
  isGroupoidFinTardis = isOfHLevelTardis {2} λ k → isSetFin {k}

  FinSet' : (ℓ : Level) → Type (ℓ-suc ℓ)
  FinSet' ℓ = TypeWithStr ℓ isFinSet'

  FinInj : (k l : ℕ) → Fin k ≡ Fin l → k ≡ l
  FinInj k l p = LTFin.Fin-inj k l (subst2 _≡_ (SumFin≡Fin k) (SumFin≡Fin l) p) where
    import Cubical.Data.Fin as LTFin

  FinSet≃FinSet' : FinSet ℓ-zero ≃ FinSet' ℓ-zero
  FinSet≃FinSet' = Skel∞≃Skel isSetℕ FinInj

  -- It's equivalent to a large universe of finite sets:
  FinTardis≃FinSet : FinTardis ≃ FinSet ℓ-zero
  FinTardis≃FinSet =
    FinTardis       ≃⟨ skeletonEquiv ⟩
    FinSet' ℓ-zero  ≃⟨ invEquiv FinSet≃FinSet' ⟩
    FinSet ℓ-zero   ≃∎

  FinInduction' : ∀ {ℓ} {P : Type → Type ℓ} → ((X : Type) → isProp (P X)) → ((a : ℕ) → P (Fin a)) → (x : FinTardis) → P (El x)
  FinInduction' = elimElProp

  FinInduction″ : ∀ {ℓ} {P : FinTardis → Type ℓ} → ((x : FinTardis) → isProp (P x)) → ((a : ℕ) → P (put a)) → (x : FinTardis) → P x
  FinInduction″ = FinTardis.elimProp

  -- FinInduction‴ : ∀ {ℓ} {P : FinSet ℓ-zero → Type ℓ} → ((X : FinSet ℓ-zero) → isProp (P x)) → ((n : ℕ) → P ?) → (X : FinSet ℓ-zero) → P x
  -- FinInduction‴ = FinTardis.elimProp

module TardisSquared (A : Type) (B : A → Type) where
  private
    module Once = Tardis A B

  Tardis² : Type
  Tardis² = Tardis.Tardis Once.Tardis Once.El

  Tardis^ : (n : ℕ) → Type
  El^ : (n : ℕ) → Tardis^ n → Type

  Tardis^ zero = A
  Tardis^ (suc n) = Tardis.Tardis (Tardis^ n) (El^ n)
    
  El^ zero = B
  El^ (suc n) = Tardis.El (Tardis^ n) (El^ n)

module SigmaPiExample where
  open import Cubical.Foundations.Transport using (substEquiv)
  open import Cubical.Data.Empty.Base
  open import Cubical.Data.Unit.Base

  data U : Type
  #_ : U → Type

  data U where
    empty : U
    unit : U
    sigma : (A : U) → (B : # A → U) → U
    pi : (A : U) → (B : # A → U) → U
    path : (A : U) → (x y : # A) → U

  # empty = ⊥
  # unit = Unit
  # sigma A B = Σ[ a ∈ # A ] # B a
  # pi A B  = (a : # A) → # B a
  # path A x y = Path (# A) x y

  #Path : {A B : U} → # A ≡ # B → A ≡ B
  #Path {empty} {empty} = {! !}
  #Path {empty} {unit} = {! !}
  #Path {empty} {sigma B B₁} = {! !}
  #Path {empty} {pi B B₁} = {! !}
  #Path {empty} {path B x y} = {! !}
  #Path {unit} {B} = {! !}
  #Path {sigma A B₁} {B} = {! !}
  #Path {pi A B₁} {B} = {! !}
  #Path {path A x y} {B} = {! !}

  module ΣΠ = Tardis U #_

  ΣΠ : Type
  ΣΠ = Tardis.Tardis U #_

  isContrU : U → U
  isContrU A = sigma A λ x → pi A λ y → path A x y

  ΣΠ-isContr : ΣΠ → ΣΠ
  ΣΠ-isContr (Tardis.put A) = Tardis.put (isContrU A)
  ΣΠ-isContr (Tardis.uni X Y α i) = goal i where
    goal : ΣΠ-isContr X ≡ ΣΠ-isContr Y
    goal = {! (ua α) !}

module GlueOver
  (A : Type)
  (B : A → Type)
  where
  open import Cubical.Foundations.Univalence

  uaOver : {x y : A} → (p : x ≡ y)
    → (S : Type) → (σ : S ≃ B x)
    → (T : Type) → (τ : T ≃ B y)
    → S ≡ T
  uaOver p S σ T τ i = Glue (B (p i)) {φ = i ∨ ~ i} λ where
    (i = i0) → S , σ
    (i = i1) → T , τ
