-- Tardis
-- ======
--
-- > It's bigger on the inside
--
-- A generic construction of a small universe of types, defined via induction-recursion.

{-# OPTIONS --lossy-unification #-}
module Playground.Tardis where

open import Playground.Prelude
open import Playground.Proposition

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv renaming (_■ to _≃∎)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
import Cubical.Foundations.Univalence as Univalence
import Cubical.Foundations.Univalence.Universe as UU

open import Cubical.Functions.Embedding using (isEmbedding ; isEmbedding→Inj ; isEmbedding→hasPropFibers)
open import Cubical.Functions.Image using (Image ; isPropIsInImage)
open import Cubical.Data.Sigma as Sigma using (Σ≡Prop ; map-snd)
open import Cubical.Data.Nat.Base
open import Cubical.HITs.PropositionalTruncation as PT

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

  El (put x) = B x
  El (uni x y α i) = ua α i

  module Uni = UU Tardis El uni (λ _ → refl)

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

  isPropElWitness : {Y : Type ℓ'} → isProp (Σ[ x ∈ Tardis ] El x ≃ Y)
  isPropElWitness {Y = Y} = isOfHLevelRetractFromIso 1 (Sigma.Σ-cong-iso-snd ElUnivalenceIso) (hasPropFibersEl Y) where
    ElUnivalenceIso : ∀ x → Iso (El x ≃ Y) (El x ≡ Y)
    ElUnivalenceIso x = invIso (Univalence.univalenceIso {A = El x} {B = Y})
    toFiber : Σ[ x ∈ Tardis ] El x ≃ Y → fiber El Y
    toFiber = map-snd ua

  tyEquivToWitness : ∀ {a : A}
    → (Y : Type ℓ')
    → ∥ B a ≃ Y ∥₁
    → Σ[ x ∈ Tardis ] El x ≃ Y
  tyEquivToWitness {a = a} Y = PT.rec (isPropElWitness {Y}) (put a ,_)

  SkelStr : (Y : Type ℓ') → Type (ℓ-max ℓ ℓ')
  SkelStr Y = ∥ Σ[ a ∈ A ] B a ≃ Y ∥₁

  SkelStr→Witness : {Y : Type ℓ'} → SkelStr Y → Σ[ x ∈ Tardis ] El x ≃ Y
  SkelStr→Witness = PT.rec isPropElWitness λ { (a , α) → put a , α }

  isPropSkelStr : (Y : Type ℓ') → isProp (SkelStr Y)
  isPropSkelStr Y = isPropPropTrunc

  Skel : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Skel = TypeWithStr ℓ' SkelStr

  SkelPath : {S T : Skel} → ⟨ S ⟩ ≡ ⟨ T ⟩ → S ≡ T
  SkelPath = Σ≡Prop isPropSkelStr

  Tardis→SkelStr : (x : Tardis) → SkelStr (El x)
  Tardis→SkelStr = elimElProp isPropSkelStr λ (a : A) → ∣ a , idEquiv (B a) ∣₁

  Tardis→SkelStrPutWitness : (a : A) → SkelStr→Witness (Tardis→SkelStr (put a)) ≡ (put a , idEquiv (B a))
  abstract
    Tardis→SkelStrPutWitness a = refl

  Tardis→SkelStrWitness : (x : Tardis) → SkelStr→Witness (Tardis→SkelStr x) ≡ (x , idEquiv (El x))
  Tardis→SkelStrWitness (put a) = Tardis→SkelStrPutWitness a
  Tardis→SkelStrWitness (uni x y α i) = madness x y α i where
    module _ (x y : Tardis) (α : El x ≃ El y) where
      Motive : I → Type (ℓ-max ℓ ℓ')
      Motive i = SkelStr→Witness (Tardis→SkelStr (uni x y α i)) ≡ (uni x y α i , idEquiv (El (uni x y α i)))

      isPropMotive : (i : I) → isProp (Motive i)
      isPropMotive i = isProp→isSet (isPropElWitness {Y = ua α i}) (SkelStr→Witness (Tardis→SkelStr (uni x y α i))) (uni x y α i , idEquiv (ua α i))

      -- XXX: This requires `--lossy-unification`. Without lossy unification,
      -- Agda accepts the term given enought RAM (25GB is enough?)
      -- but takes an hour or so to finish on a 7th gen laptop.
      madness : PathP (λ i → Motive i) (Tardis→SkelStrWitness x) (Tardis→SkelStrWitness y)
      madness = isProp→PathP isPropMotive (Tardis→SkelStrWitness x) (Tardis→SkelStrWitness y)

  Tardis→Skel : Tardis → Skel
  Tardis→Skel x = El x , Tardis→SkelStr x

  Skel→Tardis : Skel → Tardis
  Skel→Tardis (Y , sk) = SkelStr→Witness sk .fst

  module _ where
    skeletonIso : Iso Tardis Skel
    skeletonIso .Iso.fun = Tardis→Skel
    skeletonIso .Iso.inv = Skel→Tardis
    skeletonIso .Iso.rightInv (Y , sk) = Σ≡Prop isPropSkelStr (uncurry rinv witness) where
      witness : Σ[ x ∈ Tardis ] El x ≃ Y
      witness = SkelStr→Witness sk

      module _ (x : Tardis) (α : El x ≃ Y) where
        witnessSkel : (Y , sk) ≡ Tardis→Skel x
        witnessSkel = sym (SkelPath (ua α))

        rinv : Tardis→Skel (Skel→Tardis (Y , sk)) .fst ≡ Y
        rinv =
          El (Skel→Tardis (Y , sk)) ≡⟨ cong (El ∘ Skel→Tardis) witnessSkel ⟩
          El (Skel→Tardis (Tardis→Skel x)) ≡⟨⟩
          El (SkelStr→Witness (Tardis→SkelStr x) .fst) ≡⟨ cong (El ∘ fst) (Tardis→SkelStrWitness x) ⟩
          El x ≡⟨ ua α ⟩
          Y ∎

    skeletonIso .Iso.leftInv = linv where
      linv : (x : Tardis) → SkelStr→Witness (Tardis→SkelStr x) .fst ≡ x
      linv x = cong fst (Tardis→SkelStrWitness x)

  skeletonEquiv : Tardis ≃ Skel
  skeletonEquiv = isoToEquiv skeletonIso

module Example where
  open import Cubical.Foundations.Transport using (substEquiv)
  open import Cubical.Foundations.Equiv.Properties using (invEquivEquiv)
  open import Cubical.Functions.Embedding
  open import Cubical.Data.SumFin
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

  FinSet≃FinSet' : ∀ {ℓ} → FinSet ℓ ≃ FinSet' ℓ
  FinSet≃FinSet' = Sigma.Σ-cong-equiv-snd λ Y → Univalence.pathToEquiv isFinSet≡isFinSet'

  -- It's equivalent to a large universe of finite sets:
  FinTardis≃FinSet : FinTardis ≃ FinSet ℓ-zero
  FinTardis≃FinSet =
    FinTardis ≃⟨ skeletonEquiv ⟩
    Σ[ Y ∈ Type ] ∥ Σ[ n ∈ ℕ ] Fin n ≃ Y ∥₁ ≃⟨ flip≃ ⟩
    Σ[ Y ∈ Type ] ∥ Σ[ n ∈ ℕ ] Y ≃ Fin n ∥₁ ≃⟨ idEquiv _ ⟩
    FinSet' ℓ-zero                          ≃⟨ invEquiv FinSet≃FinSet' ⟩
    FinSet ℓ-zero ≃∎

    where
      flip≃ = Sigma.Σ-cong-equiv-snd (λ Y → PT.propTrunc≃ (Sigma.Σ-cong-equiv-snd λ n → invEquivEquiv))
