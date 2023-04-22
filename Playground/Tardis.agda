-- Tardis
-- ======
--
-- > It's bigger on the inside
--
-- A generic construction of a small universe of types, defined via induction-recursion.

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
  Tardis→SkelStrWitness (uni x y α i) = {! madness x y α i !} {- See below -} where
    module _ (x y : Tardis) (α : El x ≃ El y) where
      P : I → Type (ℓ-max ℓ ℓ')
      P i = SkelStr→Witness (Tardis→SkelStr (uni x y α i)) ≡ (uni x y α i , idEquiv (El (uni x y α i)))

      isPropP : (i : I) → isProp (P i)
      abstract
        isPropP i = isProp→isSet (isPropElWitness {Y = ua α i}) (SkelStr→Witness (Tardis→SkelStr (uni x y α i))) (uni x y α i , idEquiv (ua α i))
  
      -- XXX: Here lies madness. Uncomment and see Agda go wild.
      -- Agda accepts the term, given enought RAM (25GB is enough?)
      -- but takes an hour or so to finish on a 7th gen laptop.

      -- madness : PathP P (Tardis→SkelStrWitness x) (Tardis→SkelStrWitness y)
      -- madness = isProp→PathP isPropP (Tardis→SkelStrWitness x) (Tardis→SkelStrWitness y)

  Tardis→Skel : Tardis → Skel
  Tardis→Skel x = El x , Tardis→SkelStr x

  Skel→Tardis : Skel → Tardis
  Skel→Tardis (Y , sk) = SkelStr→Witness sk .fst

  module _ {- (embB : isEmbedding B) -} where
    skeletonIso : Iso Tardis Skel
    skeletonIso .Iso.fun = Tardis→Skel
    skeletonIso .Iso.inv = Skel→Tardis
    skeletonIso .Iso.rightInv (Y , sk) = Σ≡Prop isPropSkelStr {! !} where
      witness : Σ[ x ∈ Tardis ] El x ≃ Y
      witness = SkelStr→Witness sk

      module _ (x : Tardis) (α : El x ≃ Y) where
        rinv : Tardis→Skel (Skel→Tardis (Y , sk)) .fst ≡ Y
        rinv =
          El (Skel→Tardis (Y , sk)) ≡⟨ {! !} ⟩
          El (SkelStr→Witness (Tardis→SkelStr x) .fst) ≡⟨ {! !} ⟩
          El x ≡⟨ ua α ⟩
          Y ∎

    skeletonIso .Iso.leftInv = linv where
      linv : (x : Tardis) → SkelStr→Witness (elimElProp isPropSkelStr (λ (a : A) → ∣ a , idEquiv (B a) ∣₁) x) .fst ≡ x
      linv x = {! !}

  isEquiv-Tardis→Skel : isEquiv Tardis→Skel
  isEquiv-Tardis→Skel .equiv-proof (Y , sk) = ctr , {! !} where
    P : Tardis → Type (ℓ-suc ℓ')
    P x = ∥ Σ[ Y ∈ Type ℓ' ] Y ≃ (El x) ∥₁

    get : Tardis
    get = propImageElim P {!isPropPropTrunc !} (λ { (a , _) → put a }) (λ { (a , γ) → {! !} }) sk

    ctr : Σ[ x ∈ Tardis ] Tardis→Skel x ≡ (Y , sk)
    ctr = get , {! !}

  skeletonEquiv : Tardis ≃ Skel
  skeletonEquiv = Tardis→Skel , isEquiv-Tardis→Skel

module Example where
  open import Cubical.Data.SumFin
  open import Cubical.Data.FinSet
  open import Cubical.Functions.Embedding

  FinTardis : Type
  FinTardis = Tardis.Tardis ℕ Fin

  open module FinTardis = Tardis ℕ Fin

  -- `Tardis ℕ Fin` is the (small) universe of finite sets.
  -- Since it's generated by a collection of sets, it forms a groupoid.
  isGroupoidFinTardis : isGroupoid FinTardis
  isGroupoidFinTardis = isOfHLevelTardis {2} λ k → isSetFin {k}

  -- It's equivalent to a large universe, compare this to `FinSet'` below:
  FinTardis≃FinSet : FinTardis ≃ (Σ[ Y ∈ Type ] ∥ Σ[ n ∈ ℕ ] Fin n ≃ Y ∥₁)
  FinTardis≃FinSet = skeletonEquiv

  _ : (Σ[ Y ∈ Type ] isFinSet' Y) ≡ (Σ[ Y ∈ Type ] ∥ Σ[ n ∈ ℕ ] Y ≃ Fin n ∥₁)
  _ = refl
