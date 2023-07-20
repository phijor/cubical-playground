module Playground.Universe.Univalence where

open import Playground.Prelude
open import Playground.Universe.Base

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua ; isEquivTransport ; Glue ; pathToEquiv)
open import Cubical.Foundations.HLevels using (isPropΠ2 ; isContrRetract)
open import Cubical.Foundations.Univalence using (univalence ; pathToEquivRefl ; EquivJ ; uaIdEquiv)
open import Cubical.Foundations.Path using (toPathP⁻)

open import Cubical.Functions.Embedding using (isEmbedding ; isPropIsEmbedding)
open import Cubical.Data.Sigma

module _ {ℓ} (U : Universe ℓ) where
  open Universe U using (Code ; El ; idElEquiv)

  module _ {s t : Code} where
    transportU : s ≡ t → El s → El t
    transportU p = transport (cong El p)

    pathToEquivU : s ≡ t → El s ≃ El t
    pathToEquivU p .fst = transportU p
    pathToEquivU p .snd = isEquivTransport (cong El p)

    pathToEquivU≡pathToEquiv∘congEl : pathToEquivU ≡ pathToEquiv ∘ cong {x = s} {y = t} El
    pathToEquivU≡pathToEquiv∘congEl = refl

  isUnivalent : Type ℓ
  isUnivalent = ∀ (s t : Code) → isEquiv (pathToEquivU {s} {t})

  isPropIsUnivalent : isProp isUnivalent
  isPropIsUnivalent = isPropΠ2 λ s t → isPropIsEquiv (pathToEquivU {s} {t})

  module _ (uniU : isUnivalent) where
    open import Cubical.Foundations.Equiv.Properties using (isEquiv[equivFunA≃B∘f]→isEquiv[f] ; equivAdjointEquiv)

    isUnivalent→isEmbeddingEl : isEmbedding El
    isUnivalent→isEmbeddingEl s t = isEquivCongEl where
      isEquivCongEl : isEquiv (cong {x = s} {y = t} El)
      isEquivCongEl = isEquiv[equivFunA≃B∘f]→isEquiv[f] (cong El) univalence (uniU s t)

    univalenceU : (s t : Code) → (s ≡ t) ≃ (El s ≃ El t)
    univalenceU s t = pathToEquivU , uniU s t

    uaU : {s t : Code} → (El s ≃ El t) → s ≡ t
    uaU = invEq $ univalenceU _ _

    isContrElEquiv : (s : Code) → ∃![ t ∈ Code ] (El s ≃ El t)
    isContrElEquiv s = isContrRetract {B = singl s} (map-snd uaU) (map-snd pathToEquivU) (isom .Iso.rightInv) (isContrSingl s) where
      isom : Iso (singl s) (Σ[ t ∈ Code ] El s ≃ El t)
      isom = Σ-cong-iso-snd λ t → equivToIso $ univalenceU s t

    contrSinglEl : {s t : Code} (α : El s ≃ El t) → (s , idElEquiv s) ≡ (t , α)
    contrSinglEl {s = s} {t = t} α = isContr→isProp (isContrElEquiv s) (s , idElEquiv s) (t , α)

    ElJ : ∀ {ℓP} {s t : Code} (P : (t : Code) → (α : El s ≃ El t) → Type ℓP)
      → (r : P s (idElEquiv s))
      → (α : El s ≃ El t) → P t α
    ElJ {s = s} {t = t} P r α = subst F (contrSinglEl {s} {t} α) r where
      F : Σ[ u ∈ Code ] El s ≃ El u → Type _
      F (u , φ) = P u φ

    uaUIdEquivRefl : ∀ s → uaU (idElEquiv s) ≡ refl′ s
    uaUIdEquivRefl s = sym $ invEq (equivAdjointEquiv (univalenceU s s) {a = refl′ s} {b = idElEquiv s}) pathToEquivRefl

    uaU-β : {s t : Code} → (α : El s ≃ El t) → cong El (uaU α) ≡ ua α
    uaU-β {s = s} = ElJ (λ t α → cong El (uaU α) ≡ ua α) $
      cong El (uaU (idElEquiv s)) ≡⟨ cong (cong El) (uaUIdEquivRefl s) ⟩
      cong El (refl′ s)           ≡⟨ sym $ uaIdEquiv {A = El s} ⟩∎
      ua (idEquiv (El s)) ∎

  record HasUA : Type (ℓ-suc ℓ) where
    field
      ua-fun : (s t : Code) → El s ≃ El t → s ≡ t
      ua-β : {s t : Code} → (α : El s ≃ El t) → cong El (ua-fun s t α) ≡ ua α

  module Univalence
    (uaU : (s t : Code) → El s ≃ El t → s ≡ t)
    (uaU-β : {s t : Code} → (α : El s ≃ El t) → cong El (uaU s t α) ≡ ua α)
    where

    open import Cubical.Foundations.Univalence.Universe Code El uaU uaU-β
      using
        ( equivIso
        ; pathIso
        ; minivalence
        ; path-reflection
        ; isEmbeddingEl
        )
      public
  
    hasUA→isUnivalent : isUnivalent
    hasUA→isUnivalent s t = minivalence {s = s} {t = t} .snd

  isEmbeddingEl→isUnivalent : isEmbedding El → isUnivalent
  isEmbeddingEl→isUnivalent is-emb-El s t = equivIsEquiv α where
    α : (s ≡ t) ≃ (El s ≃ El t)
    α = (cong El , is-emb-El s t) ∙ₑ univalence

  isEmbeddingEl≃isUnivalent : isEmbedding El ≃ isUnivalent
  isEmbeddingEl≃isUnivalent = propBiimpl→Equiv
    isPropIsEmbedding
    isPropIsUnivalent
    isEmbeddingEl→isUnivalent
    isUnivalent→isEmbeddingEl

Univalent : (ℓ : Level) → Type (ℓ-suc ℓ)
Univalent ℓ = Σ[ U ∈ Universe ℓ ] isUnivalent U
