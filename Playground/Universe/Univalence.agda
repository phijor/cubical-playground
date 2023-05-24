module Playground.Universe.Univalence where

open import Playground.Prelude
open import Playground.Universe.Base

open import Cubical.Foundations.Equiv using (_≃_ ; isEquiv ; equivProof ; isPropIsEquiv)
open import Cubical.Foundations.Univalence using (ua ; isEquivTransport)
open import Cubical.Foundations.HLevels using (isPropΠ2)


module _ {ℓ} (U : Universe ℓ) where
  open Universe U using (Code ; El)

  module _ {s t : Code} where
    transportU : s ≡ t → El s → El t
    transportU p = transport (cong El p)

    pathToEquivU : s ≡ t → El s ≃ El t
    pathToEquivU p .fst = transportU p
    pathToEquivU p .snd = isEquivTransport (cong El p)

  isUnivalent : Type ℓ
  isUnivalent = ∀ (s t : Code) → isEquiv (pathToEquivU {s} {t})

  isPropIsUnivalent : isProp isUnivalent
  isPropIsUnivalent = isPropΠ2 λ s t → isPropIsEquiv (pathToEquivU {s} {t})

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

Univalent : (ℓ : Level) → Type (ℓ-suc ℓ)
Univalent ℓ = Σ[ U ∈ Universe ℓ ] isUnivalent U
