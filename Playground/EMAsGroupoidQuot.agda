module Playground.EMAsGroupoidQuot where

open import Playground.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path using (flipSquare)
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.HITs.EilenbergMacLane1 as EM using (EM₁)
open import Cubical.HITs.GroupoidQuotients as GQ using (_//_)
open import Cubical.Algebra.Group.Base using (Group ; GroupStr)

module _ {ℓ} (G : Group ℓ) where
  module G = GroupStr (str G)

  R : Unit → Unit → Type ℓ
  R tt tt = ⟨ G ⟩

  ·R : BinaryRelation.isTrans R
  ·R tt tt tt = G._·_

  1/G : Type ℓ
  1/G = Unit // ·R

  ΩG : Type ℓ
  ΩG = EM₁ G

  1/G→ΩG : 1/G → ΩG
  1/G→ΩG = GQ.rec ·R EM₁.emsquash base loop comp' where
    base : Unit → ΩG
    base tt = EM₁.embase

    loop : {a b : Unit} → R a b → base a ≡ base b
    loop {a = tt} {tt} = EM₁.emloop

    comp' : ∀ {a b c : Unit} (g : R a b) (h : R b c) → Square (loop g) (loop (g G.· h)) refl (loop h)
    comp' {a = tt} {tt} {tt} = EM₁.emcomp

  ΩG→1/G : ΩG → 1/G
  ΩG→1/G = EM.rec G GQ.squash// ⋆ loop comp' where
    ⋆ : 1/G
    ⋆ = GQ.[ tt ]

    loop : (g : ⟨ G ⟩) → ⋆ ≡ ⋆
    loop = GQ.eq//

    comp' : (g h : ⟨ G ⟩) → Square (loop g) (loop (g G.· h)) refl (loop h)
    comp' = GQ.comp//


  1/-Ω-Iso : Iso 1/G ΩG
  1/-Ω-Iso .Iso.fun = 1/G→ΩG
  1/-Ω-Iso .Iso.inv = ΩG→1/G
  1/-Ω-Iso .Iso.rightInv = EM.elimSet G (λ x → isSetEMPath _ x) loop sq where
    isSetEMPath : (x y : EM₁ G) → isSet (x ≡ y)
    isSetEMPath = EM₁.emsquash

    loop : EM₁.embase ≡ EM₁.embase
    loop = refl

    sq : (g : ⟨ G ⟩) → PathP (λ i → 1/G→ΩG (ΩG→1/G (EM₁.emloop g i)) ≡ EM₁.emloop g i) loop loop
    sq g i j = EM₁.emloop g i

  1/-Ω-Iso .Iso.leftInv = GQ.elimSet ·R (λ x → isSetGQPath _ x) (λ { tt → refl }) λ { {tt} {tt} g h → refl } where
    isSetGQPath : (x y : 1/G) → isSet (x ≡ y)
    isSetGQPath = GQ.squash//
