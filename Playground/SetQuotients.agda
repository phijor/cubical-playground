module Playground.SetQuotients where

open import Playground.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels as HLevels using (hProp ; isSetHProp)
open import Cubical.Foundations.Univalence using (hPropExt ; ua)
open import Cubical.Foundations.Equiv.Fiberwise using (fundamentalTheoremOfId)
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Foundations.Structure
open import Cubical.Reflection.StrictEquiv using (strictIsoToEquiv)

open import Cubical.Data.Sigma.Properties
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_])
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Relation.Binary.Base using (module BinaryRelation ; Rel)

open import Cubical.Functions.Logic using (hProp≡ ; isProp⟨⟩)

open BinaryRelation using (isEffective)

module Effective {ℓ} {A : Type ℓ} {R : Rel A A ℓ} (eff : isEffective R) where
  effectiveEquiv : ∀ a b → R a b ≃ ([ a ] ≡ [ b ])
  effectiveEquiv a b = _ , eff a b

  effectivePath : ∀ a b → R a b ≡ ([ a ] ≡ [ b ])
  effectivePath a b = ua (effectiveEquiv a b)

  isPropValuedR : BinaryRelation.isPropValued R
  isPropValuedR a b = HLevels.isOfHLevelRespectEquiv 1 (invEquiv (effectiveEquiv a b)) (HLevels.isOfHLevelPath' 1 SQ.squash/ [ a ] [ b ])

  private
    toR : (a b : A) → [ a ] ≡ [ b ] → R a b
    toR a b = invIsEq (eff a b)

    reflR : (a : A) → R a a
    reflR a = toR a a refl

    subst-R-left : ∀ {a b c : A} → (r : R a b) → R a c ≡ R b c
    subst-R-left {a} {b} {c} r = subst2 _≡_ (sym $ effectivePath _ _) (sym $ effectivePath _ _) goal where
      goal : ([ a ] ≡ [ c ]) ≡ ([ b ] ≡ [ c ])
      goal = cong (_≡ [ c ]) (SQ.eq/ a b r)

    subst-R-right : ∀ {a b c : A} → (r : R a b) → R c a ≡ R c b
    subst-R-right {a} {b} {c} r = subst2 _≡_ (sym $ effectivePath _ _) (sym $ effectivePath _ _) goal where
      goal : ([ c ] ≡ [ a ]) ≡ ([ c ] ≡ [ b ])
      goal = cong ([ c ] ≡_) (SQ.eq/ a b r)

    RProp : A → A → hProp ℓ
    RProp a b = R a b , isPropValuedR a b

    RProp-left : (a b c : A) → R a b → RProp a c ≡ RProp b c
    RProp-left a b c r = hProp≡ $ subst-R-left r

    RProp-right : (a b c : A) → R b c → RProp a b ≡ RProp a c
    RProp-right a b c r = hProp≡ $ subst-R-right r

  EqProp : (x y : A / R) → hProp ℓ
  EqProp = SQ.rec2 isSetHProp RProp RProp-left RProp-right

  Eq : (x y : A / R) → Type ℓ
  Eq x y = ⟨ EqProp x y ⟩

  isPropEq : (x y : A / R) → isProp (Eq x y)
  isPropEq x y = isProp⟨⟩ (EqProp x y)

  reflEq : (x : A / R) → Eq x x
  reflEq = SQ.elimProp (λ x → isPropEq x x) reflR

  isContrEqSingl : (x : A / R) → isContr (Σ (A / R) (Eq x))
  isContrEqSingl x = (x , reflEq x) , uncurry (goal x) where
    module _ (x y : A / R) where
      step : Eq x y → x ≡ y
      step = SQ.elimProp2 {P = λ x y → Eq x y → x ≡ y} (λ _ _ → HLevels.isPropΠ λ _ → SQ.squash/ _ _) SQ.eq/ x y

      goal : (p : Eq x y) → (x , reflEq x) ≡ (y , p)
      goal p = Σ≡Prop (λ z → isPropEq x z) (step p)

  Path≃Eq : (x y : A / R) → (x ≡ y) ≃ Eq x y
  Path≃Eq = fundamentalTheoremOfId Eq reflEq isContrEqSingl
