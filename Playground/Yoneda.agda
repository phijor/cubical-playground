module Playground.Yoneda where

open import Playground.Prelude using (Type)
open import Cubical.Functions.FunExtEquiv using (funExt₂)

module Path {ℓA ℓB}
  {A : Type ℓA}
  (B : A → Type ℓB)
  where
  open import Playground.Prelude
  open import Cubical.Foundations.Isomorphism

  elem : {x : A} → ((y : A) → x ≡ y → B y) → B x
  elem {x} η = η x refl

  よ : {x : A} → B x → ((y : A) → x ≡ y → B y)
  よ b _ p = subst B p b

  よ-Iso : {x : A} → Iso ((y : A) → x ≡ y → B y) (B x)
  よ-Iso .Iso.fun = elem
  よ-Iso .Iso.inv = よ
  よ-Iso .Iso.rightInv = transportRefl
  よ-Iso {x} .Iso.leftInv h = funExt₂ goal where
    goal : (y : A) (p : x ≡ y) → subst B p (h x refl) ≡ h y p
    goal y = J (λ y (p : x ≡ y) → subst B p (h x refl) ≡ h y p) (substRefl {B = B} (h x refl))

module Id {ℓA ℓB}
  {A : Type ℓA}
  (B : A → Type ℓB)
  where
  open import Playground.Prelude using (isContr ; refl′ ; _≡_ ; Path ; Square ; sym ; uncurry)
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Id using (Id ; refl ; J)
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.Sigma using (Σ ; _,_ ; ΣPathP)

  open Σ

  elem : {x : A} → ((y : A) → Id x y → B y) → B x
  elem {x} η = η x refl

  よ : {x : A} → B x → ((y : A) → Id x y → B y)
  よ {x} b y = J (λ y (p : Id x y) → B y) b

  よ-lemma : {x : A} → (η : (y : A) → Id x y → B y) → Path _ (よ (elem η)) η
  よ-lemma {x} η = funExt₂ λ y → J (λ y p → Path (B y) (よ (elem η) y p) (η y p)) (refl′ (η x refl))

  よ-compute : {x : A} → (b : B x) → Path (B x) (elem (よ b)) b
  よ-compute b = refl′ b

  よ-Iso : {x : A} → Iso ((y : A) → Id x y → B y) (B x)
  よ-Iso {x} = isom where
    open Iso
    isom : Iso _ _
    isom .fun = elem
    isom .inv = よ
    isom .rightInv = よ-compute
    isom .leftInv = よ-lemma

  よ-Equiv : {x : A} → ((y : A) → Id x y → B y) ≃ B x
  よ-Equiv = isoToEquiv よ-Iso
