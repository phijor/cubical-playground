module Playground.Categories where

open import Playground.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

_≡₁_ : ∀ {ℓ} {A : Type ℓ} → (x y : A) → Type _
x ≡₁ y = ∥ x ≡ y ∥₁

infix 4 _≡₁_

record MereCategory ℓob ℓhom : Type (ℓ-suc (ℓ-max ℓob ℓhom)) where
  field
    ob : Type ℓob
    Hom[_,_] : ob → ob → Type ℓhom
    id : ∀ {x} → Hom[ x , x ]
    _⋆_ : ∀ {x y z} → (f : Hom[ x , y ]) → (g : Hom[ y , z ]) → Hom[ x , z ]

    ⋆IdL : ∀ {x y} → (f : Hom[ x , y ]) → id ⋆ f ≡₁ f
    ⋆IdR : ∀ {x y} → (f : Hom[ x , y ]) → f ⋆ id ≡₁ f
    ⋆Assoc : ∀ {u v w x} (f : Hom[ u , v ]) (g : Hom[ v , w ]) (h : Hom[ w , x ]) → (f ⋆ g) ⋆ h ≡₁ f ⋆ (g ⋆ h)


module _ {ℓob ℓhom} where
  open import Cubical.Categories.Category
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

  open Iso

  MereCategory→Category : MereCategory ℓob ℓhom → Category ℓob ℓhom
  MereCategory→Category M = cat where
    cat : Category _ _
    cat .Category.ob = M .MereCategory.ob
    cat .Category.Hom[_,_] x y = ∥ M .MereCategory.Hom[_,_] x y ∥₂
    cat .Category.id = ∣ M .MereCategory.id ∣₂
    cat .Category._⋆_ = ST.rec2 ST.isSetSetTrunc λ { f g → ∣ M .MereCategory._⋆_ f g ∣₂ }
    cat .Category.⋆IdL = ST.elim (λ f → isProp→isSet (ST.isSetSetTrunc _ f)) (ST.PathIdTrunc₀Iso .inv ∘ M .MereCategory.⋆IdL)
    cat .Category.⋆IdR = ST.elim (λ f → isProp→isSet (ST.isSetSetTrunc _ f)) (ST.PathIdTrunc₀Iso .inv ∘ M .MereCategory.⋆IdR)
    cat .Category.⋆Assoc f g h = {! !}
    cat .Category.isSetHom = ST.isSetSetTrunc
