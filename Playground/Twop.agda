module Playground.Twop where
open import Playground.Prelude

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.Data.Bool using (Bool ; false ; true ; false≢true)
open import Cubical.Relation.Nullary
  using
    ( ¬_
    ; isProp¬
    )

private
  variable
    ℓ : Level
    A : Type ℓ

record TwopointedStr {ℓ} (A : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    𝟘 𝟙 : A
    𝟘≢𝟙 : ¬ (𝟘 ≡ 𝟙)

open TwopointedStr

TwopointedStr≡ : {b₀ b₁ : TwopointedStr A} (open TwopointedStr)
  → (p₀ : b₀ .𝟘 ≡ b₁ .𝟘)
  → (p₁ : b₀ .𝟙 ≡ b₁ .𝟙)
  → b₀ ≡ b₁
TwopointedStr≡ p₀ p₁ i .𝟘 = p₀ i
TwopointedStr≡ p₀ p₁ i .𝟙 = p₁ i
TwopointedStr≡ {b₀ = b₀} {b₁} p₀ p₁ i .𝟘≢𝟙 = isProp→PathP {B = λ i → ¬ p₀ i ≡ p₁ i} (λ _ → isProp¬ _) (b₀ .𝟘≢𝟙) (b₁ .𝟘≢𝟙) i

Twopointed : (ℓ : Level) → Type (ℓ-suc ℓ)
Twopointed ℓ = TypeWithStr ℓ TwopointedStr

TwopointedStrBool : TwopointedStr Bool
TwopointedStrBool .𝟘 = false
TwopointedStrBool .𝟙 = true
TwopointedStrBool .𝟘≢𝟙 = false≢true

module _ {ℓA ℓB : Level} where
  open import Cubical.Data.Unit

  open TwopointedStr

  module _ {A : Type ℓA} {B : Type ℓB} where
    data [_⌣_] (a : A) (b : B) : Type (ℓ-max ℓA ℓB) where
      inl : A → [ a ⌣ b ]
      inr : B → [ a ⌣ b ]
      push : inl a ≡ inr b

    module _ {a· : A} {b· : B} where
      _≈_ : (r s : [ a· ⌣ b· ]) → Type (ℓ-max ℓA ℓB)
      inl a₀ ≈ inl a₁ = Lift (a₀ ≡ a₁)
      inl a₀ ≈ inr b₁ = Σ (a₀ ≡ a·) (λ _ → b₁ ≡ b·)
      inl a₀ ≈ push i = {! !}
      inr b₀ ≈ s = {! !}
      push i ≈ s = {! !}

      -- encode : {r s : [ a· ⌣ b· ]} → r ≡ s → r ≈ s
      -- encode {r} {s} = J (λ s (p : r ≡ s) → r ≈ s) {! !}

      ¬[⌣] : ∀ {a b}
        → (p : ¬ (a ≡ a·))
        → (q : ¬ (b ≡ b·))
        → ¬ (Path [ a· ⌣ b· ] (inl a) (inr b))
      ¬[⌣] p q = {! !}

    TwopointedStr⌣ : (biA : TwopointedStr A) (biB : TwopointedStr B)
      → TwopointedStr [ biA .𝟙 ⌣ biB .𝟘 ]
    TwopointedStr⌣ biA biB .𝟘 = inl $ biA .𝟘
    TwopointedStr⌣ biA biB .𝟙 = inr $ biB .𝟙
    TwopointedStr⌣ biA biB .𝟘≢𝟙 = goal where
      goal : ¬ (inl (biA .𝟘) ≡ inr (biB .𝟙))
      goal = ¬[⌣] (biA .𝟘≢𝟙) (biB .𝟘≢𝟙 ∘ sym)


  _⌣_ : Twopointed ℓA → Twopointed ℓB → Twopointed (ℓ-max ℓA ℓB)
  (A ⌣ B) .fst = [ str A .𝟙 ⌣ str B .𝟘 ]
  (A ⌣ B) .snd = TwopointedStr⌣ (str A) (str B)

2·_ : ∀ {ℓA} → Twopointed ℓA → Twopointed ℓA
2· A = A ⌣ A
