module Playground.Subgroupoid where

open import Playground.Prelude

open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fundamentalTheoremOfId)
open import Cubical.Functions.Embedding

data Subgroupoid {ℓA ℓP} (A : Type ℓA)
  (P : {a b : A} → a ≡ b → Type ℓP)
  : Type (ℓ-max ℓA ℓP) where

  [_] : (a : A) → Subgroupoid A P
  _∣_ : {a b : A} → (p : a ≡ b) → (res : P p) → [ a ] ≡ [ b ]

private
  variable
    ℓA ℓP : Level

module _ {A : Type ℓA} {P : {a b : A} → a ≡ b → Type ℓP} where
  rec : ∀ {ℓB} {B : Type ℓB} → (f : A → B) → Subgroupoid A P → B
  rec f [ a ] = f a
  rec f ((p ∣ res) i) = f (p i)

  rec2 : ∀ {ℓB} {B : Type ℓB} → (_·_ : A → A → B) → (x y : Subgroupoid A P) → B
  rec2 _·_ [ a ] [ b ] = a · b
  rec2 _·_ [ a ] ((q ∣ _) j) = a · q j
  rec2 _·_ ((p ∣ _) i) [ b ] = p i · b
  rec2 _·_ ((p ∣ _) i) ((q ∣ _) j) = p i · q j

  elim : ∀ {ℓB} {B : Subgroupoid A P → Type ℓB}
    → (f : (a : A) → B [ a ])
    → (well-def : ∀ {a b : A} → (p : a ≡ b) → (res : P p) → PathP (λ i → B ((p ∣ res) i)) (f a) (f b))
    → (x : Subgroupoid A P) → B x
  elim f well-def [ a ] = f a
  elim f well-def ((p ∣ res) i) = well-def p res i

  elimProp : ∀ {ℓB} {B : Subgroupoid A P → Type ℓB}
    → (propB : ∀ x → isProp (B x))
    → (f : (a : A) → B [ a ])
    → (x : Subgroupoid A P) → B x
  elimProp propB f = elim f λ {a} {b} p res → isProp→PathP (λ i → propB ((p ∣ res) i)) (f a) (f b)

  elim2 : ∀ {ℓB} {B : (x y : Subgroupoid A P) → Type ℓB}
    → (_·_ : (a₀ a₁ : A) → B [ a₀ ] [ a₁ ])
    → (well-def-left : ∀ {l₀ l₁ b} → (p : l₀ ≡ l₁) → (res : P p) → PathP (λ i → B ((p ∣ res) i) [ b ]) (l₀ · b) (l₁ · b))
    → (well-def-right : ∀ {r₀ r₁ a} → (p : r₀ ≡ r₁) → (res : P p) → PathP (λ i → B [ a ] ((p ∣ res) i)) (a · r₀) (a · r₁))
    → (x y : Subgroupoid A P) → B x y
  elim2 _·_ well-def-left well-def-right = elim (λ a₀ → elim (a₀ ·_) well-def-right)
    λ {a} {b} p res → funExt (elim (λ b → well-def-left {b = b} p res) {! !})

  ι : Subgroupoid A P → A
  ι = rec (idfun A)

  cong-ι : (x y : Subgroupoid A P) → Path (Subgroupoid A P) x y → Path A (ι x) (ι y)
  cong-ι x y = cong {x = x} {y = y} ι

module _ {A : Type ℓA} {P : {a b : A} → a ≡ b → Type ℓP}
  (propP : ∀ {a b} → (p : a ≡ b) → isProp (P p))
  (reflP : ∀ {a} → P (refl {x = a}))
  (compP : ∀ {a b c} → (p : a ≡ b) → (q : b ≡ c) → P p → P q → P (p ∙ q))
  where
  Code' : (a : A) → (y : Subgroupoid A P) → Type (ℓ-max ℓA ℓP)
  Code' a [ b ] = Σ (a ≡ b) P
  Code' a (_∣_ p res i) = Σ (a ≡ p i) P

  Code : (x y : Subgroupoid A P) → Type _
  Code = rec2 λ a b → Σ (a ≡ b) P

  reflCode : ∀ x → Code x x
  reflCode = elim
    (λ a → refl , reflP)
    λ {a} {b} (p : a ≡ b) (res : P p)
      → ΣPathP ((λ i → refl {x = p i}) , isProp→PathP (λ i → propP λ j → p i) reflP reflP)

  isContrCodeSingl : (x : Subgroupoid A P) → isContr (Σ[ y ∈ Subgroupoid A P ] Code x y)
  isContrCodeSingl x = (x , reflCode x) , uncurry (contr x) where
    contr : (x y : Subgroupoid A P) (c : Code x y) → (x , reflCode x) ≡ (y , c)
    contr = elim (λ { a → elim (λ { b (a≡b , P[a≡b]) → ΣPathP (cong [_] a≡b , {! !}) }) {! !} }) {! !}
    -- contr : (a : A) → isContr (Σ[ y ∈ Subgroupoid A P ] Code [ a ] y)
    -- contr a = ([ a ] , refl , reflP) , uncurry (elim {! !} {! !}) -- λ { (y , q) → ΣPathP ({! !} , Σ≡Prop propP {! !}) }

  -- encode : ∀ x y → x ≡ y → Code x y
  -- encode x _ = J (λ y _ → Code x y) (reflCode x)

  -- encodeRefl : ∀ x → encode x x refl ≡ reflCode x
  -- encodeRefl x = JRefl (λ y _ → Code x y) (reflCode x)

  -- decode' : ∀ c y → Code [ c ] y → [ c ] ≡ y
  -- decode' a [ b ] (p , res) = p ∣ res
  -- decode' a ((p ∣ res) i) = uncurry λ (α : a ≡ p i) hasP-α j → {! !}
  -- -- decode' c = elim (λ b → uncurry _∣_)
  -- --   λ {a} {b}
  -- --     → J (λ b (p : a ≡ b) → (res : P p) → PathP (λ i → Σ (c ≡ p i) P → [ c ] ≡ (p ∣ res) i) _ (uncurry _∣_)) {! !}

  -- decode : ∀ x y → Code x y → x ≡ y
  -- decode [ a ] [ b ] = uncurry _∣_
  -- decode [ a ] ((p ∣ res) i) = uncurry λ a≡pi has-P → {! !}
  -- decode ((p ∣ res) i) y c = {! !}

  Path≃Code : ∀ x y → (x ≡ y) ≃ (Code x y)
  Path≃Code = fundamentalTheoremOfId Code reflCode {! !}

  -- π : (x y : Subgroupoid A P) → Path A (ι x) (ι y) → Path (Subgroupoid A P) x y
  -- π = elim (λ (a : A) → elim {! !} {! !}) {! !}

  -- hasPropFibers-ι : ∀ {x y} → hasPropFibers (cong-ι x y)
  -- hasPropFibers-ι {x = x} {y = y} = {! !}
  -- -- hasPropFibers-ι c (x , ιx≡c) (y , ιy≡c) = uncurried x y ιx≡c ιy≡c where
  -- --   uncurried : (x y : Subgroupoid A P) → (p : ι x ≡ c) → (q : ι y ≡ c) → (x , p) ≡ (y , q)
  -- --   uncurried = elim (λ (a : A) → elim (λ (b : A) (p : a ≡ c) (q : b ≡ c) → ΣPathP (cong [_] (p ∙ sym q) , {! !})) {! !}) {! !}

  -- isEmbedding-ι : ∀ {x y} → isEmbedding (cong-ι x y)
  -- isEmbedding-ι = {! !}
