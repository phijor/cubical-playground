module Playground.WeightedSet where

open import Playground.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Algebra.CommMonoid

private
  variable
    ℓ : Level
    A : Type ℓ

module _ {ℓM} (Mon : CommMonoid ℓM) where
  M : Type ℓM
  M = ⟨ Mon ⟩
  open module M = CommMonoidStr (str Mon) renaming (_·_ to _+_ ; ε to 0m)

  data FMSet {ℓ} (A : Type ℓ) : Type (ℓ-max ℓM ℓ) where
    ⟅_∶_⟆ : (a : A) → (m : M) → FMSet A
    _∪_ : (xs ys : FMSet A) → FMSet A

    ∪IdL :
      (xs : FMSet A) (a : A)
      ----------------------
      → ⟅ a ∶ 0m ⟆ ∪ xs ≡ xs

    ∪IdR :
      (xs : FMSet A) (a : A)
      ----------------------
      → xs ∪ ⟅ a ∶ 0m ⟆ ≡ xs

    ∪Comm :
      (xs ys : FMSet A)
      -------------------
      → xs ∪ ys ≡ ys ∪ xs

    ∪Assoc :
      (xs ys zs : FMSet A)
      --------------------
      → xs ∪ (ys ∪ zs) ≡ (xs ∪ ys) ∪ zs

    ∪Idem :
      (a : A) (m n : M)
      ---------------------------------------
      → ⟅ a ∶ m ⟆ ∪ ⟅ a ∶ n ⟆ ≡ ⟅ a ∶ m + n ⟆

    isSetFMSet : isSet (FMSet A)

  module _ {ℓ'} {B : FMSet A → Type ℓ'}
    (setB : ∀ xs → isSet (B xs))
    (⟅_∶_⟆* : (a : A) → (m : M) → B ⟅ a ∶ m ⟆)
    (_∪*_ : ∀ {xs ys} → B xs → B ys → B (xs ∪ ys))
    (∪*IdL : ∀ {xs} → (b : B xs) (a : A) → PathP (λ i → B (∪IdL xs a i)) (⟅ a ∶ 0m ⟆* ∪* b) b)
    (∪*IdR : ∀ {xs} → (b : B xs) (a : A) → PathP (λ i → B (∪IdR xs a i)) (b ∪* ⟅ a ∶ 0m ⟆*) b)
    (∪*Comm : ∀ {xs ys} → (b : B xs) (c : B ys) → PathP (λ i → B (∪Comm xs ys i)) (b ∪* c) (c ∪* b))
    (∪*Assoc : ∀ {xs ys zs} → (b : B xs) (c : B ys) (d : B zs) → PathP (λ i → B (∪Assoc xs ys zs i)) (b ∪* (c ∪* d)) ((b ∪* c) ∪* d))
    (∪*Idem : (a : A) (m n : M) → PathP (λ i → B (∪Idem a m n i)) (⟅ a ∶ m ⟆* ∪* ⟅ a ∶ n ⟆*) ⟅ a ∶ m + n ⟆*)
    where

    elim : (xs : FMSet A) → B xs
    elim ⟅ a ∶ m ⟆ = ⟅ a ∶ m ⟆*
    elim (xs ∪ ys) = elim xs ∪* elim ys
    elim (∪IdL xs a i) = ∪*IdL (elim xs) a i
    elim (∪IdR xs a i) = ∪*IdR (elim xs) a i
    elim (∪Comm xs ys i) = ∪*Comm (elim xs) (elim ys) i
    elim (∪Assoc xs ys zs i) = ∪*Assoc (elim xs) (elim ys) (elim zs) i
    elim (∪Idem a m n i) = ∪*Idem a m n i
    elim (isSetFMSet xs ys p q i j) = setB' (elim xs) (elim ys) (cong elim p) (cong elim q) (isSetFMSet xs ys p q) i j where
      setB' : isOfHLevelDep 2 B
      setB' = isOfHLevel→isOfHLevelDep 2 setB

  module _ {ℓ'} {P : FMSet A → Type ℓ'}
    (propP : ∀ xs → isProp (P xs))
    (⟅_∶_⟆* : (a : A) → (m : M) → P ⟅ a ∶ m ⟆)
    (_∪*_ : ∀ {xs ys} → P xs → P ys → P (xs ∪ ys))
    where

    elimProp : (xs : FMSet A) → P xs
    elimProp = elim {B = P} (isProp→isSet ∘ propP) ⟅_∶_⟆* _∪*_ ∪*IdL ∪*IdR ∪*Comm ∪*Assoc ∪*Idem where
      propP' : isOfHLevelDep 1 P
      propP' = isOfHLevel→isOfHLevelDep 1 propP

      ∪*IdL : ∀ {xs} → (b : P xs) (a : A) → PathP (λ i → P (∪IdL xs a i)) _ _
      ∪*IdL b a = propP' _ _ (∪IdL _ a)

      ∪*IdR : ∀ {xs} → (b : P xs) (a : A) → PathP (λ i → P (∪IdR xs a i)) _ _
      ∪*IdR b a = propP' _ _ (∪IdR _ a)

      ∪*Comm : ∀ {xs ys} → (b : P xs) (c : P ys) → PathP (λ i → P (∪Comm xs ys i)) (b ∪* c) (c ∪* b)
      ∪*Comm b c = propP' _ _ (∪Comm _ _)

      ∪*Assoc : ∀ {xs ys zs} → (b : P xs) (c : P ys) (d : P zs) → PathP (λ i → P (∪Assoc xs ys zs i)) _ _
      ∪*Assoc b c d = propP' _ _ (∪Assoc _ _ _)

      ∪*Idem : (a : A) (m n : M) → PathP (λ i → P (∪Idem a m n i)) (⟅ a ∶ m ⟆* ∪* ⟅ a ∶ n ⟆*) ⟅ a ∶ m + n ⟆*
      ∪*Idem a m n = propP' _ _ (∪Idem a m n)
      

  module _ {ℓ'} {B : Type ℓ'}
    (setB : isSet B)
    (⟅_∶_⟆* : (a : A) → (m : M) → B)
    (_∪*_ : B → B → B)
    (∪*IdL : (b : B) (a : A) → ⟅ a ∶ 0m ⟆* ∪* b ≡ b)
    (∪*IdR : (b : B) (a : A) → b ∪* ⟅ a ∶ 0m ⟆* ≡ b)
    (∪*Comm : (b c : B) → b ∪* c ≡ c ∪* b)
    (∪*Assoc : (b c d : B) → b ∪* (c ∪* d) ≡ (b ∪* c) ∪* d)
    (∪*Idem : (a : A) (m n : M) → ⟅ a ∶ m ⟆* ∪* ⟅ a ∶ n ⟆* ≡ ⟅ a ∶ m + n ⟆*)
    where

    rec : FMSet A → B
    rec ⟅ a ∶ m ⟆ = ⟅ a ∶ m ⟆*
    rec (xs ∪ ys) = rec xs ∪* rec ys
    rec (∪IdL xs a i) = ∪*IdL (rec xs) a i
    rec (∪IdR xs a i) = ∪*IdR (rec xs) a i
    rec (∪Comm xs ys i) = ∪*Comm (rec xs) (rec ys) i
    rec (∪Assoc xs ys zs i) = ∪*Assoc (rec xs) (rec ys) (rec zs) i
    rec (∪Idem a m n i) = ∪*Idem a m n i
    rec (isSetFMSet xs ys p q i j) = setB (rec xs) (rec ys) (cong rec p) (cong rec q) i j


  module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    (f : A → B)
    where

    map : FMSet A → FMSet B
    map ⟅ a ∶ m ⟆ = ⟅ f a ∶ m ⟆
    map (xs ∪ ys) = map xs ∪ map ys
    map (∪IdL xs a i) = ∪IdL (map xs) (f a) i
    map (∪IdR xs a i) = ∪IdR (map xs) (f a) i
    map (∪Comm xs ys i) = ∪Comm (map xs) (map ys) i
    map (∪Assoc xs ys zs i) = ∪Assoc (map xs) (map ys) (map zs) i
    map (∪Idem a m n i) = ∪Idem (f a) m n i
    map (isSetFMSet xs ys p q i j) = isSetFMSet (map xs) (map ys) (cong map p) (cong map q) i j


  module _ {ℓ} {A : Type ℓ} where
    mapId : map (idfun A) ≡ idfun (FMSet A)
    mapId = funExt (elimProp (λ xs → isSetFMSet _ _) (λ a m → refl) λ p q → cong₂ _∪_ p q)

  mapComp : ∀ {ℓA ℓB ℓC} {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
    → (g : B → C) → (f : A → B)
    → map (g ∘ f) ≡ map g ∘ map f
  mapComp g f = funExt (elimProp (λ _ → isSetFMSet _ _) (λ _ _ → refl) λ p q → cong₂ _∪_ p q)
