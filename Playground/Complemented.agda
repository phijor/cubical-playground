module Playground.Complemented where

open import Playground.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Functions.Embedding

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Unit as Unit

open import Cubical.Reflection.RecordEquiv

_∙ₑ_ = compEquiv

foo : 3 ≡ 3
foo = refl ∙ refl

_ = {! foo !}

open Iso

∂ : I → I
∂ i = i ∨ ~ i

kiteFiller : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → {p : x ≡ y}
  → {q : y ≡ z}
  → Square p q p q
kiteFiller {A = A} {x} {y} {z} {p} {q} = λ i j → hcomp (faces i j) y where
  faces : (i j k : I) → Partial (∂ i ∨ ∂ j) A
  faces i j k (i = i0) = p (j ∨ ~ k)
  faces i j k (i = i1) = q (j ∧ k)
  faces i j k (j = i0) = p (i ∨ ~ k)
  faces i j k (j = i1) = q (i ∧ k)

module _
  {ℓ} {X A B : Type ℓ}
  (u : A → X) (v : B → X) where

  infixr 5 _∩_

  record _∩_ : Type ℓ where
    constructor intersection
    field
      prl : A
      prr : B
      prl≡prr : u prl ≡ v prr

  unquoteDecl ∩-Σ-Iso = declareRecordIsoΣ ∩-Σ-Iso (quote _∩_)

  open _∩_

  _∩ˡ_ : _∩_ → X
  _∩ˡ_ = u ∘ prl

  _∩ʳ_ : _∩_ → X
  _∩ʳ_ = v ∘ prr

  ∩ˡ≡∩ʳ : _∩ˡ_ ≡ _∩ʳ_
  ∩ˡ≡∩ʳ = funExt prl≡prr

open _∩_

module _
  {ℓ} {X A B : Type ℓ}
  {u : A → X} {v : B → X} where

  ∩PathP : ∀ {a a′ : A} {b b′ : B}
    → (p : a ≡ a′)
    → (q : b ≡ b′)
    → {P : u a ≡ v b}
    → {Q : u a′ ≡ v b′}
    → PathP (λ i → u (p i) ≡ v (q i)) P Q
    → intersection a b P ≡ intersection a′ b′ Q
  ∩PathP p q PP = λ { i → intersection (p i) (q i) (PP i) }

  ∩-flip : u ∩ v → v ∩ u
  ∩-flip inter .prl = inter .prr
  ∩-flip inter .prr = inter .prl
  ∩-flip inter .prl≡prr = sym (inter .prl≡prr)

module _
  {ℓ} {X A B : Type ℓ}
  (u : A → X) (v : B → X) where

  ∩-flip-flip : (inter : u ∩ v) → ∩-flip (∩-flip inter) ≡ inter
  ∩-flip-flip inter = refl

  ∩-symm-iso : ∀ {ℓ} {X A B : Type ℓ} → Iso (u ∩ v) (v ∩ u)
  ∩-symm-iso .fun = ∩-flip
  ∩-symm-iso .inv = ∩-flip
  ∩-symm-iso .leftInv = λ _ → refl
  ∩-symm-iso .rightInv = λ _ → refl

  ∩-symm-equiv : (u ∩ v) ≃ (v ∩ u)
  ∩-symm-equiv = isoToEquiv ∩-symm-iso

∩-unitr-iso : ∀ {ℓ} {X A : Type ℓ}
  → (u : A → X)
  → Iso (u ∩ (idfun X)) A
∩-unitr-iso u .fun = prl
∩-unitr-iso u .inv = (λ a → intersection a (u a) refl)
∩-unitr-iso u .rightInv a = refl {x = a}
∩-unitr-iso u .leftInv (intersection _ _ p) = ∩PathP refl p kiteFiller

∅[_] : ∀ {ℓ} (A : Type ℓ) → ⊥* {ℓ = ℓ} → A
∅[ A ] ()

∩-annihr-iso : ∀ {ℓ} {X A : Type ℓ}
  → (u : A → X)
  → Iso (u ∩ ∅[ X ]) ⊥*
∩-annihr-iso u .fun = prr
∩-annihr-iso {X = X} u .inv ()
∩-annihr-iso u .rightInv ()
∩-annihr-iso u .leftInv (intersection _ () _)

∩-idem-iso : ∀ {ℓ} {X A : Type ℓ}
  → (u : A → X)
  → (isEmbedding u)
  → Iso (u ∩ u) A
∩-idem-iso u emb .fun (intersection l r p) = l
∩-idem-iso u emb .inv x = intersection x x refl
∩-idem-iso u emb .rightInv = λ _ → refl
∩-idem-iso u emb .leftInv (intersection l r p) = ∩PathP refl (emb-inv p) coh where
  emb-inv : u l ≡ u r → l ≡ r
  emb-inv = invIsEq (emb l r)

  p' : p ≡ (λ i → cong u (emb-inv p) i)
  p' = sym (secIsEq (emb l r) p)

  coh : Square
    (refl {x = u l}) p
    (refl {x = u l}) (cong u (emb-inv p))
  coh = subst {x = p} (λ q → Square refl p refl q) p' kiteFiller

module _ {ℓ} {X A B : Type ℓ}
  (f : X → A) (g : X → B) where

  data _⊔_ : Type ℓ where
    inl : (a : A) → _⊔_
    inr : (b : B) → _⊔_
    inl≡inr : (x : X) → inl (f x) ≡ inr (g x)

  _⊔ˡ_ : X → _⊔_
  _⊔ˡ_ = λ x → inl (f x)

  _⊔ʳ_ : X → _⊔_
  _⊔ʳ_ = λ x → inr (g x)

  ⊔ˡ≡⊔ʳ : _⊔ˡ_ ≡ _⊔ʳ_
  ⊔ˡ≡⊔ʳ = funExt inl≡inr

module _ {ℓ} {X A B : Type ℓ}
  {f : X → A} {g : X → B} where

  ⊔-elim : ∀ {ℓ′} {Y : f ⊔ g → Type ℓ′}
    → (inl* : ∀ a → Y (inl a))
    → (inr* : ∀ b → Y (inr b))
    → (inl≡inr* : ∀ x → PathP (λ i → Y (inl≡inr x i)) (inl* (f x)) (inr* (g x)))
    → (u : f ⊔ g) → Y u
  ⊔-elim {Y = Y} inl* inr* inl≡inr* = go where
    go : (u : f ⊔ g)  → Y u
    go (inl a) = inl* a
    go (inr b) = inr* b
    go (inl≡inr x i) = inl≡inr* x i

  ⊔-elimProp : ∀ {ℓ′} {P : f ⊔ g → Type ℓ′}
    → (∀ u → isProp (P u))
    → (inl* : ∀ a → P (inl a))
    → (inr* : ∀ b → P (inr b))
    → (u : f ⊔ g) → P u
  ⊔-elimProp {P = P} propP inl* inr* = ⊔-elim {Y = P} inl* inr*
    λ u → isProp→PathP
      {B = λ i → P (inl≡inr u i)}
      (λ i → propP (inl≡inr u i))
      (inl* (f u)) (inr* (g u))

  ⊔-rec : ∀ {ℓ′} {Y : Type ℓ′}
    → (inl* : A → Y)
    → (inr* : B → Y)
    → (inl≡inr* : ∀ x → inl* (f x) ≡ inr* (g x))
    → f ⊔ g → Y
  ⊔-rec = ⊔-elim

  ⊔-flip : f ⊔ g → g ⊔ f
  ⊔-flip (inl a) = inr a
  ⊔-flip (inr b) = inl b
  ⊔-flip (inl≡inr x i) = inl≡inr x (~ i)

module _ {ℓ} {X A B : Type ℓ}
  {f : X → A} {g : X → B} where

  ⊔-flip-flip : (u : f ⊔ g) → ⊔-flip (⊔-flip u) ≡ u
  ⊔-flip-flip = ⊔-elim (λ _ → refl) (λ _ → refl) (λ x i j → inl≡inr x i)

module _ {ℓ} {X A B : Type ℓ}
  (f : X → A) (g : X → B) where

  ⊔-symm-iso : Iso (f ⊔ g) (g ⊔ f)
  fun ⊔-symm-iso = ⊔-flip {f = f} {g = g}
  inv ⊔-symm-iso = ⊔-flip {f = g} {g = f}
  rightInv ⊔-symm-iso = ⊔-flip-flip
  leftInv ⊔-symm-iso = ⊔-flip-flip

  ⊔-symm-equiv = isoToEquiv ⊔-symm-iso

-- ⊔-congˡ-iso : ∀ {ℓ} {X A A′ B : Type ℓ}
--   → (f : X → A)
--   → (g : X → B)
--   → (e : A′ ≃ A)

_∪_ : ∀ {ℓ} {X S₁ S₂ : Type ℓ} → (s₁ : S₁ → X) (s₂ : S₂ → X) → Type _
_∪_ {S₁ = S₁} {S₂} s₁ s₂ = _⊔_ {X = s₁ ∩ s₂} {A = S₁} {B = S₂} (prl {u = s₁} {v = s₂}) (prr {u = s₁} {v = s₂})

module _ {ℓ} {X : Type ℓ}
  where
  ∪-flip : {S₁ S₂ : Type ℓ} {s₁ : S₁ → X} {s₂ : S₂ → X} → s₁ ∪ s₂ → s₂ ∪ s₁
  ∪-flip {s₁ = s₁} {s₂} = ⊔-rec inr inl λ inter → sym (inl≡inr (∩-flip inter))

  ∪-flip-flip : {S₁ S₂ : Type ℓ} {s₁ : S₁ → X} {s₂ : S₂ → X} → (u : s₁ ∪ s₂) → ∪-flip (∪-flip u) ≡ u
  ∪-flip-flip {s₁ = s₁} {s₂ = s₂} = ⊔-elim (λ _ → refl) (λ _ → refl) coh where
    coh : (u : s₁ ∩ s₂)
      → Square
        (refl {x = inl (prl u)})
        (refl {x = inr (prr u)})
        (inl≡inr (∩-flip (∩-flip u)))
        (inl≡inr u)
    coh (intersection _ _ p) =
      subst
        (λ q → Square refl refl q (inl≡inr (intersection _ _ p)))
        (cong inl≡inr (sym (∩-flip-flip _ _ _)))
        λ i j → inl≡inr (intersection _ _ p) i

  ∪-symm-iso : {S₁ S₂ : Type ℓ} (s₁ : S₁ → X) (s₂ : S₂ → X) → Iso (s₁ ∪ s₂) (s₂ ∪ s₁)
  ∪-symm-iso s₁ s₂ .fun = ∪-flip
  ∪-symm-iso s₁ s₂ .inv = ∪-flip
  ∪-symm-iso s₁ s₂ .rightInv = ∪-flip-flip
  ∪-symm-iso s₁ s₂ .leftInv = ∪-flip-flip

  ∪-symm-equiv : {S₁ S₂ : Type ℓ} (s₁ : S₁ → X) (s₂ : S₂ → X) → s₁ ∪ s₂ ≃ s₂ ∪ s₁
  ∪-symm-equiv s₁ s₂ = isoToEquiv (∪-symm-iso s₁ s₂)

module _ {ℓ} {X S₁ S₂ : Type ℓ} where
  record isComplementary (f : S₁ → X) (g : S₂ → X) : Type ℓ where
    field
      ∩-is-set : isSet (f ∩ g)
      ∪-is-tot : f ∪ g ≃ X

  isComplemented : (f : S₁ → X) → Type ℓ
  isComplemented f = Σ[ g ∈ (S₂ → X) ] isComplementary f g

module _ {ℓ} {X S₁ S₂ : Type ℓ}
  {f : S₁ → X} {g : S₂ → X} where
  open isComplementary

  isSymIsComplementary : isComplementary f g → isComplementary g f
  isSymIsComplementary c .∩-is-set = isOfHLevelRespectEquiv 2 (∩-symm-equiv _ _) (c .∩-is-set)
  isSymIsComplementary c .∪-is-tot = ∪-symm-equiv g f ∙ₑ c .∪-is-tot

module Example where
  open import Cubical.Data.Unit
  open import Cubical.Data.Bool

  open import Cubical.HITs.Susp

  data Iv : Type where
    left right : Iv
    path : left ≡ right

  Iv-rec : ∀ {ℓ} {A : Type ℓ}
    → {l r : A} → (l ≡ r)
    → Iv → A
  Iv-rec p left = p i0
  Iv-rec p right = p i1
  Iv-rec p (path i) = p i

  Iv-elim : ∀ {ℓ} {B : Iv → Type ℓ}
    → {l : B left}
    → {r : B right}
    → PathP (λ i → B (path i)) l r
    → (𝕚 : Iv) → B 𝕚
  Iv-elim p left = p i0
  Iv-elim p right = p i1
  Iv-elim p (path i) = p i

  Iv→true≡true : Iv → Bool
  Iv→true≡true = Iv-rec (refl {x = true})

  data S¹ : Type where
    north south : S¹
    east west : north ≡ south

  S¹-rec : ∀ {ℓ} {A : Type ℓ}
    → {n s : A}
    → (e w : n ≡ s)
    → S¹ → A
  S¹-rec {n = n} e w north = n
  S¹-rec {s = s} e w south = s
  S¹-rec e w (east i) = e i
  S¹-rec e w (west i) = w i

  rot : S¹ → S¹
  rot = S¹-rec (sym west) (sym east)

  f : Iv → S¹
  f = Iv-rec west

  g : Iv → S¹
  g = Iv-rec (sym east)

  to : f ∪ g → S¹
  to = ⊔-elim f g prl≡prr

  to-north : f ∩ g
  to-north = intersection left right (refl {x = north})

  to-south : f ∩ g
  to-south = intersection right left (refl {x = south})

  from : S¹ → f ∪ g
  from = S¹-rec {n = inl left} {s = inr left}
    (cong inl path ∙ inl≡inr to-south)
    (inl≡inr to-north ∙ cong inr (sym path))

  ∩-Bool-equiv : f ∩ g ≃ Bool
  ∩-Bool-equiv = isoToEquiv (iso toBool {! !} {! !} {! !}) where
    toBool : f ∩ g → Bool
    toBool (intersection l r p) = Iv-elim {B = λ ivl → (ivr : Iv) → f ivl ≡ g ivr → Bool}
      {l = Iv-elim {B = λ ivr → north ≡ g ivr → Bool} {l = {! !}} {r = {! !}} {! !}} {r = {! !}} {! !} l r p

  set-∩ : isSet (f ∩ g)
  set-∩ (intersection l r P) (intersection l′ r′ P′) p q = {!  !}

  _ : isComplementary f g
  _ = record
    { ∩-is-set = set-∩
    ; ∪-is-tot = to , {! !}
    }

