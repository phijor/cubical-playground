module Playground.Doubleton where

open import Playground.Prelude
open import Playground.Proposition

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Path as Path using (flipSquare)
open import Cubical.Foundations.Transport
open import Cubical.Functions.Image
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Bool as Bool using (Bool ; true ; false ; not) renaming (notEq to notPath)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ≡Prop ; map-×)
open import Cubical.Data.FinSet.Binary.Large
open import Cubical.HITs.PropositionalTruncation as PT using ()

private
  variable
    ℓ : Level
    X : Type ℓ

Doubleton : (X : Type ℓ) → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
Doubleton {ℓ = ℓ} X = Σ[ B ∈ Binary ℓ-zero ] (⟨ B ⟩ → X)

Doubleton≡ : {x y : Doubleton X}
  → (p : ⟨ x .fst ⟩ ≡ ⟨ y .fst ⟩)
  → (q : PathP (λ i → p i → X) (x .snd) (y .snd))
  → x ≡ y
Doubleton≡ p q = ΣPathP (Σ≡Prop (λ _ → PT.isPropPropTrunc) p , q)

-- swap : ∀ {ℓ} → Binary ℓ → Binary ℓ
-- swap (B , α) = B , PT.map (notEquiv ∙ₑ_) α

module Coequalizer {ℓA ℓB} {A : Type ℓA} {B : Type ℓB} (f g : A → B) where

  private
    variable
      ℓC : Level
      C : Type ℓC

  isCorelator : (p : B → C) → Type _
  isCorelator p = p ∘ f ≡ p ∘ g

  Corelator : (ℓC : Level) → Type _
  Corelator ℓC = Σ[ C ∈ Type ℓC ] Σ[ p ∈ (B → C) ] (isCorelator p)

  CorelatorMorphism : (c₀ c₁ : Corelator ℓC) → Type _
  CorelatorMorphism (C₀ , p₀ , corel-p₀) (C₁ , p₁ , corel-p₁) =
    Σ[ w ∈ (C₀ → C₁) ]
    Σ[ m ∈ (w ∘ p₀ ≡ p₁) ]
      PathP (λ i → m i ∘ f ≡ m i ∘ g) (cong (w ∘_) corel-p₀) corel-p₁

  isCoequalizer : (c : Corelator ℓC) → Type _
  isCoequalizer {ℓC = ℓC} c = (d : Corelator ℓC) → isContr $ CorelatorMorphism c d

module UnorderedPairs where
  swap : (X : Type ℓ) → (X × X) → (X × X)
  swap X (x , y) = (y , x)

  module _ (X : Type ℓ) where
    open Coequalizer (idfun (X × X)) (swap X)

    c : Corelator (ℓ-max (ℓ-suc ℓ-zero) ℓ)
    c = Doubleton X , proj , corel where
      pair : (X × X) → Bool → X
      pair (x , _) false = x
      pair (_ , y) true = y

      proj : X × X → Doubleton X
      proj (x , y) = Base , pair (x , y)

      swap-lemma : {x y : X} → (b : Bool) → pair (x , y) b ≡ pair (y , x) (not b)
      swap-lemma {x = x} false = refl′ x
      swap-lemma {y = y} true = refl′ y

      corel : isCorelator proj
      corel = funExt λ { (x , y) → Doubleton≡ notPath (funExtDep (goal x y)) } where
        module _ (x y : X) {b₀ b₁ : Bool} (p : PathP (λ i → notPath i) b₀ b₁) where
          p′ : not b₀ ≡ b₁
          p′ = fromPathP p
          
          goal : pair (x , y) b₀ ≡ pair (y , x) b₁
          goal =
            pair (x , y) b₀       ≡⟨ swap-lemma b₀ ⟩
            pair (y , x) (not b₀) ≡⟨ cong (pair (y , x)) p′ ⟩∎
            pair (y , x) b₁ ∎

    mediator : (d : Corelator _) → CorelatorMorphism c d
    mediator (D , q , corel-q) = map , {! !} where
      map : Doubleton X → D
      map ((B , ∣α∣) , f) = propImageElim' {A = Bool ≃ B} {B = (B → X) → D} go isPropImage-go ∣α∣ f where
        module _ {B : Type _} where
          go : (α : Bool ≃ B) → (f : B → X) → D
          go α f = q (x₀ , x₁) where
            f' : Bool → X
            f' = f ∘ equivFun α

            x₀ x₁ : X
            x₀ = f' false
            x₁ = f' true

          isPropImage-go : isProp (Image go)
          isPropImage-go (d₀ , im₀) (d₁ , im₁) = Σ≡Prop (isPropIsInImage go) goal where
            goal : d₀ ≡ d₁
            goal = {! !}

    isCoequalizerDoubleton : isCoequalizer c
    isCoequalizerDoubleton d = mediator d , {! !}

module BoolCoequalizer where
  open Coequalizer (idfun Bool) not

  c : Corelator _
  c = Unit , (λ _ → tt) , refl

  mediator : (d : Corelator _) → CorelatorMorphism c d
  mediator (D , q , corel-q) = (λ (_ : Unit) → q true) , funExt (q≡const corel-q) , (sq-filler corel-q) where
    module _ (corel-q : _) where
      q≡const : (b : Bool) → q true ≡ q b
      q≡const false = funExt⁻ corel-q true
      q≡const true = refl

      lemma : funExt q≡const ∙ corel-q ≡ funExt (q≡const ∘ not)
      lemma i j false = {! !}
      lemma i j true = {! !}

      sq-filler : PathP (λ i → funExt q≡const i ≡ funExt (q≡const ∘ not) i) (refl′ λ _ → q true) corel-q
      sq-filler = flipSquare (transport⁻ (Path.PathP≡compPath (funExt q≡const) corel-q (funExt (q≡const ∘ not))) lemma)

  isCoequalizer-c : isCoequalizer c
  isCoequalizer-c d = mediator d , {! !}
