module Playground.EquivToFamily where

open import Playground.Prelude
open import Playground.Square

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma using (∃-syntax ; ΣPathP ; Σ≡Prop ; ΣPathPProp ; map-snd ; Σ-cong-equiv-snd ; _×_ ; Σ-contractFst)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

module EquivToFamily {ℓ} {ℓ'} {A : Type ℓ} (B : A → Type ℓ') where
  private
    transportU : {x y : A} → x ≡ y → B x → B y
    transportU p = transport (cong B p)

    pathToEquivU : ∀ {x y} → x ≡ y → B x ≃ B y
    pathToEquivU p .fst = transportU p
    pathToEquivU p .snd = isEquivTransport (cong B p)

  isUnivalent : Type (ℓ-max ℓ ℓ')
  isUnivalent = ∀ {x y : A} → isEquiv (pathToEquivU {x} {y})

  fiber≃ : (X : Type ℓ') → Type (ℓ-max ℓ ℓ')
  fiber≃ X = Σ[ a ∈ A ] B a ≃ X

  isConnectedTo : (X : Type ℓ') → Type (ℓ-max ℓ ℓ')
  isConnectedTo X = ∥ fiber≃ X ∥₁

  fiber≃→isConnectedTo : ∀ {X} → fiber≃ X → isConnectedTo X
  fiber≃→isConnectedTo = ∣_∣₁

  isPropIsConnectedTo : (X : Type ℓ') → isProp (isConnectedTo X)
  isPropIsConnectedTo _ = PT.isPropPropTrunc

  Connected : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Connected = TypeWithStr ℓ' isConnectedTo

  Connected≡ : {S T : Connected} → ⟨ S ⟩ ≡ ⟨ T ⟩ → S ≡ T
  Connected≡ = Σ≡Prop isPropIsConnectedTo

  ConnectedElimProp : ∀ {ℓP} {P : Connected → Type ℓP}
    → (∀ S → isProp (P S))
    → ((a : A) → P (B a , ∣ a , idEquiv (B a) ∣₁))
    → (S : Connected) → P S
  ConnectedElimProp {P = P} propP base =
    uncurry λ (X : Type _) → PT.elim (λ { ∣fib≃∣ → propP (X , ∣fib≃∣) }) (uncurry goal)
    where module _ {X : Type _} (a : A) (α : B a ≃ X) where
      substPath : (B a , _) ≡ (X , _)
      substPath = Connected≡ (ua α)

      goal : P (X , ∣ a , α ∣₁)
      goal = subst P substPath (base a)

  isConnectedInFiber : (X : Type ℓ') → Type (ℓ-max ℓ ℓ')
  isConnectedInFiber X = Σ[ a ∈ A ] ∥ B a ≃ X ∥₁

  fiber≃→isConnectedInFiber : ∀ {X} → fiber≃ X → isConnectedInFiber X
  fiber≃→isConnectedInFiber = map-snd ∣_∣₁

  isConnectedInFiber≡ : {X : Type ℓ'} → {h₁ h₂ : isConnectedInFiber X} → h₁ .fst ≡ h₂ .fst → h₁ ≡ h₂
  isConnectedInFiber≡ = Σ≡Prop λ _ → PT.isPropPropTrunc

  FiberConnected : Type (ℓ-max ℓ (ℓ-suc ℓ'))
  FiberConnected = TypeWithStr ℓ' isConnectedInFiber

  FiberConnected≡ : {x y : FiberConnected}
    → (ty-path : ⟨ x ⟩ ≡ ⟨ y ⟩)
    → (fib-path : Path A (str x .fst) (str y .fst))
    → x ≡ y
  FiberConnected≡ ty-path fib-path = ΣPathP (ty-path , ΣPathPProp (λ _ → PT.isPropPropTrunc) fib-path)

  isConnectedInFiber→isConnectedTo : ∀ {X} → isConnectedInFiber X → isConnectedTo X
  isConnectedInFiber→isConnectedTo {X = X} = uncurry λ a → PT.map (a ,_)

  ∥isConnectedInFiber∥≃isConnectedTo : ∀ X → ∥ isConnectedInFiber X ∥₁ ≃ isConnectedTo X
  ∥isConnectedInFiber∥≃isConnectedTo X = propBiimpl→Equiv
    PT.isPropPropTrunc
    (isPropIsConnectedTo X)
    (PT.rec (isPropIsConnectedTo X) isConnectedInFiber→isConnectedTo)
    (PT.map fiber≃→isConnectedInFiber)

  module PropConnectedInFiber (prop : ∀ X → isProp (isConnectedInFiber X)) where
    isConnectedTo→isConnectedInFiber : ∀ {X} → isConnectedTo X → isConnectedInFiber X
    isConnectedTo→isConnectedInFiber {X} = PT.rec (prop X) fiber≃→isConnectedInFiber

    isConnectedInFiber≃isConnectedTo : ∀ X → isConnectedInFiber X ≃ isConnectedTo X
    isConnectedInFiber≃isConnectedTo X = propBiimpl→Equiv
      (prop X)
      (isPropIsConnectedTo X)
      isConnectedInFiber→isConnectedTo
      isConnectedTo→isConnectedInFiber

    FiberConnected≃Connected : FiberConnected ≃ Connected
    FiberConnected≃Connected = Σ-cong-equiv-snd isConnectedInFiber≃isConnectedTo

  module InjFam (setA : isSet A) (injB : (x y : A) → B x ≡ B y → x ≡ y) where
    isPropIsConnectedInFiber : (X : Type ℓ') → isProp (isConnectedInFiber X)
    isPropIsConnectedInFiber X (x , ∣α∣) (y , ∣β∣) = isConnectedInFiber≡ goal where
      lem : (α : B x ≃ X) (β : B y ≃ X) → x ≡ y
      lem α β = injB x y (ua γ) where
        γ : B x ≃ B y
        γ = α ∙ₑ invEquiv β

      goal : x ≡ y
      goal = PT.rec2 (setA x y) lem ∣α∣ ∣β∣

    open PropConnectedInFiber isPropIsConnectedInFiber public

  module ContrIndex (contrA : isContr A) where
    isPropIsConnectedInFiber : (X : Type ℓ') → isProp (isConnectedInFiber X)
    isPropIsConnectedInFiber X = isOfHLevelRespectEquiv 1 (invEquiv (Σ-contractFst contrA)) PT.isPropPropTrunc

    open PropConnectedInFiber isPropIsConnectedInFiber public

  module UnivalentFamily (univ : isUnivalent) where
    isPropIsConnectedInFiber : (X : Type ℓ') → isProp (isConnectedInFiber X)
    isPropIsConnectedInFiber X (x , ∣α∣) (y , ∣β∣) = isConnectedInFiber≡ goal where
      lem : B x ≃ B y
      lem = {! !}

      goal : x ≡ y
      goal = invIsEq (univ {x} {y}) lem

    open PropConnectedInFiber isPropIsConnectedInFiber public
    

  module EmbFam (embB : isEmbedding B) where
    isPropIsConnectedInFiber : (X : Type ℓ') → isProp (isConnectedInFiber X)
    isPropIsConnectedInFiber X (x , ∣α∣) (y , ∣β∣) = isConnectedInFiber≡ goal where
      Factorization : Type _
      Factorization = Σ[ (α , β , γ) ∈ ((B x ≃ X) × (X ≃ B y) × (B x ≃ B y)) ] γ ≡ α ∙ₑ β

      Pull = Σ[ γ ∈ B x ≡ B y ] Σ[ p ∈ x ≡ y ] invIsEq (embB x y) γ ≡ p

      isPropFactorization : isProp Factorization
      isPropFactorization ((α₁ , β₁ , γ₁) , p₁) ((α₂ , β₂ , γ₂) , p₂) = {! !}

      propFib : ∀ Y → isProp (fiber B Y)
      propFib = isEmbedding→hasPropFibers embB
      open import Playground.Proposition

      module _ (α : B x ≃ X) (β : B y ≃ X) where
        γ : B x ≃ B y
        γ = α ∙ₑ invEquiv β

      propLemma : (p q : B x ≡ B y) → p ≡ q
      propLemma p q = goal where
        open import Cubical.Data.Sigma.Properties using (PathPΣ)
        p' : fiber B (B y)
        p' = x , p

        q' : fiber B (B y)
        q' = x , q

        step : p' ≡ q'
        step = propFib (B y) p' q'

        goal : p ≡ q
        goal = {! PathPΣ step!}

      _ = {!propImageElim {A = (B x ≃ X) × (B y ≃ X)} {B = B x ≡ B y} !}

      ∥Bx≡By∥ : ∥ B x ≡ B y ∥₁
      ∥Bx≡By∥ = PT.map2 (λ α β → ua (γ α β)) ∣α∣ ∣β∣

      goal : x ≡ y
      goal = invIsEq (embB x y) {! !}

  -- Assuming `isConnectedInFiber→isConnectedTo` is an equivalence...
  module _ (equiv : ∀ X → isEquiv (isConnectedInFiber→isConnectedTo {X})) where
    -- 1) B is (merely?) injective:
    isMerelyInjectiveFam : (x y : A) → ∥ B x ≡ B y ∥₁ → x ≡ y
    isMerelyInjectiveFam x y ∣p∣ = cong fst goal where
      Bx≃By : isConnectedInFiber (B y)
      Bx≃By = x , PT.map pathToEquiv ∣p∣

      By≃By : isConnectedInFiber (B y)
      By≃By = y , ∣ idEquiv (B y) ∣₁

      isProp-isConnectedInFiberBx : ∀ {z} → isProp (isConnectedInFiber (B z))
      isProp-isConnectedInFiberBx {z} =
        isPropRetract
          isConnectedInFiber→isConnectedTo
          inv
          retr
          (isPropIsConnectedTo (B z))
        where
          inv : isConnectedTo (B z) → isConnectedInFiber (B z)
          inv = invIsEq (equiv (B z))

          retr : retract isConnectedInFiber→isConnectedTo inv
          retr = retIsEq (equiv (B z))

      goal : Bx≃By ≡ By≃By
      goal = isProp-isConnectedInFiberBx Bx≃By By≃By


    isInjectiveFam : (x y : A) → B x ≡ B y → x ≡ y
    isInjectiveFam x y = isMerelyInjectiveFam x y ∘ ∣_∣₁

    -- 2) is A a set?
    isSetBase : isSet A
    isSetBase x y = {! !}

    -- 3) B is an embedding?
    isEmbeddingFam : isEmbedding B
    isEmbeddingFam x y = goal where
      goal : isEquiv (λ (p : x ≡ y) → cong B p)
      goal .equiv-proof = isCtrFib where
        module _ (q : B x ≡ B y) where
          center : fiber (cong B) q
          center = isInjectiveFam x y q , {! !}

          isCtrFib : isContr (fiber (cong B) q)
          isCtrFib = center , {! !}

-- open import Playground.Universe.Base using (Universe)

-- module UnivalenceSmall {ℓ} (V : Univalence ℓ) where
--   open EquivToFamily

--   U : Type (ℓ-suc ℓ)
--   U = Connected B

--   El : U → Type ℓ
--   El = ⟨_⟩

--   uaU : (X Y : U) → El X ≃ El Y → X ≡ Y
--   uaU _ _ α = Connected≡ B (ua α)

--   uaU-comp : {X Y : U} (α : El X ≃ El Y) → cong El (uaU X Y α) ≡ ua α
--   uaU-comp α = refl

--   module UU = UnivalentUniverse U El uaU uaU-comp

--   pathToEquivU : (X Y : U) → X ≡ Y → El X ≃ El Y
--   pathToEquivU X Y p = pathToEquiv (cong El p)

--   minivalence : ∀ {X Y} → (X ≡ Y) ≃ (El X ≃ El Y)
--   minivalence = UU.minivalence

--   isUnivalentConnected : (S T : U) → isEquiv (pathToEquivU S T)
--   isUnivalentConnected S T = minivalence .snd

module Foo where
  open import Cubical.Functions.Image
  open import Cubical.Data.Sigma
  open import Cubical.Data.Bool
  open import Cubical.Data.FinSet.Binary.Large renaming (Base to Bool₂)
  open import Playground.Proposition

  _,,Bool_ : {A : Type} → (x y : A) → Bool → A
  (x ,,Bool y) false = x
  (x ,,Bool y) true = y

  U₂ = Binary ℓ-zero

  Pair : (A : Type) → Type₁
  Pair A = Σ[ B ∈ U₂ ] (⟨ B ⟩ → A)

  Idx : ∀ {A} → Pair A → Type
  Idx p = p .fst .fst

  Binary≡ : {A : Type} {p₁ p₂ : Pair A}
    → (α : Idx p₁ ≃ Idx p₂)
    → (eq : (k : Idx p₁) → p₁ .snd k ≡ p₂ .snd (equivFun α k))
    → p₁ ≡ p₂
  Binary≡ α eq = ΣPathP (Σ≡Prop (λ _ → PT.isPropPropTrunc) (ua α) , ua→ eq)

  swap≡ : {A : Type} {f g : Bool → A}
    → (eq : f ≡ g ∘ not)
    → Path (Pair A) (Bool₂ , f) (Bool₂ , g)
  swap≡ eq = Binary≡ notEquiv (funExt⁻ eq)

  module _ {A : Type} (x y : A) where
    p : Bool → A
    p = λ {true → x ; false → y}

    q : Bool → A
    q = p ∘ not

    x,y : Pair A
    x,y = Bool₂ ,
      λ where
        true → x
        false → y

    y,x : Pair A
    y,x = Bool₂ ,
      λ where
        true → y
        false → x

    x,y≡y,x : x,y ≡ y,x
    x,y≡y,x = swap≡ $ funExt λ { true → refl′ (p true) ; false → refl′ (p false) }

  swap-U₂ : U₂ → U₂
  swap-U₂ = map-snd (PT.map (notEquiv ∙ₑ_))

  swap-U₂≡ : (B : U₂) → B ≡ swap-U₂ B
  swap-U₂≡ B = Σ≡Prop (λ _ → PT.isPropPropTrunc) refl

  swap : {A : Type} → Pair A → Pair A
  swap (B , f) = swap-U₂ B , f

  
  lem : {A : Type} → (f : Pair A) → f ≡ swap f
  lem (B , f) = ΣPathP (swap-U₂≡ B , refl′ f)

  -- _,,_ : {A : Type} → (x y : A) → (Y : Binary ℓ-zero) → ⟨ Y ⟩ → A
  -- _,,_ {A} x y = uncurry λ Y → propImageElim' f propIm where
  --   f : ∀ {Y} (α : Bool ≃ Y) → (y : Y) → A
  --   f α = (x ,,Bool y) ∘ invEq α

  --   propIm : ∀ {Y} → isProp (Image (f {Y}))
  --   propIm (g , g∈Im[f]) (g' , g'∈Im[f]) =
      -- Σ≡Prop (λ _ → PT.isPropPropTrunc) (funExt λ y → {! !})

module Example where
  open import Cubical.HITs.S1 as S1
  open import Cubical.Data.Bool
  open import Cubical.Data.Unit
  open import Cubical.Data.Sigma
  open import Cubical.Relation.Nullary.Base using (¬_)

  B : S¹ → Type
  B base = Bool
  B (loop i) = notEq i

  open EquivToFamily B

  ¬isPropIsConnectedInFiber-S¹ : ¬ (∀ X → isProp (isConnectedInFiber X))
  ¬isPropIsConnectedInFiber-S¹ prop = true≢false {! !} where
    lem : (base , ∣ idEquiv Bool ∣₁) ≡ (base , ∣ notEquiv ∣₁)
    lem = prop Bool (base , ∣ idEquiv Bool ∣₁) (base , ∣ notEquiv ∣₁)

    refl≡loop : refl ≡ loop
    refl≡loop = {!isSet→SquareP !}

    true≡false : true ≡ false
    true≡false = {!PathPΣ lem !}

  -- isPropIsConnectedInFiber-S¹ : (X : Type) → isProp (isConnectedInFiber X)
  -- isPropIsConnectedInFiber-S¹ X (s₀ , ∣α∣) (s₁ , ∣β∣) = goal s₀ s₁ ∣α∣ ∣β∣ where
  --   coh-sq : {α β γ δ : ∥ X ≃ Bool ∥₁}
  --     → PathP (λ _ → ∥ X ≃ Bool ∥₁) α β
  --     → PathP (λ i → ∥ X ≃ (notEq i) ∥₁) γ δ
  --     → Square (λ i → base) (λ i → base) (λ i → base) loop
  --   coh-sq p q = λ i j → hcomp {! !} {! !}

  --   step : (s₁ : S¹) → (∣α∣ : ∥ X ≃ Bool ∥₁) (∣β∣ : ∥ X ≃ B s₁ ∥₁) → (base , ∣α∣) ≡ (s₁ , ∣β∣)
  --   step = S1.elim _
  --     (λ _ _ → isConnectedInFiber≡ (refl {x = base}))
  --     (funExtDep λ ∣equiv∣-path₁ → funExtDep λ ∣equiv∣-path₂ → ΣSquarePProp (λ _ → PT.isPropPropTrunc) (coh-sq ∣equiv∣-path₁ ∣equiv∣-path₂))

  --   goal : (s₀ s₁ : S¹) → (∣α∣ : ∥ X ≃ B s₀ ∥₁) (∣β∣ : ∥ X ≃ B s₁ ∥₁) → (s₀ , ∣α∣) ≡ (s₁ , ∣β∣)
  --   goal = S1.elim (λ s₀ → (s₁ : S¹) → _)
  --     step
  --     (funExtDep {! !})

  -- isConnectedTo→isConnectedInFiber' : ∀ {X} → isConnectedTo X → isConnectedInFiber X
  -- isConnectedTo→isConnectedInFiber' {X = X} conn = {! !}

open EquivToFamily public
