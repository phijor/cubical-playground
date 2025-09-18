{-# OPTIONS --hidden-argument-puns #-}
module Playground.DerivativeIsolated where

open import Playground.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Univalence.Dependent
open import Cubical.Functions.Embedding
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.Relation.Nullary as Rel using (Dec ; Discrete ; ¬_ ; isProp¬)
open import Cubical.Data.Empty as Empty renaming (⊥* to ⊥ ; ⊥ to ⊥₀)
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit as Unit renaming (Unit* to ⊤ ; tt* to tt) hiding (tt)
open import Cubical.Reflection.StrictEquiv

private
  variable
    ℓ ℓ' : Level
    A B : Type ℓ

  equivInvCancel : ∀ {b₀ b₁ : B} → (e : A ≃ B) → invEq e b₀ ≡ invEq e b₁ → b₀ ≡ b₁
  equivInvCancel {b₀} {b₁} e = invEq (congEquiv (invEquiv e))

  invEquivEq : {e f : A ≃ B} → invEq e ≡ invEq f → e ≡ f
  invEquivEq {e} {f} inv-path = equivEq
    $ funExt λ a → invEq (congEquiv {x = equivFun e a} {y = equivFun f a} (invEquiv e))
    $ retEq e a ∙∙ sym (retEq f a) ∙∙ sym (inv-path ≡$ equivFun f a)

  Dec→Collapsible : Dec A → Rel.Collapsible A
  Dec→Collapsible = SplitSupport→Collapsible ∘ PStable→SplitSupport ∘ Stable→PStable ∘ Dec→Stable where
    open Rel

  opaque
    localHedberg : (a : A) → (∀ b → Rel.Collapsible (a ≡ b)) → (∀ b → isProp (a ≡ b))
    localHedberg {A} a coll b p q =
      p ≡⟨ conj b p ⟩
      sym (collapse a refl) ∙ collapse b p ≡⟨ cong (sym (collapse a refl) ∙_) (is-2-const-collapse b p q) ⟩
      sym (collapse a refl) ∙ collapse b q ≡⟨ sym $ conj b q ⟩
      q ∎
      where
        module _ (b : A) where
          collapse : a ≡ b → a ≡ b
          collapse = fst (coll b)

          is-2-const-collapse : (p q : a ≡ b) → collapse p ≡ collapse q
          is-2-const-collapse = snd (coll b)

        conj : ∀ b → (p : a ≡ b) → p ≡ sym (collapse a refl) ∙ collapse b p
        conj b = J (λ b p → p ≡ sym (collapse a refl) ∙ collapse b p) $ sym (lCancel (collapse a refl))

  symEquiv : ∀ {a b : A} → (a ≡ b) ≃ (b ≡ a)
  symEquiv = strictEquiv sym sym

  inhToProp→isProp : (A → isProp A) → isProp A
  inhToProp→isProp h a b = h a a b

  dec-⊎-equiv : Dec A ≃ (A ⊎ (¬ A))
  dec-⊎-equiv = isoToEquiv go module dec-⊎-equiv where
    go : Iso _ _
    go .Iso.fun (Rel.yes p) = inl p
    go .Iso.fun (Rel.no ¬p) = inr ¬p
    go .Iso.inv (inl x) = Rel.yes x
    go .Iso.inv (inr x) = Rel.no x
    go .Iso.rightInv (inl x) = refl
    go .Iso.rightInv (inr x) = refl
    go .Iso.leftInv (Rel.yes p) = refl
    go .Iso.leftInv (Rel.no ¬p) = refl

  decElim : ∀ {B : Dec A → Type ℓ}
    → (yes* : (a : A) → B (Rel.yes a))
    → (no* : (¬a : ¬ A) → B (Rel.no ¬a))
    → (a? : Dec A) → B a?
  decElim {B = B} yes* no* (Rel.yes a) = yes* a
  decElim {B = B} yes* no* (Rel.no ¬a) = no* ¬a

  ⊎-elim-Iso : {A : Type ℓ} {B : Type ℓ'} {ℓC : Level} {C : A ⊎ B → Type ℓC}
    → Iso
      ((∀ a → C (inl a)) × (∀ b → C (inr b)))
      (∀ x → C x)
  ⊎-elim-Iso .Iso.fun = uncurry Sum.elim
  ⊎-elim-Iso .Iso.inv f .fst = f ∘ inl
  ⊎-elim-Iso .Iso.inv f .snd = f ∘ inr
  ⊎-elim-Iso .Iso.rightInv f = funExt $ Sum.elim (λ _ → refl) (λ _ → refl)
  ⊎-elim-Iso .Iso.leftInv _ = refl

  inl≢inr : {a : A} {b : B} → ¬ inl a ≡ inr b
  inl≢inr p = Sum.⊎Path.encode _ _ p .lower

  ⊎-del-right : (b₀ : B) → A → (Σ[ x ∈ A ⊎ B ] ¬ x ≡ inr b₀)
  ⊎-del-right b₀ a .fst = inl a
  ⊎-del-right b₀ a .snd = inl≢inr

  ⊎-del-right-is-equiv : ((b₀ , _) : isContr B) → isEquiv (⊎-del-right {A = A} b₀)
  ⊎-del-right-is-equiv {B} {A} (b₀ , contr-b₀) .equiv-proof = uncurry (Sum.elim contr-fib-left contr-fib-right) where
    del : A → (Σ[ x ∈ A ⊎ B ] ¬ x ≡ inr b₀)
    del = ⊎-del-right b₀

    contr-fib-left : (a : A) (h : ¬ inl a ≡ inr b₀)
      → isContr (Σ[ a′ ∈ A ] del a′ ≡ (inl a , h))
    contr-fib-left a h = isOfHLevelRespectEquiv 0 fiber-equiv contr-singl where
      fiber-equiv : _ ≃ (Σ[ a′ ∈ A ] del a′ ≡ (inl a , h))
      fiber-equiv =
        (Σ[ (a′ , p) ∈ singl a ] PathP (λ i → ¬ inl (p (~ i)) ≡ inr b₀) inl≢inr h)
          ≃⟨ strictEquiv (λ ((a′ , p) , q) → (a′ , sym p , q)) (λ (a′ , p , q) → ((a′ , sym p) , q)) ⟩
        (Σ[ a′ ∈ A ] Σ[ p ∈ a′ ≡ a ] PathP (λ i → ¬ inl (p i) ≡ inr b₀) inl≢inr h)
          ≃⟨ Σ-cong-equiv-snd (λ a′ → Σ-cong-equiv-fst (cong inl , Sum.isEmbedding-inl a′ a)) ⟩
        (Σ[ a′ ∈ A ] Σ[ p ∈ inl a′ ≡ inl a ] PathP (λ i → ¬ p i ≡ inr b₀) inl≢inr h)
          ≃⟨ Σ-cong-equiv-snd (λ a′ → ΣPathP≃PathPΣ) ⟩
        (Σ[ a′ ∈ A ] del a′ ≡ (inl a , h))
          ≃∎

      contr-singl : isContr (Σ[ (a′ , p) ∈ singl a ] PathP (λ i → ¬ inl (p (~ i)) ≡ inr b₀) inl≢inr h)
      contr-singl = isContrΣ (isContrSingl a) λ where
        (a′ , p) → isProp→isContrPathP (λ _ → isProp¬ _) inl≢inr h
      
    contr-fib-right : (b : B) (h : ¬ inr b ≡ inr b₀) → isContr (Σ[ a ∈ A ] del a ≡ (inr b , h))
    contr-fib-right b h = Empty.rec contra where
      contra : ⊥₀
      contra = h $ cong inr $ sym $ contr-b₀ b

  ⊎-del-right-equiv : ((b₀ , _) : isContr B) → A ≃ (Σ[ x ∈ A ⊎ B ] ¬ x ≡ inr b₀)
  ⊎-del-right-equiv is-contr-B .fst = ⊎-del-right _
  ⊎-del-right-equiv is-contr-B .snd = ⊎-del-right-is-equiv is-contr-B

  Σ-⊎-snd-Iso : {B : A → Type ℓ'} {C : A → Type ℓ'}
    → Iso (Σ[ a ∈ A ] B a ⊎ C a) (Σ A B ⊎ Σ A C)
  Σ-⊎-snd-Iso .Iso.fun = uncurry λ a → Sum.rec (λ b → inl (a , b)) (λ c → inr (a , c))
  Σ-⊎-snd-Iso .Iso.inv = Sum.rec (λ (a , b) → a , inl b) (λ (a , c) → a , inr c)
  Σ-⊎-snd-Iso .Iso.rightInv = Sum.elim (λ _ → refl) (λ _ → refl)
  Σ-⊎-snd-Iso .Iso.leftInv = uncurry λ a → Sum.elim (λ b → refl) (λ c → refl)

Container : ∀ ℓ → Type (ℓ-suc ℓ)
Container ℓ = Σ[ S ∈ Type ℓ ] (S → Type ℓ)

ContainerEquiv : (C D : Container ℓ) → Type ℓ
ContainerEquiv (A₁ , B₁) (A₂ , B₂) = Σ[ α ∈ A₁ ≃ A₂ ] ∀ a₁ → B₁ a₁ ≃ B₂ (equivFun α a₁)

containerEquivToPath : ∀ {C D : Container ℓ}
  → ContainerEquiv C D
  → C ≡ D
containerEquivToPath (α , β) = Sigma.ΣPathP (ua α , uaOver α (equivFun ∘ β) (equivIsEquiv ∘ β))

module Container (C : Container ℓ) where
  open Σ C renaming (fst to Shape ; snd to Pos) public

_+_ : (C D : Container ℓ) → Container ℓ
_+_ (A₁ , B₁) (A₂ , B₂) = A₁ ⊎ A₂ , Sum.rec B₁ B₂

_⊗_ : (C D : Container ℓ) → Container ℓ
_⊗_ C D = C.Shape × D.Shape , (λ { (c , d) → C.Pos c ⊎ D.Pos d }) where
  module C = Container C
  module D = Container D

isIsolated : (a : A) → Type _
isIsolated a = ∀ a′ → Dec (a ≡ a′)

isIsolated→isPropPath : (a : A) → isIsolated a → ∀ a′ → isProp (a ≡ a′)
isIsolated→isPropPath a isolated = localHedberg a is-collapsible-path where
  is-collapsible-path : ∀ a′ → Rel.Collapsible (a ≡ a′)
  is-collapsible-path a′ = Dec→Collapsible (isolated a′)
  
isPropIsIsolated : (a : A) → isProp (isIsolated a)
isPropIsIsolated a = inhToProp→isProp go where module _ (isolated : isIsolated a) where
  go : isProp (isIsolated a)
  go = isPropΠ λ a′ → isOfHLevelRespectEquiv 1 (invEquiv dec-⊎-equiv) (Sum.isProp⊎ (isIsolated→isPropPath a isolated a′) (isProp¬ _) λ p ¬p → Empty.rec $ ¬p p)

_° : (A : Type ℓ) → Type ℓ
A ° = Σ[ a ∈ A ] isIsolated a

Isolated≡ : ∀ {a b : A °} → a .fst ≡ b .fst → a ≡ b
Isolated≡ = Σ≡Prop isPropIsIsolated

DiscreteIsolated : Discrete (A °)
DiscreteIsolated (a , a≟_) (b , b≟_) = Rel.decRec (λ a≡b → Dec.yes (Isolated≡ a≡b)) (λ a≢b → Dec.no λ p → Empty.rec $ a≢b $ cong fst p) (a≟ b)

opaque
  isSetIsolated : isSet (A °)
  isSetIsolated = Rel.Discrete→isSet DiscreteIsolated

_∖_ : (B : Type ℓ) (b : B) → Type ℓ
B ∖ b = Σ[ b′ ∈ B ] ¬ (b ≡ b′)

∂ : Container ℓ → Container ℓ
∂ (S , P) .fst = Σ[ s ∈ S ] (P s) °
∂ (S , P) .snd (s , p , _) = (P s) ∖ p

Cart : (C D : Container ℓ) → Type ℓ
Cart (S , P) (T , Q) = Σ[ f ∈ (S → T) ] ∀ s → Q (f s) ≃ P s

Id : Container ℓ
Id .fst = ⊤
Id .snd = const ⊤

isIsolatedRespectEquiv : (e : A ≃ B) → (b : B) → isIsolated b → isIsolated (invEq e b)
isIsolatedRespectEquiv e b isolated a = Rel.EquivPresDec eqv (isolated (equivFun e a))
  where
    eqv : (b ≡ equivFun e a) ≃ (invEq e b ≡ a)
    eqv = symEquiv ∙ₑ invEquiv (equivAdjointEquiv e) ∙ₑ symEquiv

isIsolatedInr : isIsolated {A = A ⊎ ⊤ {ℓ}} (inr tt)
isIsolatedInr (inl _) = Dec.no (inl≢inr ∘ sym)
isIsolatedInr (inr tt) = Dec.yes refl

module _ {ℓ} (P Q : Type ℓ) where
  isolate : (Q ≃ P ⊎ ⊤ {ℓ}) → Σ[ (q , _) ∈ Q ° ] (Q ∖ q) ≃ P
  isolate e = goal module isolate where
    q₀ : Q
    q₀ = invEq e (inr tt)

    is-isolated-q₀ : isIsolated q₀
    is-isolated-q₀ = isIsolatedRespectEquiv e (inr tt) isIsolatedInr

    e1ᴰ : (q : Q) → _
    e1ᴰ q = preCompEquiv (compPathrEquiv (retEq e q))

    e1 = Σ-cong-equiv-snd e1ᴰ
    e2 = Σ-cong-equiv-fst e
    e3 = Σ-cong-equiv-snd (λ q → preCompEquiv (congEquiv (invEquiv e)))
    e4 = Σ-cong-equiv-snd (λ p → preCompEquiv (strictEquiv sym sym))
    e5 = invEquiv (⊎-del-right-equiv isContrUnit*)

    Q∖q₀≃P : (Q ∖ q₀) ≃ P
    Q∖q₀≃P =
      Σ[ q ∈ Q ] ¬ (q₀ ≡ q)
        ≃⟨ e1 ⟩
      Σ[ q ∈ Q ] ¬ (q₀ ≡ invEq e (equivFun e q))
        ≃⟨ e2 ⟩
      Σ[ p ∈ P ⊎ ⊤ ] (¬ invEq e (inr tt) ≡ invEq e p)
        ≃⟨ e3 ⟩
      Σ[ p ∈ P ⊎ ⊤ {ℓ} ] (¬ inr tt ≡ p)
        ≃⟨ e4 ⟩
      Σ[ p ∈ P ⊎ ⊤ {ℓ} ] (¬ p ≡ inr tt)
        ≃⟨ e5 ⟩
      P
        ≃∎

    goal : Σ[ (q₀ , _) ∈ Q ° ] (Q ∖ q₀) ≃ P
    goal .fst = q₀ , is-isolated-q₀
    goal .snd = Q∖q₀≃P

  unisolate : (Σ[ (q , _) ∈ Q ° ] (Q ∖ q) ≃ P) → (Q ≃ P ⊎ ⊤ {ℓ})
  unisolate ((q₀ , q₀≟_) , e) = Q≃P⊎⊤ module unisolate where
    e1 = invEquiv (Σ-contractSnd λ q → inhProp→isContr (q₀≟ q) (Rel.isPropDec (isIsolated→isPropPath q₀ q₀≟_ q)))
    e2 = Σ-cong-equiv-snd (λ q → dec-⊎-equiv ∙ₑ Sum.⊎-swap-≃)
    e3 = isoToEquiv Σ-⊎-snd-Iso
    e4 = Sum.⊎-equiv e (isContr→≃Unit* (isContrSingl q₀))

    Q≃P⊎⊤ : Q ≃ P ⊎ ⊤
    Q≃P⊎⊤ =
      Q
        ≃⟨ e1 ⟩
      (Σ[ q ∈ Q ] Dec (q₀ ≡ q))
        ≃⟨ e2 ⟩
      (Σ[ q ∈ Q ] (¬ q₀ ≡ q) ⊎ (q₀ ≡ q))
        ≃⟨ e3 ⟩
      (Q ∖ q₀) ⊎ (singl q₀)
        ≃⟨ e4 ⟩
      P ⊎ ⊤
        ≃∎

  unisolate-β : ∀ q₀ → (q₀≟_ : isIsolated q₀) → (e : Q ∖ q₀ ≃ P)
    → ∀ q → (q₀≢q : ¬ q₀ ≡ q) → equivFun (unisolate ((q₀ , q₀≟_) , e)) q ≡ inl (equivFun e (q , q₀≢q))
  unisolate-β q₀ q₀≟_ e q q₀≢q = goal where
    lemma : q₀≟ q ≡ Dec.no q₀≢q
    lemma = Rel.isPropDec (isIsolated→isPropPath q₀ q₀≟_ q) _ _

    open unisolate q₀ q₀≟_ e

    goal : _ ≡ _
    goal =
      equivFun (unisolate ((q₀ , q₀≟_) , e)) q
        ≡⟨⟩
      equivFun (e2 ∙ₑ e3 ∙ₑ e4) (invEq (Σ-contractSnd λ q → inhProp→isContr (q₀≟ q) (Rel.isPropDec (isIsolated→isPropPath q₀ q₀≟_ q))) q)
        ≡⟨⟩
      equivFun (e2 ∙ₑ e3 ∙ₑ e4) (q , q₀≟ q)
        ≡⟨ cong (equivFun (e2 ∙ₑ e3 ∙ₑ e4)) (ΣPathP (refl , lemma)) ⟩
      equivFun (e2 ∙ₑ e3 ∙ₑ e4) (q , Dec.no q₀≢q)
        ≡⟨⟩
      inl (equivFun e (q , q₀≢q))
        ∎

  isolate-rinv : ∀ q₀ → (q₀≟_ : isIsolated q₀) → (e : Q ∖ q₀ ≃ P)
    → (q : Q ∖ q₀) → equivFun (isolate (unisolate ((q₀ , q₀≟_) , e)) .snd) q ≡ equivFun e q
  isolate-rinv q₀ q₀≟_ e (q , q₀≢q) =
    equivFun (isolate e' .snd) (q , q₀≢q)
      ≡⟨⟩
    equivFun (e1 ∙ₑ e2 ∙ₑ e3 ∙ₑ e4 ∙ₑ e5) (q , q₀≢q)
      ≡⟨⟩
    equivFun (e3 ∙ₑ e4 ∙ₑ e5) (equivFun e2 (equivFun e1 (q , q₀≢q)))
      ≡⟨⟩
    equivFun (e3 ∙ₑ e4 ∙ₑ e5) (equivFun e2 (q , equivFun (e1ᴰ q) q₀≢q))
      ≡⟨⟩
    equivFun (e3 ∙ₑ e4 ∙ₑ e5) (equivFun e' q , equivFun (e1ᴰ q) q₀≢q)
      ≡⟨ cong (equivFun (e3 ∙ₑ e4 ∙ₑ e5)) $ ΣPathP (unisolate-β q₀ q₀≟_ e q q₀≢q , isProp→PathP (λ i → isProp¬ $ invEq e' (inr tt) ≡ invEq e' (unisolate-β q₀ q₀≟_ e q q₀≢q i)) (equivFun (e1ᴰ q) q₀≢q) e[inr]≢e[inl]) ⟩
    equivFun (e3 ∙ₑ e4 ∙ₑ e5) (inl (equivFun e (q , q₀≢q)) , e[inr]≢e[inl])
      ≡⟨⟩
    equivFun e (q , q₀≢q)
      ∎
      where
        e' = unisolate ((q₀ , q₀≟_) , e)
        open isolate e' hiding (q₀)

        e[inr]≢e[inl] : ¬ invEq e' (inr tt) ≡ invEq e' (inl (equivFun e (q , q₀≢q)))
        e[inr]≢e[inl] = λ p → Empty.rec $ inl≢inr $ sym (equivInvCancel {b₀ = inr tt} e' p)

  isolate-iso : Iso (Q ≃ P ⊎ ⊤ {ℓ}) (Σ[ (q , _) ∈ Q ° ] (Q ∖ q) ≃ P)
  isolate-iso .Iso.fun = isolate
  isolate-iso .Iso.inv = unisolate
  isolate-iso .Iso.rightInv ((q₀ , q₀≟_) , e) = ΣPathP λ where
    .fst → Isolated≡ refl
    .snd → equivPathP $ funExt $ isolate-rinv q₀ q₀≟_ e
  isolate-iso .Iso.leftInv e = invEquivEq $ funExt λ where
    (inl p) → refl′ (invEq (unisolate (isolate e)) (inl p))
    (inr tt) → refl′ (invEq (unisolate (isolate e)) (inr tt))

check : ∀ {F G : Container ℓ} → Iso (Cart (F ⊗ Id) G) (Cart F (∂ G))
check {F = F@(S , P)} {G = G@(T , Q)} =
  Cart (F ⊗ Id) G
    Iso⟨ idIso ⟩
  (Σ[ f ∈ (S × ⊤ → T) ] ∀ s* → Q (f s*) ≃ P (s* .fst) ⊎ ⊤)
    Iso⟨ Σ-cong-iso (domIso rUnit*×Iso) (λ u → domIsoDep (invIso rUnit*×Iso)) ⟩
  (Σ[ f ∈ (S → T) ] ∀ s → Q (f s) ≃ P s ⊎ ⊤)
    Iso⟨ invIso Σ-Π-Iso ⟩
  ((s : S) → Σ[ t ∈ T ] Q t ≃ P s ⊎ ⊤)
    Iso⟨ codomainIsoDep (λ s → Σ-cong-iso-snd λ t → isolate-iso (P s) (Q t)) ⟩
  ((s : S) → Σ[ t ∈ T ] Σ[ (q , _) ∈ Q t ° ] (Q t ∖ q) ≃ P s)
    Iso⟨ codomainIsoDep (λ s → invIso Σ-assoc-Iso) ⟩
  ((s : S) → Σ[ (t , q , _) ∈ Σ[ t ∈ T ] (Q t °) ] (Q t ∖ q) ≃ P s)
    Iso⟨ Σ-Π-Iso ⟩
  Cart F (∂ G)
    ∎Iso
