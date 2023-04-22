module Playground.Loop where

open import Playground.Prelude

open import Cubical.HITs.S1
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

Ω : Type₁
Ω = (A : Type) (B : A → Type) (a : A) (b : B a) (p : a ≡ a) → PathP (λ i → B (p i)) b b

¬Ω : ¬ Ω
¬Ω ω = boom where
  A = S¹

  B : A → Type
  B base = Bool
  B (loop i) = notEq i

  p : PathP (λ i → notEq i) true true
  p = ω A B base true loop

  false≡true : false ≡ true
  false≡true = fromPathP p

  boom : ⊥
  boom = false≢true false≡true
