{-# OPTIONS --guardedness #-}

module Playground.Conat where

open import Playground.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Sum.Base
open import Cubical.Codata.Conat

open Bisimulation

≈-refl : {x : Conat} → x ≈ x
≈-refl = misib refl

≈″-refl : {x : Conat′} → x ≈′′ x
≈″-refl {inl x} = tt
≈″-refl {suc x} = ≈-refl {x}

≈′-refl : {x : Conat′} → x ≈′ x
≈′-refl = con ≈″-refl

open Iso
fix : Iso Conat Conat′
fix .fun = force
fix .inv = conat
fix .rightInv n′ = refl
fix .leftInv n = bisim goal where
  goal : conat (force n) ≈ n
  goal .prove = ≈′-refl {x = force n}
