{-# OPTIONS --universe-polymorphism #-}

module Relation.Nullary.Auto where

open import Level
open import Data.Empty
open import Data.Unit
open import Relation.Nullary


toT : ∀ {ℓ} → {P : Set ℓ} → Dec P → Set
toT (yes _) = ⊤
toT (no _) = ⊥

fromT : ∀ {ℓ P} dP → toT {ℓ} {P} dP → P
fromT {P} (yes p) _ = p
fromT {P} (no _) ()
