module Relation.Nullary.Auto where

open import Data.Empty
open import Data.Unit
open import Relation.Nullary


toT : {P : Set} → Dec P → Set
toT (yes _) = ⊤
toT (no _) = ⊥

fromT : ∀ {P} dP → toT {P} dP → P
fromT {P} (yes p) _ = p
fromT {P} (no _) ()
