{-# OPTIONS --universe-polymorphism #-}

module Data.Matrix where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.List hiding (map)
open import Data.Vec renaming (lookup to vec-lookup; map to vec-map)


Matrix : ∀ {ℓ} → Set ℓ → List ℕ → Set ℓ
Matrix A [] = A
Matrix A (n ∷ ns) = Vec (Matrix A ns) n

data Fins : List ℕ → Set where
  []  : Fins []
  _∷_ : ∀ {n ns}
      → Fin n
      → Fins ns
      → Fins (n ∷ ns)


lookup : ∀ {ns ℓ} {A : Set ℓ}
       → Fins ns
       → Matrix A ns
       → A
lookup []       x  = x
lookup (j ∷ js) xs = lookup js (vec-lookup j xs)

map : ∀ {ns a b} {A : Set a} {B : Set b}
    → (A → B)
    → Matrix A ns
    → Matrix B ns
map {[]}     f x  = f x
map {n ∷ ns} f xs = vec-map (map {ns} f) xs
