module Data.Matrix where

open import Data.Nat
open import Data.Fin
open import Data.List hiding (lookup; map)
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
       → Matrix A ns
       → Fins ns
       → A
lookup x  []       = x
lookup xs (j ∷ js) = lookup (vec-lookup xs j) js

map : ∀ {ns a b} {A : Set a} {B : Set b}
    → (A → B)
    → Matrix A ns
    → Matrix B ns
map {[]}     f x  = f x
map {n ∷ ns} f xs = vec-map (map {ns} f) xs
