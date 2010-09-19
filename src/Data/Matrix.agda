{-# OPTIONS --universe-polymorphism #-}

module Data.Matrix where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.List hiding (map)
open import Data.Vec renaming (lookup to vec-lookup; map to vec-map)
open import Data.Vec.Auto renaming (lookup-free to vec-lookup-free)
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


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


lookup-free : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
            → ∀ {ns}
            → (js : Fins ns)
            → {xs : Matrix A ns}
            → lookup js (map {ns} f xs)
            ≡ f (lookup js xs)
lookup-free f {[]}     []       {x}  = refl
lookup-free f {n ∷ ns} (j ∷ js) {xs} =
  begin
    lookup js (vec-lookup j (vec-map (map {ns} f) xs))
  ≡⟨ cong (lookup js) (vec-lookup-free (map {ns} f) j) ⟩
    lookup js (map {ns} f (vec-lookup j xs))
  ≡⟨ lookup-free f js ⟩
    f (lookup js (vec-lookup j xs))
  ∎
