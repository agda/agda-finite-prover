{-# OPTIONS --universe-polymorphism #-}

module Data.Vec.Theorems where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


lookup-free : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
            → ∀ {n} i (xs : Vec A n)
            → lookup (map f xs) i
            ≡ f (lookup xs i)
lookup-free f zero    (x ∷ xs) = refl
lookup-free f (suc i) (x ∷ xs) = lookup-free f i xs

-- a version of map-id supporting functions which are
-- merely extensionaly equivalent to id.
map-ext-id : ∀ {a} {A : Set a}
           → {f : A → A}
           → (∀ x → f x ≡ x)
           → ∀ {n}
           → (xs : Vec A n)
           → map f xs ≡ xs
map-ext-id {f = f} fx≡x []       = refl
map-ext-id {f = f} fx≡x (x ∷ xs) =
  begin
    f x ∷ map f xs
  ≡⟨ cong₂ _∷_
           (fx≡x x)
           (map-ext-id fx≡x xs) ⟩
    x ∷ xs
  ∎
