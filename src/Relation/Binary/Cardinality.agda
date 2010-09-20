{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Cardinality where

open import Level
open import Data.Fin
open import Data.Product
open import Data.Function.LeftInverse
open import Relation.Binary.PropositionalEquality


Cancels : ∀ {a b} {A : Set a} {B : Set b}
        → (A → B) → (B → A) → Set b
Cancels f g = ∀ x → f (g x) ≡ x

Bijection : ∀ {a b} {A : Set a} {B : Set b}
          → (A → B) → (B → A) → Set (a ⊔ b)
Bijection f g = Cancels f g × Cancels g f

record SameCardinality {a b} (A : Set a) (B : Set b)
                     : Set (a ⊔ b)
                       where
  field
    into : A → B
    from : B → A
    bij : Bijection into from

Finite : ∀ {ℓ} → Set ℓ → Set ℓ
Finite A = ∃ λ n → SameCardinality A (Fin n)


leftInverse : ∀ {a b} {A : Set a} {B : Set b}
            → SameCardinality A B
            → LeftInverse (setoid A) (setoid B)
leftInverse car = record
                { to           = →-to-⟶ into
                ; from         = →-to-⟶ from
                ; left-inverse = proj₂ bij
                } where
  open SameCardinality car
