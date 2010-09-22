{-# OPTIONS --universe-polymorphism #-}

-- a drop-in replacement for N-ary which supports
--   (A : Set a) (B : Set b) instead of
--   (A : Set ℓ) (B : Set ℓ).
-- also includes Π-ary, a version of N-ary whose
--   second type parameter is a dependent type.
module Data.Vec.Pi-ary where

open import Level
open import Data.Nat hiding (_⊔_)
open import Data.Vec


private
 module Levels {a b : Level} where
  private
    level : ℕ → Level
    level zero    = b
    level (suc _) = a ⊔ b
  
  N-ary : (n : ℕ) → Set a → Set b → Set (level n)
  N-ary zero          A B = B
  N-ary (suc zero)    A B = A → N-ary zero    A B
  N-ary (suc (suc n)) A B = A → N-ary (suc n) A B
  
  Π-ary : (n : ℕ)
        → (A : Set a)
        → (B : Vec A n → Set b)
        → Set (level n)
  Π-ary zero    A B = B []
  Π-ary (suc zero)    A B = (x : A) → Π-ary zero    A (λ xs → B (x ∷ xs))
  Π-ary (suc (suc n)) A B = (x : A) → Π-ary (suc n) A (λ xs → B (x ∷ xs))
  
  curryⁿ : ∀ {n A B} → (Vec A n → B) → N-ary n A B
  curryⁿ {zero}        f = f []
  curryⁿ {suc zero}    f = λ x → curryⁿ (λ xs → f (x ∷ xs))
  curryⁿ {suc (suc n)} f = λ x → curryⁿ (λ xs → f (x ∷ xs))
  
  _$ⁿ_ : ∀ {n A B} → N-ary n A B → (Vec A n → B)
  f $ⁿ []             = f
  f $ⁿ (x₁ ∷ [])      = f x₁
  f $ⁿ (x₁ ∷ x₂ ∷ xs) = f x₁ $ⁿ (x₂ ∷ xs)
  
  πcurryⁿ : ∀ {n A B} → ((xs : Vec A n) → B xs) → Π-ary n A B
  πcurryⁿ {zero}        f = f []
  πcurryⁿ {suc zero}    f = λ x → πcurryⁿ (λ xs → f (x ∷ xs))
  πcurryⁿ {suc (suc n)} f = λ x → πcurryⁿ (λ xs → f (x ∷ xs))
  
  _π$ⁿ_ : ∀ {n A B} → Π-ary n A B → ((xs : Vec A n) → B xs)
  f π$ⁿ []             = f
  f π$ⁿ (x₁ ∷ [])      = f x₁
  f π$ⁿ (x₁ ∷ x₂ ∷ xs) = f x₁ π$ⁿ (x₂ ∷ xs)
open Levels public
