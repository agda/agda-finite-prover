{-# OPTIONS --universe-polymorphism #-}

module Data.Vec.Auto where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Vec.Theorems
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


private
  module Args {ℓ} {A : Set ℓ}
              {n : ℕ}
         where
    toVec : (Fin n → A)
          → Vec A n
    toVec f = map f (allFin n)
    
    lookup-toVec : (f : Fin n → A)
                 → (x : Fin n)
                 → lookup x (toVec f) ≡ f x
    lookup-toVec f x =
      begin
        lookup x (map f (allFin n))
      ≡⟨ lookup-free f x ⟩
        f (lookup x (allFin n))
      ≡⟨ cong f (lookup-allFin x) ⟩
        f x
      ∎
    
    
    zip-eq : (P Q : Fin n → A)
           → toVec P ≡ toVec Q
           → (∀ x → P x ≡ Q x)
    zip-eq P Q eq x =
      begin
        P x
      ≡⟨ sym (lookup-toVec P x) ⟩
        lookup x (toVec P)
      ≡⟨ cong (lookup x) eq ⟩
        lookup x (toVec Q)
      ≡⟨ lookup-toVec Q x ⟩
        Q x
      ∎

open Args public
