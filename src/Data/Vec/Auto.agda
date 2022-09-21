module Data.Vec.Auto where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.Vec.Properties
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
               → lookup (toVec f) x ≡ f x
  lookup-toVec f x =
    begin
      lookup (map f (allFin n)) x
    ≡⟨ lookup-free f x (allFin n) ⟩
      f (lookup (allFin n) x)
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
      lookup (toVec P) x
    ≡⟨ cong (λ xs → lookup xs x) eq ⟩
      lookup (toVec Q) x
    ≡⟨ lookup-toVec Q x ⟩
      Q x
    ∎

open Args public
