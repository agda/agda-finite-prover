{-# OPTIONS --universe-polymorphism #-}

module Data.Fin.Cardinality where

open import Level
open import Data.Fin
open import Data.Vec hiding (replicate) renaming (lookup to vec-lookup)
open import Data.Vec.Auto
open import Data.Product hiding (map)
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality


private
  module Args {ℓ} {A : Set ℓ} where
    FiniteWitness : ∀ {n}
                  → Vec A n
                  → Set ℓ
    FiniteWitness xs = ∀ x
                     → ∃ λ i
                     → vec-lookup i xs ≡ x

    module WithWitness {n} (xs : Vec A n)
                       (w : FiniteWitness xs)
         where
      private
        into : A → Fin n
        into x = proj₁ (w x)
        
        from : Fin n → A
        from i = vec-lookup i xs
        
        P : Fin n → Fin n
        P i = into (from i)
        
        Q : Fin n → Fin n
        Q i = i
        
        Cancels₁ : Set
        Cancels₁ = toVec P ≡ toVec Q
        
        Cancels₂ : Set ℓ
        Cancels₂ = ∀ x
                 → from (into x) ≡ x
        
        lookupWitness : Cancels₂
        lookupWitness x = proj₂ (w x)
      
      finiteCardinality : Cancels₁
                        → SameCardinality A (Fin n)
      finiteCardinality eq = record
                           { into = into
                           ; from = from
                           ; bij = to-from , lookupWitness
                           } where
        to-from : ∀ i → into (vec-lookup i xs) ≡ i
        to-from = zip-eq P Q eq
      
      finite : Cancels₁
             → Finite A
      finite eq = n , finiteCardinality eq
    
    open WithWitness public
open Args public
