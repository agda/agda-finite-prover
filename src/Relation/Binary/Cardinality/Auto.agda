{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Cardinality.Auto where

open import Level
open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.Fin.Dec
open import Data.Vec
open import Data.Vec.Auto
open import Data.Product
open import Data.Function.LeftInverse
open import Relation.Nullary
open import Relation.Nullary.Auto
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


private
  module Args {ℓ} {A : Set ℓ} where
    FiniteWitness : ∀ {n}
                  → Vec A n
                  → Set ℓ
    FiniteWitness xs = ∀ x
                     → ∃ λ i
                     → lookup i xs ≡ x
    
    module Finite {n} (xs : Vec A n)
                  (w : FiniteWitness xs)
         where
      private
        into : A → Fin n
        into x = proj₁ (w x)
        
        from : Fin n → A
        from i = lookup i xs
        
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
        to-from : ∀ i → into (lookup i xs) ≡ i
        to-from = zip-eq P Q eq
      
      finite : Cancels₁
             → Finite A
      finite eq = n , finiteCardinality eq
    
    open Finite public
    
    
    leftInverse : ∀ {b} {B : Set b}
                → SameCardinality A B
                → LeftInverse (setoid A) (setoid B)
    leftInverse car = record
                    { to           = →-to-⟶ into
                    ; from         = →-to-⟶ from
                    ; left-inverse = proj₂ bij
                    } where
      open SameCardinality car

open Args public
