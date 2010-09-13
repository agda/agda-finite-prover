{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Cardinality.Auto where

open import Level
open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.Fin.Dec
open import Data.Fin.Props hiding (to-from)
open import Data.Vec
open import Data.Vec.Auto
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Auto
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


FiniteWitness : ∀ {n a} {A : Set a}
              → Vec A n
              → Set a
FiniteWitness xs = ∀ x
                 → ∃ λ i
                 → lookup i xs ≡ x

module Args {n a} {A : Set a}
            (xs : Vec A n)
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
    
    Cancels₂ : Set a
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

open Args public
