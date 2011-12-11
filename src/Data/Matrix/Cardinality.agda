module Data.Matrix.Cardinality where

open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.Vec hiding (replicate)
open import Data.Matrix
open import Data.Product
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


fins-cardinality : ∀ {m n}
                 → SameCardinality (Fins (replicate n m))
                                   (Vec (Fin m) n)
fins-cardinality {m} = record
                     { into = into
                     ; from = from
                     ; bij = into-from , from-into
                     } where
  From : ℕ → Set
  From n = Fins (replicate n m)
  
  Into : ℕ → Set
  Into n = Vec (Fin m) n
  
  into : ∀ {n} → From n → Into n
  into {zero}  []       = []
  into {suc n} (x ∷ xs) = x ∷ into xs
  
  from : ∀ {n} → Into n → From n
  from {zero}  []       = []
  from {suc n} (x ∷ xs) = x ∷ from xs
  
  into-from : ∀ {n} → (x : Into n) → into (from x) ≡ x
  into-from {zero}  []       = refl
  into-from {suc n} (x ∷ xs) = cong (_∷_ x) (into-from xs)
  
  from-into : ∀ {n} → (x : From n) → from (into x) ≡ x
  from-into {zero}  []       = refl
  from-into {suc n} (x ∷ xs) = cong (_∷_ x) (from-into xs)
