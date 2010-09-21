module Main where

open import Data.Nat hiding (_≟_; eq?)
open import Data.Fin
open import Data.Fin.Auto
open import Data.Fin.Cardinality
open import Data.Vec
open import Data.Vec.L-ary
open import Data.Vec.Pi-ary
open import Data.Matrix hiding (lookup)
open import Data.Matrix.Auto
open import Data.Product
open import Data.Function
open import Data.Function.LeftInverse using (LeftInverse)
open import Relation.Nullary
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality
import Algebra.FunctionProperties

open import Crosswhite


data Pauli : Set where
  I : Pauli
  X : Pauli
  Y : Pauli
  Z : Pauli

_⋅_ : Pauli → Pauli → Pauli
X ⋅ X = I
X ⋅ Y = Z
X ⋅ Z = Y
Y ⋅ X = Z
Y ⋅ Y = I
Y ⋅ Z = X
Z ⋅ X = Y
Z ⋅ Y = X
Z ⋅ Z = I
a ⋅ I = a
I ⋅ a = a

finitePauli : Finite Pauli
finitePauli = finite xs w refl where
  xs = I ∷ X ∷ Y ∷ Z ∷ []
  
  w : FiniteWitness xs
  w I = # 0 , refl
  w X = # 1 , refl
  w Y = # 2 , refl
  w Z = # 3 , refl

pauli4 : SameCardinality Pauli (Fin 4)
pauli4 = proj₂ finitePauli

leftPauli : LeftInverse (setoid Pauli) (setoid (Fin 4))
leftPauli = leftInverse pauli4

-- ⋅-identity : Identity I _⋅_
-- ⋅-identity = fromYes (decide (_⋅_ I) id) refl
--            , fromYes (decide (flip _⋅_ I) id) refl
-- 
-- ⋅-commutative : Commutative _⋅_
-- ⋅-commutative = fromYes (decide₂ (_⋅_) (flip _⋅_)) refl
-- 
-- ⋅-inverse : Inverse I id _⋅_
-- ⋅-inverse = fromYes (decide (λ x → x ⋅ x) (const I)) refl , fromYes (decide (λ x → x ⋅ x) (const I)) refl

-- causes a "memory allocation failed (requested 2097152 bytes)" error
--   ⋅-associative : Associative _⋅_
--   ⋅-associative = fromYes (decide₃ (λ x y z → (x ⋅ y) ⋅ z) (λ x y z → x ⋅ (y ⋅ z))) refl
