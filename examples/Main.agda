module Main where

open import Data.Nat
open import Data.Fin
open import Data.Fin.Auto
open import Data.Fin.Cardinality
open import Data.Vec
open import Data.Vec.Pi-ary
open import Data.Product
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality
import Algebra.FunctionProperties as F

open F _≡_


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

⋅-identity : Identity I _⋅_
⋅-identity = auto finitePauli 1 (λ x → I ⋅ x ≈ x) refl
           , auto finitePauli 1 (λ x → x ⋅ I ≈ x) refl

⋅-commutative : Commutative _⋅_
⋅-commutative = auto finitePauli 2 (λ x y → x ⋅ y ≈ y ⋅ x) refl

⋅-inverse : Inverse I (λ x → x) _⋅_
⋅-inverse = auto finitePauli 1 (λ x → x ⋅ x ≈ I) refl
          , auto finitePauli 1 (λ x → x ⋅ x ≈ I) refl

⋅-associative : Associative _⋅_
⋅-associative = auto finitePauli 3 (λ x y z → (x ⋅ y) ⋅ z ≈ x ⋅ (y ⋅ z)) refl
