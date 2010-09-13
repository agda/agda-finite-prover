module Main where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
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
import Algebra.FunctionProperties as P
open P _≡_
open ≡-Reasoning


data Pauli : Set where
  I : Pauli
  X : Pauli
  Y : Pauli
  Z : Pauli

_⋅_ : Pauli → Pauli → Pauli
_ ⋅ I = I
I ⋅ _ = I
X ⋅ X = I
X ⋅ Y = Z
X ⋅ Z = Y
Y ⋅ X = Z
Y ⋅ Y = I
Y ⋅ Z = X
Z ⋅ X = Y
Z ⋅ Y = X
Z ⋅ Z = I

+-comm : Commutative _⋅_
+-comm I I = refl
+-comm I X = refl
+-comm I Y = refl
+-comm I Z = refl
+-comm X I = refl
+-comm X X = refl
+-comm X Y = refl
+-comm X Z = refl
+-comm Y I = refl
+-comm Y X = refl
+-comm Y Y = refl
+-comm Y Z = refl
+-comm Z I = refl
+-comm Z X = refl
+-comm Z Y = refl
+-comm Z Z = refl

finitePauli : Finite Pauli
finitePauli = 4 , record { into = toFin
                         ; from = fromFin
                         ; bij = to-from , from-to
                         } where
  xs : Vec Pauli 4
  xs = I ∷ X ∷ Y ∷ Z ∷ []
  
  info : ∀ x
       → ∃ λ i
       → lookup i xs ≡ x
  info I = # 0 , refl
  info X = # 1 , refl
  info Y = # 2 , refl
  info Z = # 3 , refl
  
  toFin : Pauli → Fin 4
  toFin x = proj₁ (info x)
  
  fromFin : Fin 4 → Pauli
  fromFin i = lookup i xs
  
  to-from : ∀ x → toFin (fromFin x) ≡ x
  to-from = fromT (all? λ x
          → toFin (fromFin x) ≟ x
            ) _
  
  from-to : ∀ x → fromFin (toFin x) ≡ x
  from-to x = proj₂ (info x)
  
  ⋅-comm : Commutative _⋅_
  ⋅-comm x y = thus x y (almost (toFin x) (toFin y)) where
    _∙_ : Fin 4 → Fin 4 → Fin 4
    x ∙ y = toFin (fromFin x ⋅ fromFin y)
    
    and-similarly : ∀ x y
                  → x ⋅ y ≡ fromFin (toFin x ∙ toFin y)
    and-similarly x y =
      begin
        x ⋅ y
      ≡⟨ cong₂ _⋅_ (sym (from-to x)) (sym (from-to y)) ⟩
        fromFin (toFin x) ⋅ fromFin (toFin y)
      ≡⟨ sym (from-to _) ⟩
        fromFin (toFin (fromFin (toFin x) ⋅ fromFin (toFin y)))
      ≡⟨ refl ⟩
        fromFin (toFin x ∙ toFin y)
      ∎
    
    P : Fin 4 → Fin 4 → Set
    P x y = x ∙ y ≡ y ∙ x
    
    Q : Pauli → Pauli → Set
    Q x y = x ⋅ y ≡ y ⋅ x
    
    thus : ∀ x y → P (toFin x) (toFin y) → Q x y
    thus x y p =
      begin
        x ⋅ y
      ≡⟨ and-similarly x y ⟩
        fromFin (toFin x ∙ toFin y)
      ≡⟨ cong fromFin p ⟩
        fromFin (toFin y ∙ toFin x)
      ≡⟨ sym (and-similarly y x) ⟩
        y ⋅ x
      ∎
    
    almost : ∀ x y → P x y
    almost = fromT (all? λ x
           → (all? λ y
           → x ∙ y ≟ y ∙ x
             )) _
