module Main where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (_≟_)
open import Data.Fin
open import Data.Fin.Dec
open import Data.Fin.Props hiding (to-from)
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
import Algebra.FunctionProperties as P
open P _≡_
open ≡-Reasoning


toT : {P : Set} → Dec P → Set
toT (yes _) = ⊤
toT (no _) = ⊥

fromT : ∀ {P} dP → toT {P} dP → P
fromT {P} (yes p) _ = p
fromT {P} (no _) ()
    

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

LoopsBack : ∀ {A B} → (A → B) → (B → A) → Set
LoopsBack f g = ∀ x → f (g x) ≡ x

Bijection : ∀ {A B} → (A → B) → (B → A) → Set
Bijection f g = LoopsBack f g × LoopsBack g f

record SameCardinality (A B : Set) : Set where
  field
    into : A → B
    from : B → A
    bij : Bijection into from

Finite : Set → Set
Finite A = ∃ λ n → SameCardinality A (Fin n)

finitePauli : Finite Pauli
finitePauli = 4 , record { into = toFin
                         ; from = fromFin
                         ; bij = to-from , from-to
                         } where
  toFin : Pauli → Fin 4
  toFin I = # 0
  toFin X = # 1
  toFin Y = # 2
  toFin Z = # 3
  
  fromFin : Fin 4 → Pauli
  fromFin zero = I
  fromFin (suc zero) = X
  fromFin (suc (suc zero)) = Y
  fromFin (suc (suc (suc zero))) = Z
  fromFin (suc (suc (suc (suc ()))))
  
  to-from : ∀ x → toFin (fromFin x) ≡ x
  to-from = fromT (all? λ x
          → toFin (fromFin x) ≟ x
            ) _
  
  from-to : ∀ x → fromFin (toFin x) ≡ x
  from-to I = refl
  from-to X = refl
  from-to Y = refl
  from-to Z = refl
  
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
