module Data.Fin.Auto where

open import Data.Nat
open import Data.Fin
open import Data.List hiding (map)
open import Data.Vec hiding (replicate)
open import Data.Vec.Properties
open import Data.Vec.Theorems
open import Data.Vec.Pi-ary
open import Data.Matrix hiding (map)
open import Data.Matrix.Auto
open import Data.Matrix.Cardinality
open import Data.Product hiding (map)
open import Function
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


infix 0 _≈_
_≈_ : ∀ {ℓ} {A : Set ℓ}
    → A → A
    → A × A
_≈_ = _,_

private
 module Args {a b} {A : Set a} {B : Set b}
             (finite : Finite A)
             (k : ℕ)
             (P,Q : N-ary k A (B × B))
        where
  private
    P : Vec A k → B
    P xs = proj₁ (P,Q $ⁿ xs)
    
    Q : Vec A k → B
    Q xs = proj₂ (P,Q $ⁿ xs)
    
    n = proj₁ finite
    ns = replicate k n
    open SameCardinality (proj₂ finite)
         renaming ( into to A→fin
                  ; from to fin→A
                  ; bij to A↔fin
                  )
    open SameCardinality (fins-cardinality {n} {k})
         renaming ( into to fins→vec
                  ; from to vec→fins
                  ; bij to fins↔vec
                  )
    
    _′ : (Vec A k → B) → Fins ns → B
    _′ f js = f (map fin→A (fins→vec js))
    
    P′ = P ′
    Q′ = Q ′
    
    _′′ : (f : Vec A k → B)
        → (xs : Vec A k)
        → (f ′) (vec→fins (map A→fin xs))
        ≡ f xs
    _′′ f xs =
      begin
        f (map fin→A (fins→vec (vec→fins (map A→fin xs))))
      ≡⟨ cong (λ – → f (map fin→A –))
              (proj₁ fins↔vec _) ⟩
        f (map fin→A (map A→fin xs))
      ≡⟨ cong f $ sym $ map-∘ fin→A A→fin _ ⟩
        f (map (fin→A ∘ A→fin) xs)
      ≡⟨ cong f $ map-ext-id (proj₂ A↔fin) _ ⟩
        f xs
      ∎
  
  vec-auto : toMatrix P′ ≡ toMatrix Q′
           → (xs : Vec A k)
           → P xs ≡ Q xs
  vec-auto eqs xs =
    begin
      P xs
    ≡⟨ sym ((P ′′) xs) ⟩
      P′ (vec→fins (map A→fin xs))
    ≡⟨ matrix-zip-eq P′ Q′ eqs _ ⟩
      Q′ (vec→fins (map A→fin xs))
    ≡⟨ (Q ′′) xs ⟩
      Q xs
    ∎
  
  auto : toMatrix P′ ≡ toMatrix Q′
       → Π-ary k A λ xs
       → P xs ≡ Q xs
  auto eqs = πcurryⁿ (vec-auto eqs)

open Args public
