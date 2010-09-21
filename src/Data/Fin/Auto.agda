{-# OPTIONS --universe-polymorphism #-}

module Data.Fin.Auto where

open import Level
open import Data.Fin
open import Data.List hiding (map)
open import Data.Vec hiding (replicate)
open import Data.Vec.Theorems
open import Data.Vec.N-ary
open import Data.Matrix hiding (map)
open import Data.Matrix.Auto
open import Data.Matrix.Cardinality
open import Data.Product hiding (map)
open import Data.Function
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


private
 module Args {ℓ} {A : Set ℓ} {B : Set ℓ}
             (finite : Finite A)
             {k} (P Q : N-ary k A B)
        where
  private
    n = proj₁ finite
    ns = replicate k n
    open SameCardinality (proj₂ finite)
         renaming ( into to A→fin
                  ; from to fin→A
                  ; bij to A↔fin
                  )
    open SameCardinality fins-cardinality
         renaming ( into to fins→vec
                  ; from to vec→fins
                  ; bij to fins↔vec
                  )
    
    _′ : N-ary k A B → Fins ns → B
    _′ f js = f $ⁿ map fin→A (fins→vec js)
    
    P′ = P ′
    Q′ = Q ′
    
    _′′ : (f : N-ary k A B)
        → (xs : Vec A k)
        → (f ′) (vec→fins (map A→fin xs))
        ≡ f $ⁿ xs
    _′′ f xs =
      begin
        f $ⁿ map fin→A (fins→vec (vec→fins (map A→fin xs)))
      ≡⟨ cong (λ – → f $ⁿ map fin→A –)
              (proj₁ fins↔vec _) ⟩
        f $ⁿ map fin→A (map A→fin xs)
      ≡⟨ cong (λ – → f $ⁿ –)
              (map-∘ fin→A A→fin xs) ⟩
        f $ⁿ map (fin→A ∘ A→fin) xs
      ≡⟨ cong (λ – → f $ⁿ –)
              (map-id (proj₂ A↔fin) xs) ⟩
        f $ⁿ xs
      ∎
  
  vec-auto : toMatrix P′ ≡ toMatrix Q′
           → (xs : Vec A k)
           → P $ⁿ xs
           ≡ Q $ⁿ xs
  vec-auto eqs xs =
    begin
      P $ⁿ xs
    ≡⟨ sym ((P ′′) xs) ⟩
      P′ (vec→fins (map A→fin xs))
    ≡⟨ matrix-zip-eq P′ Q′ eqs _ ⟩
      Q′ (vec→fins (map A→fin xs))
    ≡⟨ (Q ′′) xs ⟩
      Q $ⁿ xs
    ∎

open Args public
