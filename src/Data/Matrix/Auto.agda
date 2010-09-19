{-# OPTIONS --universe-polymorphism #-}

module Data.Matrix.Auto where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.List hiding (map)
open import Data.Vec renaming (lookup to vec-lookup; map to vec-map)
open import Data.Vec.Auto renaming (lookup-free to vec-lookup-free)
open import Data.Matrix
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


private
  module Args {ℓ} {A : Set ℓ} where
    mutual
      private
        split-call : ∀ {n ns}
                   → (Fins (n ∷ ns) → A)
                   → Fin n
                   → Fins ns
                   → A
        split-call f j js = f (j ∷ js)
        
        toMatrices : ∀ {n ns}
                   → (Fins (n ∷ ns) → A)
                   → Fin n
                   → Matrix A ns
        toMatrices f j = toMatrix (split-call f j)
      
      toMatrix : ∀ {ns}
               → (Fins ns → A)
               → Matrix A ns
      toMatrix {[]}     f = f []
      toMatrix {n ∷ ns} f = vec-map (toMatrices f) (allFin n)


    lookup-toMatrix : ∀ {ns}
                    → (f : Fins ns → A)
                    → (js : Fins ns)
                    → lookup js (toMatrix f) ≡ f js
    lookup-toMatrix {[]}     f []       = refl
    lookup-toMatrix {n ∷ ns} f (j ∷ js) =
      begin
        lookup js (vec-lookup j (vec-map (toMatrices f) (allFin n)))
      ≡⟨ cong (lookup js)
              (vec-lookup-free (toMatrices f) j) ⟩
        lookup js (toMatrices f (vec-lookup j (allFin n)))
      ≡⟨ cong (λ x → lookup js (toMatrices f x))
              (lookup-allFin j) ⟩
        lookup js (toMatrices f j)
      ≡⟨ refl ⟩
        lookup js (toMatrix (split-call f j))
      ≡⟨ lookup-toMatrix _ js ⟩
        split-call f j js
      ∎


    matrix-zip-eq : ∀ {ns}
                  → (P Q : Fins ns → A)
                  → toMatrix P ≡ toMatrix Q
                  → (∀ js → P js ≡ Q js)
    matrix-zip-eq P Q eq js =
      begin
        P js
      ≡⟨ sym (lookup-toMatrix P js) ⟩
        lookup js (toMatrix P)
      ≡⟨ cong (lookup js) eq ⟩
        lookup js (toMatrix Q)
      ≡⟨ lookup-toMatrix Q js ⟩
        Q js
      ∎

open Args public
