module Data.Matrix.Auto where

open import Data.Nat
open import Data.Fin
open import Data.List hiding (allFin; lookup; map)
open import Data.Vec renaming (lookup to vec-lookup; map to vec-map)
open import Data.Vec.Properties
open import Data.Vec.Theorems renaming (lookup-free to vec-lookup-free)
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
                  → lookup (toMatrix f) js ≡ f js
  lookup-toMatrix {[]}     f []       = refl
  lookup-toMatrix {n ∷ ns} f (j ∷ js) =
    begin
      lookup (vec-lookup (vec-map (toMatrices f) (allFin n))
                         j)
             js
    ≡⟨ cong (λ xs → lookup xs js)
            (vec-lookup-free (toMatrices f) j (allFin n)) ⟩
      lookup (toMatrices f (vec-lookup (allFin n) j))
             js
    ≡⟨ cong (λ x → lookup (toMatrices f x) js)
            (lookup-allFin j) ⟩
      lookup (toMatrices f j) js
    ≡⟨ refl ⟩
      lookup (toMatrix (split-call f j)) js
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
      lookup (toMatrix P) js
    ≡⟨ cong (λ xs → lookup xs js) eq ⟩
      lookup (toMatrix Q) js
    ≡⟨ lookup-toMatrix Q js ⟩
      Q js
    ∎

open Args public
