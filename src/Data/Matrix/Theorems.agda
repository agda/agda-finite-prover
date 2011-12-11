module Data.Matrix.Theorems where

open import Data.Matrix
open import Data.List hiding (map)
open import Data.Vec renaming (lookup to vec-lookup; map to vec-map)
open import Data.Vec.Theorems renaming (lookup-free to vec-lookup-free)
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


lookup-free : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
            → ∀ {ns}
            → (js : Fins ns)
            → {xs : Matrix A ns}
            → lookup js (map {ns} f xs)
            ≡ f (lookup js xs)
lookup-free f {[]}     []       {x}  = refl
lookup-free f {n ∷ ns} (j ∷ js) {xs} =
  begin
    lookup js (vec-lookup j (vec-map (map {ns} f) xs))
  ≡⟨ cong (lookup js) (vec-lookup-free (map {ns} f) j) ⟩
    lookup js (map {ns} f (vec-lookup j xs))
  ≡⟨ lookup-free f js ⟩
    f (lookup js (vec-lookup j xs))
  ∎
