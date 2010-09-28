{-# OPTIONS --universe-polymorphism #-}

module Data.Vec.Theorems where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning


lookup-free : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
            → ∀ {n} i {xs : Vec A n}
            → lookup i (map f xs)
            ≡ f (lookup i xs)
lookup-free f zero    {x ∷ xs} = refl
lookup-free f (suc i) {x ∷ xs} = lookup-free f i {xs}

lookup-allFin : ∀ {n} x
              → lookup x (allFin n) ≡ x
lookup-allFin {zero}  ()
lookup-allFin {suc n} (zero)  = refl
lookup-allFin {suc n} (suc x) =
  begin
    lookup x (map suc (allFin n))
  ≡⟨ lookup-free suc x ⟩
    suc (lookup x (allFin n))
  ≡⟨ cong suc (lookup-allFin x) ⟩
    suc x
  ∎


map-∘ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
      → (f : B → C)
      → (g : A → B)
      → ∀ {n}
      → (xs : Vec A n)
      → map f (map g xs)
      ≡ map (f ∘ g) xs
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) =
  begin
    f (g x) ∷ map f (map g xs)
  ≡⟨ cong (λ – → f (g x) ∷ –)
          (map-∘ f g xs) ⟩
    (f ∘ g) x ∷ map (f ∘ g) xs
  ∎

map-id : ∀ {a} {A : Set a}
       → {f : A → A}
       → (∀ x → f x ≡ x)
       → ∀ {n}
       → (xs : Vec A n)
       → map f xs ≡ xs
map-id {f = f} fx≡x []       = refl
map-id {f = f} fx≡x (x ∷ xs) =
  begin
    f x ∷ map f xs
  ≡⟨ cong₂ _∷_
           (fx≡x x)
           (map-id fx≡x xs) ⟩
    x ∷ xs
  ∎
