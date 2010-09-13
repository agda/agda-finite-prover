{-# OPTIONS --universe-polymorphism #-}

module Data.Vec.Auto where

open import Level
open import Data.Nat
open import Data.Fin
open import Data.Vec
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


toVec : ∀ {ℓ n} {A : Set ℓ}
      → (Fin n → A)
      → Vec A n
toVec {ℓ} {n} f = map f (allFin n)

lookup-toVec : ∀ {ℓ n x} {A : Set ℓ}
             → (f : Fin n → A)
             → lookup x (toVec f) ≡ f x
lookup-toVec {ℓ} {n} {x} f =
  begin
    lookup x (map f (allFin n))
  ≡⟨ lookup-free f x ⟩
    f (lookup x (allFin n))
  ≡⟨ cong f (lookup-allFin x) ⟩
    f x
  ∎


zip-eq : ∀ {ℓ n} {A : Set ℓ}
       → (P Q : Fin n → A)
       → toVec P ≡ toVec Q
       → (∀ x → P x ≡ Q x)
zip-eq P Q eq x =
  begin
    P x
  ≡⟨ sym (lookup-toVec P) ⟩
    lookup x (toVec P)
  ≡⟨ cong (lookup x) eq ⟩
    lookup x (toVec Q)
  ≡⟨ lookup-toVec Q ⟩
    Q x
  ∎
