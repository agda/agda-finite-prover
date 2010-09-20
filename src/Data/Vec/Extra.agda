{-# OPTIONS --universe-polymorphism #-}

module Data.Vec.Extra where

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


