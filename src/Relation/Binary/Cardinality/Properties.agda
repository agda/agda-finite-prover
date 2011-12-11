module Relation.Binary.Cardinality.Properties where

open import Data.Product
open import Function
open import Function.LeftInverse hiding (id ; _∘_)
open import Relation.Binary.Cardinality
open import Relation.Binary.PropositionalEquality renaming ( sym to ≡-sym
                                                           ; trans to ≡-trans
                                                           )

open ≡-Reasoning


reflexive : ∀ {a} {A : Set a}
          → SameCardinality A A
reflexive = record
          { into = id
          ; from = id
          ; bij = (λ x → refl)
                , (λ x → refl)
          }

private
 module Args {a b} {A : Set a} {B : Set b}
        (car : SameCardinality A B)
        where
  open SameCardinality car
       renaming ( into to A→B
                ; from to A←B
                ; bij  to A↔B
                )
  
  leftInverse : LeftInverse (setoid A) (setoid B)
  leftInverse = record
              { to              = →-to-⟶ A→B
              ; from            = →-to-⟶ A←B
              ; left-inverse-of = proj₂ A↔B
              }
  
  sym : SameCardinality B A
  sym = record
      { into  = A←B
      ; from  = A→B
      ; bij   = swap A↔B
      }
  
  trans : ∀ {c} {C : Set c}
        → SameCardinality B C
        → SameCardinality A C
  trans car = record
            { into  = B→C ∘ A→B
            ; from  = A←B ∘ B←C
            ; bij   = bij₁ , bij₂
            } where
    open SameCardinality car
         renaming ( into to B→C
                  ; from to B←C
                  ; bij  to B↔C
                  )
    bij₁ : ∀ x → B→C (A→B (A←B (B←C x))) ≡ x
    bij₁ x =
      begin
        B→C (A→B (A←B (B←C x)))
      ≡⟨ cong B→C
              (proj₁ A↔B _) ⟩
        B→C (B←C x)
      ≡⟨ proj₁ B↔C x ⟩
        x
      ∎
    
    bij₂ : ∀ x → A←B (B←C (B→C (A→B (x)))) ≡ x
    bij₂ x =
      begin
        A←B (B←C (B→C (A→B (x))))
      ≡⟨ cong A←B
              (proj₂ B↔C _) ⟩
        A←B (A→B (x))
      ≡⟨ proj₂ A↔B x ⟩
        x
      ∎
open Args public
