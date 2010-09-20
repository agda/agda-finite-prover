module Crosswhite where

open import Data.Function using (_∘_)
open import Data.Function.LeftInverse hiding (_∘_)
open import Relation.Nullary

  
------------------------------------------------------------------------
-- ExpFunctors
------------------------------------------------------------------------

-- Note that currently the expfunctor laws are not included here.

open import Level

record RawExpFunctor (f : Set → Set) : Set₁ where
  field
    xmap : ∀ {a b} → (a → b) → (b → a) → f a → f b

  unxmap : ∀ {a b} → (b → a) → (a → b) → f a → f b
  unxmap g f = xmap f g

mapDec : ∀ {P Q} → (P → Q) → (Q → P) → Dec P → Dec Q
mapDec f _ (yes p) = yes (f p)
mapDec _ g (no p) = no (p ∘ g)

------------------------------------------------------------------------
-- ExpFunctor instance for Dec.

expfunctor : RawExpFunctor Dec
expfunctor = record { xmap = mapDec }

open import Data.Fin using (Fin)
open import Data.Fin.Dec using (all?)
open import Data.Fin.Props using (eq?)
open import Data.Function using (_∘_; id; _on_; Fun₁; Fun₂)
open import Data.Function.Equality as FEq hiding (_∘_; id)
open import Relation.Binary.PropositionalEquality as PEq
import Relation.Binary.EqReasoning as EqReasoning

module Decision
 {n}
 {A : Set}
 (finite : LeftInverse (PEq.setoid A) (PEq.setoid (Fin n)))
 where

  infix 4 _≟_

  private
   to : A → Fin n
   to = FEq._⟨$⟩_ (LeftInverse.to finite)

   from : Fin n → A
   from = FEq._⟨$⟩_ (LeftInverse.from finite)

  _≟_ : (a₁ a₂ : A) → Dec (a₁ ≡ a₂)
  _≟_ = eq? (LeftInverse.injection finite)

  from∘to : ∀ {a} → (from ∘ to) a ≡ a
  from∘to {a} = LeftInverse.left-inverse finite a

  decide : ∀ (f g : Fun₁ A) → Dec (∀ a → f a ≡ g a)
  decide f g =
   mapDec
     f∘from≡g∘from→f≡g
     f≡g→f∘from≡g∘from
     (all? (λ a → (f ∘ from) a ≟ (g ∘ from) a))
   where
     open EqReasoning (PEq.setoid A)

     f≡g→f∘from≡g∘from :
       ∀ {f g : Fun₁ A}
       → (∀ a → f a ≡ g a)
       → (∀ b → (f ∘ from) b ≡ (g ∘ from) b)
     f≡g→f∘from≡g∘from proveFor = proveFor ∘ from

     f∘from≡g∘from→f≡g :
       ∀ {f g : Fun₁ A}
       → (∀ b → (f ∘ from) b ≡ (g ∘ from) b)
       → (∀ a → f a ≡ g a)
     f∘from≡g∘from→f≡g {f} {g} proveFor a = begin
       f a                ≈⟨ sym (PEq.cong f from∘to) ⟩
       (f ∘ from ∘ to) a  ≈⟨ proveFor (to a) ⟩
       (g ∘ from ∘ to) a  ≈⟨ PEq.cong g from∘to ⟩
       g a                ∎

  all?₂ : ∀ {P : Fin n → Fin n → Set} → (∀ a b → Dec (P a b)) → Dec (∀ a b → P a b)
  all?₂ f = all? (λ a → all? (λ b → f a b))

  decide₂ : ∀ (f g : Fun₂ A) → Dec (∀ a b → f a b ≡ g a b)
  decide₂ f g =
   mapDec
     f∘from≡g∘from→f≡g
     f≡g→f∘from≡g∘from
     (all?₂ (λ a b → (f on from) a b ≟ (g on from) a b))
   where
     open EqReasoning (PEq.setoid A)

     f≡g→f∘from≡g∘from :
       ∀ {f g : Fun₂ A}
       → (∀ a b → f a b ≡ g a b)
       → (∀ a b → (f on from) a b ≡ (g on from) a b)
     f≡g→f∘from≡g∘from proveFor a b = proveFor (from a) (from b)

     f∘from≡g∘from→f≡g :
       ∀ {f g : Fun₂ A}
       → (∀ a b → (f on from) a b ≡ (g on from) a b)
       → (∀ a b → f a b ≡ g a b)
     f∘from≡g∘from→f≡g {f} {g} proveFor a b = begin
       f a b                  ≈⟨ sym (PEq.cong₂ f from∘to from∘to) ⟩
       (f on (from ∘ to)) a b ≈⟨ proveFor (to a) (to b) ⟩
       (g on (from ∘ to)) a b ≈⟨ PEq.cong₂ g from∘to from∘to ⟩
       g a b                  ∎

  cong₃ : ∀ {A B C D : Set}
         (f : A → B → C → D) {a b c x y z} → a ≡ x → b ≡ y → c ≡ z → f a b c ≡ f x y z
  cong₃ f refl refl refl = refl

  Fun₃ : (A : Set) → Set
  Fun₃ A = A → A → A → A

  _on₃_ : ∀ {A B C} → (B → B → B → C) → (A → B) → (A → A → A → C)
  _on₃_ f g x y z = f (g x) (g y) (g z)

  all?₃ : ∀ {P : Fin n → Fin n → Fin n → Set} → (∀ a b c → Dec (P a b c)) → Dec (∀ a b c → P a b c)
  all?₃ f = all? (λ a → all?₂ (λ b c → f a b c))

  decide₃ : ∀ (f g : Fun₃ A) → Dec (∀ a b c → f a b c ≡ g a b c)
  decide₃ f g =
   mapDec
     f∘from≡g∘from→f≡g
     f≡g→f∘from≡g∘from
     (all?₃ (λ a b c → (f on₃ from) a b c ≟ (g on₃ from) a b c))
   where
     open EqReasoning (PEq.setoid A)

     f≡g→f∘from≡g∘from :
       ∀ {f g : Fun₃ A}
       → (∀ a b c → f a b c ≡ g a b c)
       → (∀ a b c → (f on₃ from) a b c ≡ (g on₃ from) a b c)
     f≡g→f∘from≡g∘from proveFor a b c = proveFor (from a) (from b) (from c)

     f∘from≡g∘from→f≡g :
       ∀ {f g : Fun₃ A}
       → (∀ a b c → (f on₃ from) a b c ≡ (g on₃ from) a b c)
       → (∀ a b c → f a b c ≡ g a b c)
     f∘from≡g∘from→f≡g {f} {g} proveFor a b c = begin
       f a b c                   ≈⟨ sym (cong₃ f from∘to from∘to from∘to) ⟩
       (f on₃ (from ∘ to)) a b c ≈⟨ proveFor (to a) (to b) (to c) ⟩
       (g on₃ (from ∘ to)) a b c ≈⟨ cong₃ g from∘to from∘to from∘to ⟩
       g a b c                   ∎
