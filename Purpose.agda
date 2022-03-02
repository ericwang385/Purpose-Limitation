module Purpose where

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

record Purpose : Set₁ where
    field
        Label : Set
        ⊥ : Label
        ⊤ : Label
        _◦_ : Label → Label → Label

        _⊑_ : Label → Label → Set
        ⊑-refl  : Reflexive _⊑_
        ⊑-trans : Transitive _⊑_

        r-id : {l : Label} → l ◦ ⊥ ≡ l
        l-id : {l : Label} → ⊥ ◦ l ≡ l
        assoc : {l₁ l₂ l₃ : Label} → l₁ ◦ (l₂ ◦ l₃) ≡ (l₁ ◦ l₂) ◦ l₃
 