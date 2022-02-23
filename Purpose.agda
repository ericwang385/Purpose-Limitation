module Purpose where

open import Relation.Binary

record Purpose : Set₁ where
    field
        Label : Set
        _⊑_ : Label → Label → Set

    postulate
        ⊑-refl  : Reflexive _⊑_
        ⊑-trans : Transitive _⊑_