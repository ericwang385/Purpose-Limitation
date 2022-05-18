open import Relation.Binary.Lattice using (BoundedJoinSemilattice)

module Type {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Purpose J

infixr 10 _⇒_

data Type : Set c where
    Unit : Type
    Nat  : Type
    Bool : Type
    _⇒_  : (a b : Type) → Type
    -- Labeled data with purpose
    ⟨_⟩_ : Label → Type → Type
    IO⟨_⟩_ : Label → Type → Type