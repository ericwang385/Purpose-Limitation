open import Relation.Binary.Lattice using (BoundedJoinSemilattice)

module Variable {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Type J
open import Context J
open import Purpose J

variable
    Γ : Ctx
    A B C : Set
    a b : Type
    l l₁ l₂ : Label