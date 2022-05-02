open import Relation.Binary.Lattice using (BoundedJoinSemilattice)

module Purpose {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Level public renaming (suc to lsuc; _⊔_ to _l⊔_ ; zero to lzero)
open import Relation.Nullary


open BoundedJoinSemilattice J public renaming (
    Carrier       to Label
  ; _≈_           to _≃_
  ; _≤_           to _⊑_
  ; _∨_           to _∘_
  ; refl          to ⊑-refl
  ; reflexive     to ⊑-reflexive
  ; trans         to ⊑-trans 
  ; minimum       to ⊑-minimum 
  ; antisym       to ⊑-antisym
  ; supremum      to ∘-supremum
  )


_⋢_ : Label → Label → Set ℓ₂
t ⋢ u = ¬ (t ⊑ u)

⊥-⊑ᵣ : ∀ {A} → ⊥ ⊑ A
⊥-⊑ᵣ {A} = ⊑-minimum A

-- ⊥-⊑ₗ : ∀ {A} → Dec (A ⊑ ⊥)
-- ⊥-⊑ₗ {A} with Dec (A ≡ ⊥)
-- ...   | yes = {!   !}
-- ...   | no = {!   !}