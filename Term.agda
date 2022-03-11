open import Relation.Binary.Lattice using (BoundedJoinSemilattice)

module Term {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Variable J
open import Context J
open import Purpose J
open import Type J

infix  4 _⊢_
data _⊢_ (Γ : Ctx) : Type → Set (c l⊔ ℓ₂) where
    unit          : Γ ⊢ Unit
    true          : Γ ⊢ Bool
    false         : Γ ⊢ Bool
    lit           : ℕ → Γ ⊢ Nat
    --case_of[zero=>_|suc=>_]      : Γ ⊢ Nat → Γ ⊢ a → Γ , Nat ⊢ a → Γ ⊢ a

    var_          : Γ ∋ a → Γ ⊢ a                
    ƛ_            : Γ , a ⊢ b → Γ ⊢ (a ⇒ b)
    _•_           : Γ ⊢ (a ⇒ b) → Γ ⊢ a → Γ ⊢ b
    plus          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
    If_Then_Else_ : Γ ⊢ Bool → Γ ⊢ a → Γ ⊢ a → Γ ⊢ a

    η_            : Γ ⊢ a → Γ ⊢ ⟨ ⊥ ⟩ a  
    _↑_           : l₁ ⊑ l₂ → Γ ⊢ ⟨ l₁ ⟩ a → Γ ⊢ ⟨ l₂ ⟩ a
    label         : (l : Label) → Γ ⊢ a → Γ ⊢ (⟨ l ⟩ a)
    Let_⇐_In_     : Γ ⊢ a → Γ ⊢ (⟨ l₁ ⟩ a) → Γ , a ⊢ (a ⇒ ⟨ l₂ ⟩ b) → Γ ⊢ ⟨ l₁ ∘ l₂ ⟩ b 