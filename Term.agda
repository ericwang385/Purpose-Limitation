open import Purpose

module Term (p : Purpose) where

open import Variable p
open import Context p
open import Type p

variable
    Γ : Ctx
    A B : Type
    l l₁ l₂ : Label

    
infix  4 _⊢_
data _⊢_ : Ctx → Type → Set where
    true : Γ ⊢ Bool
    false : Γ ⊢ Bool
    zero : Γ ⊢ Nat
    suc : Γ ⊢ Nat → Γ ⊢ Nat
    var_ : Γ ∋ A → Γ ⊢ A 
    ƛ_ : (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
    _•_ : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    Labeled : Γ ⊢ A → Γ ⊢ (⟨ l ⟩ A)
    _>>=_ : l₁ ⊑ l₂ → Γ ⊢ (⟨ l₁ ⟩ A) → Γ ⊢ (A ⇒ ⟨ l₂ ⟩ B) → Γ ⊢ ⟨ l₂ ⟩ B
    
    