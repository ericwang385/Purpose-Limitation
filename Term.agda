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
    true        : Γ ⊢ bool
    false       : Γ ⊢ bool
    zero        : Γ ⊢ nat
    suc         : Γ ⊢ nat → Γ ⊢ nat
    case_of_    : Γ ⊢ nat → Γ ⊢ A → Γ , nat ⊢ A → Γ ⊢ A

    var_        : Γ ∋ A → Γ ⊢ A                
    ƛ_          : Γ , A ⊢ B → Γ ⊢ (A ⇒ B)
    _•_         : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    _+_         : Γ ⊢ nat → Γ ⊢ nat → Γ ⊢ nat
    If_Then_Else : Γ ⊢ bool → Γ ⊢ A → Γ ⊢ A → Γ ⊢ A

    η_          : Γ ⊢ A → Γ ⊢ ⟨ ⊥ ⟩ A  
    _↑_         : l₁ ⊑ l₂ → Γ ⊢ ⟨ l₁ ⟩ A → Γ ⊢ ⟨ l₂ ⟩ A
    Labeled     : Γ ⊢ A → Γ ⊢ (⟨ l ⟩ A)
    Let_⇐_In_   : l₁ ⊑ l₂ → Γ ⊢ (⟨ l₁ ⟩ A) → Γ ⊢ (A ⇒ ⟨ l₂ ⟩ B) → Γ ⊢ ⟨ l₁ ◦ l₂ ⟩ B
    
    