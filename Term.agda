open import Purpose

module Term (p : Purpose) where

open import Variable p
open import Context p
open import GMonad p
open import Type p

variable
    Γ : Ctx
    a b : Type

infix  4 _⊢_
data _⊢_ (Γ : Ctx) : Type → Set where
    true        : Γ ⊢ Bool
    false       : Γ ⊢ Bool
    zero        : Γ ⊢ Nat
    suc         : Γ ⊢ (Nat ⇒ Nat)
    case_of_    : Γ ⊢ Nat → Γ ⊢ a → Γ , Nat ⊢ a → Γ ⊢ a

    var_        : Γ ∋ a → Γ ⊢ a                
    ƛ_          : Γ , a ⊢ b → Γ ⊢ (a ⇒ b)
    _•_         : Γ ⊢ (a ⇒ b) → Γ ⊢ a → Γ ⊢ b
    _+_         : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
    If_Then_Else : Γ ⊢ Bool → Γ ⊢ a → Γ ⊢ a → Γ ⊢ a

    η_          : Γ ⊢ a → Γ ⊢ ⟨ ⊥ ⟩ a  
    _↑_         : l₁ ⊑ l₂ → Γ ⊢ ⟨ l₁ ⟩ a → Γ ⊢ ⟨ l₂ ⟩ a
    -- GMonad_     : GMonad (⟨ l ⟩ a)
    -- Maybe remove these  
    Labeled     : Γ ⊢ a → Γ ⊢ (⟨ l ⟩ a)
    Let_⇐_In_   : l₁ ⊑ l₂ → Γ ⊢ (⟨ l₁ ⟩ a) → Γ ⊢ (a ⇒ ⟨ l₂ ⟩ b) → Γ ⊢ ⟨ l₁ ◦ l₂ ⟩ b
