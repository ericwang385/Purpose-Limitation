{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open import Data.GMonad.Base using (GMonad)

module Term {v c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (G : GMonad {v} J) where

open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Agda.Builtin.Bool using () renaming (Bool to 𝔹)
open import Agda.Builtin.Unit using (⊤)
open import Variable J
open import Context J
open import Purpose J
open import Type J
open GMonad G

open import Data.List using (List)

Value : Type → Set v

IOStream : (l : Label) → Type → Set v
IOStream l a = List (M l (Value a))

-- data IOStream (l : Label) : Type → Set v where
--     []    : IOStream l a
--     _∷ˢ_  : (Value a) → IOStream l a → IOStream l a

Value Nat       = ℕ
Value Bool      = 𝔹
Value Unit      = ⊤
Value (a ⇒ b)   = Value a → Value b
Value (⟨ l ⟩ a) = M l (Value a)
Value (IO⟨ l ⟩ a) = List (M l (Value a))

infix  4 _⊢_
data _⊢_ (Γ : Ctx) : Type → Set (c l⊔ ℓ₂ l⊔ v) where
    unit          : Γ ⊢ Unit
    true          : Γ ⊢ Bool
    false         : Γ ⊢ Bool
    lit           : ℕ → Γ ⊢ Nat
    case_of[zero⇒_|suc⇒_]      : Γ ⊢ Nat → Γ ⊢ a → Γ , Nat ⊢ a → Γ ⊢ a

    var_          : Γ ∋ a → Γ ⊢ a                
    ƛ_            : Γ , a ⊢ b → Γ ⊢ (a ⇒ b)
    _•_           : Γ ⊢ (a ⇒ b) → Γ ⊢ a → Γ ⊢ b
    plus          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
    If_Then_Else_ : Γ ⊢ Bool → Γ ⊢ a → Γ ⊢ a → Γ ⊢ a

    η_            : Γ ⊢ a → Γ ⊢ ⟨ ⊥ ⟩ a  
    _↑_           : l₁ ⊑ l₂ → Γ ⊢ ⟨ l₁ ⟩ a → Γ ⊢ ⟨ l₂ ⟩ a
    label         : (l : Label) → Γ ⊢ a → Γ ⊢ (⟨ l ⟩ a)
    Let_⇐_In_     : Γ ⊢ a → Γ ⊢ (⟨ l₁ ⟩ a) → Γ , a ⊢ (a ⇒ ⟨ l₂ ⟩ b) → Γ ⊢ ⟨ l₁ ∘ l₂ ⟩ b 

    -- read_      : Γ ⊢ IO⟨ l ⟩ a → Γ  ⊢ ⟨ l ⟩ a 
    write         : Γ ⊢ ⟨ l ⟩ a → IOStream l a → Γ ⊢ IO⟨ l ⟩ a  