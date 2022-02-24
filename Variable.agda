open import Purpose
module Variable (l : Purpose) where

open import Type l
open import Context l

infix  4 _∋_
data _∋_ : Ctx → Type → Set where
    Z  : ∀ {Γ A} → Γ , A ∋ A
    S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A