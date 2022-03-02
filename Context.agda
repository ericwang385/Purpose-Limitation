open import Purpose

module Context (p : Purpose) where

open import Type p
open import Data.List using (List ; [] ; _∷_) public

infixl 5 _,_
data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Type → Ctx

-- Γ has more type than Δ
data _⊆_ : Ctx → Ctx → Set where
    base : ∅ ⊆ ∅
    cons : ∀ {Γ Δ T} -> Γ ⊆ Δ -> (Γ , T) ⊆ (Δ , T)
    drop : ∀ {Γ Δ T} -> Γ ⊆ Δ -> (Γ , T) ⊆ Δ
