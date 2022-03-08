open import Relation.Binary.Lattice using (BoundedJoinSemilattice)

module Context {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Type J
open import Purpose J

infixl 5 _,_
data Ctx : Set c where
  ∅   : Ctx
  _,_ : Ctx → Type → Ctx

-- Γ has more type than Δ
data _⊆_ : Ctx → Ctx → Set where
    base : ∅ ⊆ ∅
    cons : ∀ {Γ Δ T} -> Γ ⊆ Δ -> (Γ , T) ⊆ (Δ , T)
    drop : ∀ {Γ Δ T} -> Γ ⊆ Δ -> (Γ , T) ⊆ Δ

infix  4 _∋_
data _∋_ : Ctx → Type → Set where
    Z  : ∀ {Γ A} → Γ , A ∋ A
    S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A

