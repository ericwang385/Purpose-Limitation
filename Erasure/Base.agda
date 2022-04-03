{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open BoundedJoinSemilattice using (Carrier)

module Erasure.base {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (u : Carrier J) where

open import Data.GMonad.Base using (GMonad)
open import Variable J
open import Context J
open import Purpose J
open import Term J
open import Type J

open import Agda.Builtin.Nat using (_+_) renaming (Nat to ℕ)
open import Agda.Builtin.Bool using () renaming (Bool to 𝔹)
open import Agda.Builtin.Unit

variable
    A B : Set ℓ₂

M : Label → Set ℓ₂ → Set ℓ₂
M l a = l ⊑ u → a

return : A → M ⊥ A
return a = λ x → a

_>>=_ : M l₁ A → (A → M l₂ B) → M (l₁ ∘ l₂) B
_>>=_ {l₁ = l₁} {l₂ = l₂} ma f = λ x → f (ma (⊑-trans (x≤x∨y l₁ l₂) x)) ((⊑-trans (y≤x∨y l₁ l₂) x))

sub : l₁ ⊑ l₂ → M l₁ A → M l₂ A
sub flow ma = λ x → ma (⊑-trans flow x)

GradedMonad : GMonad {ℓ₂} J
GradedMonad = record{
    M = M ;
    return = return ;
    _>>=_ = _>>=_ ;
    sub = sub}

open import Eval J GradedMonad

-- Value : Type → Set
-- Value Nat       = ℕ
-- Value Bool      = 𝔹
-- Value Unit      = ⊤
-- Value (a ⇒ b)   = Value a → Value b
-- Value (⟨ l ⟩ a) = M l (Value a)

-- data Env : Ctx → Set where
--     ∅   : Env ∅
--     _,_ : Env Γ → Value a → Env (Γ , a)

-- lookupVar : Env Γ → Γ ∋ a → Value a 
-- lookupVar (ρ , v) Z     = v
-- lookupVar (ρ , v) (S x) = lookupVar ρ x 

-- ⟨_⟩⟦_⟧_ : Label → Γ ⊢ a → Env Γ → Value a
-- ⟨ l ⟩⟦ unit ⟧ ρ = tt
-- ⟨ l ⟩⟦ true ⟧ ρ = 𝔹.true
-- ⟨ l ⟩⟦ false ⟧ ρ = 𝔹.false
-- ⟨ l ⟩⟦ lit n ⟧ ρ = n

-- ⟨ l ⟩⟦ case x of[zero⇒ x₁ |suc⇒ x₂ ] ⟧ ρ with (⟨ l ⟩⟦ x ⟧ ρ)
-- ...       |  ℕ.zero = ⟨ l ⟩⟦ x₁ ⟧ ρ
-- ...       |  ℕ.suc n = ⟨ l ⟩⟦ x₂ ⟧ (ρ , n)
-- ⟨ l ⟩⟦ var x ⟧ ρ = lookupVar ρ x
-- ⟨ l ⟩⟦ ƛ x ⟧ ρ = λ y → ⟨ l ⟩⟦ x ⟧ (ρ , y)

-- ⟨ l ⟩⟦ f • x ⟧ ρ = (⟨ l ⟩⟦ f ⟧ ρ) (⟨ l ⟩⟦ x ⟧ ρ)
-- ⟨ l ⟩⟦ plus x y ⟧ ρ = (⟨ l ⟩⟦ x ⟧ ρ) + (⟨ l ⟩⟦ y ⟧ ρ)
-- ⟨ l ⟩⟦ If cond Then e1 Else e2 ⟧ ρ with (⟨ l ⟩⟦ cond ⟧ ρ)
-- ...       | 𝔹.true  = ⟨ l ⟩⟦ e1 ⟧ ρ
-- ...       | 𝔹.false = ⟨ l ⟩⟦ e2 ⟧ ρ

-- ⟨ l ⟩⟦ η x ⟧ ρ = return (⟨ l ⟩⟦ x ⟧ ρ)
-- ⟨ l ⟩⟦ _↑_ {l₂ = l₂} x x₁ ⟧ ρ = l ⊑ l₂ → ?

-- ⟨ l ⟩⟦ label l₁ x ⟧ ρ = sub ⊥-⊑ᵣ (return (⟨ l ⟩⟦ x ⟧ ρ))
-- ⟨ l ⟩⟦ Let x ⇐ x₁ In x₂ ⟧ ρ = {!   !}   