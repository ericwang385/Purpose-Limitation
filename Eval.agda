open import Purpose 

module Eval (p : Purpose) where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Variable p
open import Context p
open import Term p
open import Type p

Value : Type → Set
Value Nat = ℕ
Value Bool = 𝔹
Value (A ⇒ B) = Value A → Value B
Value (⟨ l ⟩ A) = Value A

data Env : Ctx → Set where
    ∅ : Env ∅
    _,_ : Env Γ → Value a → Env (Γ , a)

lookupVar : Env Γ → Γ ∋ a → Value a 
lookupVar (ρ , v) Z = v
lookupVar (ρ , v) (S x) = lookupVar ρ x 

eval : Γ ⊢ a → Env Γ → Value a
eval true ρ = true
eval false ρ = false
eval zero ρ = zero
eval suc ρ = suc
eval x ρ = {!   !}
