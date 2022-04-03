{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open import Data.GMonad.Base using (GMonad)

module Eval {v c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (G : GMonad {v} J) where

open import Variable J
open import Context J
open import Purpose J
open import Term J
open import Type J
open GMonad G

open import Agda.Builtin.Nat using (_+_) renaming (Nat to ℕ)
open import Agda.Builtin.Bool using () renaming (Bool to 𝔹)
open import Agda.Builtin.Unit

Value : Type → Set v
Value Nat       = ℕ
Value Bool      = 𝔹
Value Unit      = ⊤
Value (a ⇒ b)   = Value a → Value b
Value (⟨ l ⟩ a) = M l (Value a)

data Env : Ctx → Set v where
    ∅   : Env ∅
    _,_ : Env Γ → Value a → Env (Γ , a)

lookupVar : Env Γ → Γ ∋ a → Value a 
lookupVar (ρ , v) Z     = v
lookupVar (ρ , v) (S x) = lookupVar ρ x 

eval : Γ ⊢ a → Env Γ → Value a
eval true ρ         = 𝔹.true
eval false ρ        = 𝔹.false
eval unit ρ         = tt
eval (lit n) ρ      = n 
eval case x of[zero⇒ expr1 |suc⇒ expr2 ] ρ with (eval x ρ)
...       |  ℕ.zero = eval expr1 ρ
...       |  ℕ.suc n = eval expr2 (ρ , n)

eval (var x) ρ      = lookupVar ρ x
eval (ƛ x) ρ        = λ y → eval x (ρ , y)
eval (f • x) ρ      = eval f ρ (eval x ρ)
eval (plus x y) ρ   = (eval x ρ) + (eval y ρ) 
eval (If cond Then e1 Else e2) ρ with (eval cond ρ)
...       | 𝔹.true  = eval e1 ρ
...       | 𝔹.false = eval e2 ρ

eval (η x) ρ        = return (eval x ρ)
eval (flow ↑ x) ρ   = sub flow (eval x ρ)
eval (label l x) ρ  = sub ⊥-⊑ᵣ (return (eval x ρ))
eval (Let a ⇐ ma In mb) ρ = (eval ma ρ) >>= (eval mb (ρ , (eval a ρ))) 
 