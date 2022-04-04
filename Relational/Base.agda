{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open BoundedJoinSemilattice using (Carrier)
open import Data.GMonad.Base using (GMonad)
open import Agda.Primitive using (lzero)

module Relational.base {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (G : GMonad {lzero} J) (u : Carrier J) where

open import Variable J
open import Context J
open import Purpose J
open import Term J
open import Type J
open GMonad G

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Binary using (Rel; Setoid)
open Setoid using (Carrier)
open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Agda.Builtin.Bool using () renaming (Bool to 𝔹)
open import Agda.Builtin.Unit

-- Value : Type → Setoid c c
-- Value Nat       = Eq.setoid ℕ
-- Value Bool      = Eq.setoid 𝔹
-- Value Unit      = Eq.setoid ⊤
-- Value (a ⇒ b)   = Value b
-- Value (⟨ l ⟩ a) = Eq.setoid (M l (Carrier (Value a)))

Value : Type → Set
Value Nat       = ℕ
Value Bool      = 𝔹
Value Unit      = ⊤
Value (a ⇒ b)   = Value a → Value b
Value (⟨ l ⟩ a) = M l (Value a)


[_]_~_ : ∀{u : Label} → (a : Type) → Rel (Value a) (c l⊔ ℓ₂)
[_]_~_ {u = u} (⟨ l₁ ⟩ t) x y = l₁ ⊑ u  → x ≡ y
-- [_]_~_ {u = u} (a ⇒ b) x y = [ b ] {!  ? !} ~ {!   !}  
[ t ] x ~ y = x ≡ y

data Env : Ctx → Set where
    ∅   : Env ∅
    _,_ : Env Γ → Value a → Env (Γ , a)

lookupVar : Env Γ → Γ ∋ a → Value a 
lookupVar (ρ , v) Z     = v
lookupVar (ρ , v) (S x) = lookupVar ρ x 

eval : Γ ⊢ a → Env Γ → Rel (Value a) (c l⊔ ℓ₂)
eval true ρ  = [_]_~_ {u} Bool 
eval false ρ = [_]_~_ {u} Bool 
eval unit ρ = [_]_~_ {u} Unit 
eval x = {!   !}