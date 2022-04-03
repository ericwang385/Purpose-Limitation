{-# OPTIONS --cumulativity #-}

open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open import Data.GMonad.Base using (GMonad)
open import Relation.Nullary
open BoundedJoinSemilattice using (Carrier ; _≤_)

module Erasure.Deciable {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) 
 (u : Carrier J) (_⊑?_ :(l u : Carrier J) → Dec(_≤_ J l u)) where

open import Variable J
open import Context J
open import Purpose J
open import Term J
open import Type J

open import Agda.Builtin.Nat using (_+_) renaming (Nat to ℕ)
open import Agda.Builtin.Bool using () renaming (Bool to 𝔹)
open import Agda.Builtin.Unit
open import Relation.Nullary.Negation using (contradiction)

variable
    A B : Set ℓ₂

M : Label → Set ℓ₂ → Set ℓ₂
M l a with (l ⊑? u)
...  | yes p = a
...  | no ¬p = ⊤

return : A → M ⊥ A
return a with (⊥ ⊑? u)
... | yes p = a
... | no ¬p = contradiction ⊥-⊑ᵣ ¬p 

_>>=_ : M l₁ A → (A → M l₂ B) → M (l₁ ∘ l₂) B
_>>=_ {l₁ = l₁} {l₂ = l₂} ma f with ((l₁ ∘ l₂) ⊑? u) | (l₁ ⊑? u) | (l₂ ⊑? u)
... | yes p | yes p1 | yes p2 = f ma
... | no ¬p | _      | _      = tt
... | yes p | yes p1 | no ¬p2 = contradiction (⊑-trans (y≤x∨y l₁ l₂) p) ¬p2
... | yes p | no ¬p1 | yes p2 = contradiction (⊑-trans (x≤x∨y l₁ l₂) p) ¬p1
... | yes p | no ¬p1 | no ¬p2 = contradiction (⊑-trans (y≤x∨y l₁ l₂) p) ¬p2


sub : l₁ ⊑ l₂ → M l₁ A → M l₂ A
sub {l₁ = l₁} {l₂ = l₂} flow ma with (l₁ ⊑? u) | (l₂ ⊑? u) 
... | yes p | yes p' = ma
... | _     | no ¬p' = tt
... | no ¬p | yes p' = contradiction (⊑-trans flow p') ¬p

GradedMonad : GMonad {ℓ₂} J
GradedMonad = record{
    M = M ;
    return = return ;
    _>>=_ = _>>=_ ;
    sub = sub} 

open import Eval J GradedMonad