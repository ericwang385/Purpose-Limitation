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