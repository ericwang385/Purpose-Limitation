{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open BoundedJoinSemilattice using (Carrier)

module Relational.base {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (u : Carrier J) where

open import Data.GMonad.Base using (GMonad)
open import Variable J
open import Context J
open import Purpose J
open import Term J
open import Type J

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Binary using (Rel; Setoid)
open Setoid using (Carrier)
open import Agda.Primitive using (lzero)


variable 
    A B : Set

M : Label → Set → Set
M l a = a

return : A → M ⊥ A
return a = a

sub : l₁ ⊑ l₂ → M l₁ A → M l₂ A
sub flow ma = ma

_>>=_ : M l₁ A → (A → M l₂ B) → M (l₁ ∘ l₂) B
_>>=_ {l₁ = l₁} {l₂ = l₂} ma f = f ma



GradedMonad : GMonad {lzero} J
GradedMonad = record{
    M = M ;
    return = return ;
    _>>=_ = _>>=_ ;
    sub = sub}

open import Eval J GradedMonad


[_]_~_ : (a : Type) → Rel (Value a) (c l⊔ ℓ₂)
[ ⟨ l₁ ⟩ t ] x ~ y = l₁ ⊑ u  → ([ t ] x ~ y)
[ a ⇒ b ] f ~ g = ∀ {x y : Value a}  → [ a ] x ~ y → [ b ] f x ~ g y
[ t ] x ~ y = x ≡ y