{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open BoundedJoinSemilattice using (Carrier)

module Semantic.Relational.Base {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (u : Carrier J) where

open import Data.GMonad.Base using (GMonad)
open import Variable J
open import Context J
open import Purpose J
open import Type J

open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary using (Rel)
open import Agda.Builtin.Unit
open import Data.List using (_∷_)

GradedMonad : GMonad {lzero} J
GradedMonad = record{
    M = λ _ z → z ;
    return = λ z → z ;
    _>>=_ = λ z z₁ → z₁ z  ;
    sub = λ _ z → z}

open import Eval {lzero} J GradedMonad
open import Term {lzero} J GradedMonad

[_]_~_ : (a : Type) → Rel (Value a) ℓ₂
[ ⟨ l₁ ⟩ t ] x ~ y = l₁ ⊑ u  → [ t ] x ~ y
[ IO⟨ l₁ ⟩ t ] (x ∷ xs) ~ (y ∷ ys) = l₁ ⊑ u  → [ t ] x ~ y
[ a ⇒ b ] f ~ g = ∀ {x y : Value a}  → [ a ] x ~ y → [ b ] f x ~ g y
[ t ] x ~ y = x ≡ y

⟨_⟩_~_ : (Γ : Ctx) → Rel (Env Γ) ℓ₂
⟨ ∅ ⟩ ea ~ eb  = ⊤
⟨ ctx , a ⟩ (ea , va) ~ (eb , vb) = (⟨ ctx ⟩ ea ~ eb) × ([ a ] va ~ vb)