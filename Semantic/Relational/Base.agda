{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open BoundedJoinSemilattice using (Carrier)

module Semantic.Relational.Base {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (u : Carrier J) where

open import Data.GMonad.Base using (GMonad)
open import Variable J
open import Context J
open import Purpose J
open import Term J
open import Type J

open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary using (Rel)
open import Agda.Builtin.Unit



variable 
    A B : Set

M : Label → Set → Set
M _ a = a

return : A → M ⊥ A
return a = a

sub : l₁ ⊑ l₂ → M l₁ A → M l₂ A
sub flow ma = ma

_>>=_ : M l₁ A → (A → M l₂ B) → M (l₁ ∘ l₂) B
_>>=_ ma f = f ma

-- GradedMonad : GMonad {lzero} J 
-- GradedMonad = record{
--     M = M;
--     return = return;
--     _>>=_ = _>>=_;
--     sub = sub;
-- }


GradedMonad : GMonad {lzero} J
GradedMonad = record{
    M = λ _ z → z ;
    return = λ z → z ;
    _>>=_ = λ z z₁ → z₁ z  ;
    sub = λ _ z → z}

open import Eval {lzero} J GradedMonad


[_]_~_ : (a : Type) → Rel (Value a) ℓ₂
[ ⟨ l₁ ⟩ t ] x ~ y = l₁ ⊑ u  → ([ t ] x ~ y)
[ a ⇒ b ] f ~ g = ∀ {x y : Value a}  → [ a ] x ~ y → [ b ] f x ~ g y
[ t ] x ~ y = x ≡ y

⟨_⟩_~_ : (Γ : Ctx) → Rel (Env Γ) ℓ₂
⟨ ∅ ⟩ ea ~ eb  = ⊤
⟨ ctx , a ⟩ (ea , va) ~ (eb , vb) = (⟨ ctx ⟩ ea ~ eb) × ([ a ] va ~ vb)