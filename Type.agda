open import Purpose
module Type (l : Purpose) where

open import Relation.Nullary public

open Purpose.Purpose l public

infixr 10 _⇒_

data Type : Set where
    Nat  : Type
    Bool : Type
    _⇒_  : (a b : Type) → Type
    ⟨_⟩_ : Label → Type → Type