open import Purpose
module Type (p : Purpose) where

open import Relation.Nullary
open import GMonad p
open Purpose.Purpose p public

infixr 10 _⇒_

data Type : Set where
    Nat  : Type
    Bool : Type
    _⇒_  : (a b : Type) → Type
    -- Labeled data with purpose
    ⟨_⟩_ : Label → Type → Type