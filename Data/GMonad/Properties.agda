open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open import Data.GMonad.Base using (GMonad)

module Data.GMonad.Properties {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (M : BoundedJoinSemilattice.Carrier J → Set → Set) (G : GMonad J M) where

open import Purpose J
open GMonad G 

open import Relation.Binary.PropositionalEquality
open import Algebra.Definitions _≃_

