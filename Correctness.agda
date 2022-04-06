open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open import Data.GMonad.Base using (GMonad)

module Correctness {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (G : GMonad J) where

open import Erasure.Base using (eval)

