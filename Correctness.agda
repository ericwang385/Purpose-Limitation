open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open import Data.GMonad.Base using (GMonad)

module Correctness {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (G : GMonad J) where

open import Variable J
open import Context J
open import Purpose J
open import Term J
open import Type J
open import Eval J G
open GMonad G

