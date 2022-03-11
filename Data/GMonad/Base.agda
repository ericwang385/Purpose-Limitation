open import Relation.Binary.Lattice using (BoundedJoinSemilattice)

module Data.GMonad.Base {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Purpose J
open import Relation.Binary.Properties.BoundedJoinSemilattice J
open import Variable J


record Functor (F : Set → Set) : Set₁ where
    field
        fmap : (A → B) → F A → F B
    _<$>_ = fmap
    infixl 4 _<$>_

record GMonad : Set (lsuc (c l⊔ ℓ₂)) where
    field
        M : Label → Set → Set
        return : A → M ⊥ A 
        _>>=_ : M l₁ A → (A → M l₂ B) → M (l₁ ∘ l₂) B
        sub : l₁ ⊑ l₂ → M l₁ A → M l₂ A
        
    join : (M l₁ (M l₂ A)) → M (l₁ ∘ l₂) A
    join ma = ma >>= λ x → x

    fmap : (A → B) → M l₁ A → M l₁ B 
    fmap f ma = sub (⊑-reflexive (identityʳ _)) (ma >>= λ x → return (f x))

    functor : Functor (M l)
    functor = record {fmap = fmap}
    
    _>>_ : M l₁ A → M l₂ B → M (l₁ ∘ l₂) B 
    ma >> mb = ma >>= λ a → mb
   