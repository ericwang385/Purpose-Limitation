open import Relation.Binary.Lattice using (BoundedJoinSemilattice)

module GMonad {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Purpose J
open import Relation.Binary.Properties.BoundedJoinSemilattice J
open import Variable J


record Functor (F : Set → Set) : Set₁ where
    field
        fmap : (A → B) → F A → F B
    _<$>_ = fmap
    infixl 4 _<$>_

record GMonad (M : Label → Set → Set) : Set (lsuc (c l⊔ ℓ₂)) where
    field
        return : A → M ⊥ A 
        _>>=_ : M l₁ A → (A → M l₂ B) → M (l₁ ∘ l₂) B
        sub : l₁ ⊑ l₂ → M l₁ A → M l₂ A
        functor : Functor (M l)

    join : (M l₁ (M l₂ A)) → M (l₁ ∘ l₂) A
    join ma = ma >>= λ x → x

    fmap : (A → B) → M l₁ A → M l₁ B 
    fmap f ma = Functor.fmap functor f ma
    -- fmap {l₁} f ma = sub (⊑-reflexive (identityʳ l₁)) (ma >>= λ x → return (f x))

    _>>_ : M l₁ A → M l₂ B → M (l₁ ∘ l₂) B 
    ma >> mb = ma >>= λ a → mb
  