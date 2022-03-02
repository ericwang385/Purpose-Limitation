open import Purpose 

module GMonad (p : Purpose) where

open Purpose.Purpose p

variable
    A B : Set
    l l₁ l₂ : Label

record Functor (F : Label → Set → Set) : Set₁ where
    field
        fmap : (A → B) → F l A → F l B
    _<$>_ = fmap
    infixl 4 _<$>_

record Applicative (F : Label → Set → Set) : Set₁ where
    field
        pure : A → F l A -- not sure
        _<*>_ : F l (A → B) → F l A → F l B
        functor : Functor F
    infixl 4 _<*>_

record GMonad (M : Label → Set → Set) : Set₁ where
    field
        return : A → M ⊥ A 
        _>>=_ : M l₁ A → (A → M l₂ B) → M (l₁ ◦ l₂) B
        applicative : Applicative M

    join : (M l₁ (M l₂ A)) → M (l₁ ◦ l₂) A
    join ma = ma >>= λ x → x

    _>>_ : ∀ {A B} → M l₁ A → M l₂ B → M (l₁ ◦ l₂) B 
    ma >> mb = ma >>= λ a → mb
 