{-# OPTIONS --cumulativity #-}
open import Relation.Binary.Lattice using (BoundedJoinSemilattice)
open BoundedJoinSemilattice using (Carrier)

module Semantic.Erasure.Correctness {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) (u : Carrier J) where

open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl)
open import Agda.Builtin.Nat using (_+_) renaming (Nat to ℕ)
open import Agda.Builtin.Bool using () renaming (Bool to 𝔹)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_) renaming (_,_ to _,'_)
open import Data.List

open import Semantic.Erasure.Base J u
open import Eval J GradedMonad
open import Variable J
open import Context J renaming (_,_ to _,ᶜ_)
open import Purpose J
open import Term J GradedMonad
open import Type J

suc-injective : {ℓ : Level} {x y : ℕ} → _≡_ {ℓ} (ℕ.suc x) (ℕ.suc y) → _≡_ {ℓ} x y
suc-injective refl = refl

plus-≡ : {ℓ : Level} {a b c d : ℕ} → _≡_ {ℓ} a b → _≡_ {ℓ} c d →  _≡_ {ℓ} (a + c) (b + d)
plus-≡ refl refl = refl

noninterference : {t : Type} → (term : Γ ⊢ t)
    → (env₁ env₂ : Env Γ) → ⟨ Γ ⟩ env₁ ~ env₂ → [ t ] (eval term env₁) ~ (eval term env₂)
noninterference unit e1 e2 enveq = refl
noninterference true e1 e2 enveq = refl
noninterference false e1 e2 enveq = refl
noninterference (lit x) e1 e2 enveq = refl

noninterference {Γ ,ᶜ a} (var x) e1 e2 enveq with e1 | e2 | enveq | x
... | (e1 , x) | (e2 , y) | (p ,' v) | Z = v
... | (e1 , _) | (e2 , _) | (p ,' v) | (S x) = noninterference {Γ} (var x) e1 e2 p

noninterference {Γ} (case term of[zero⇒ term₁ |suc⇒ term₂ ]) 
                e1 e2 enveq with (noninterference {Γ} term e1 e2 enveq)
... | p  with (eval term e1) | (eval term e2)
...     | ℕ.zero | ℕ.zero = noninterference {Γ} term₁ e1 e2 enveq
...     | ℕ.suc x | ℕ.suc y = noninterference {Γ ,ᶜ Nat} term₂ (e1 , x) (e2 , y) (enveq ,' (suc-injective {ℓ₂} p))

noninterference {Γ} {a ⇒ b} (ƛ term) e1 e2 enveq {x} {y} inputeq
                = (noninterference {Γ ,ᶜ a} term (e1 , x) (e2 , y) (enveq ,' inputeq))

noninterference {Γ} (_•_ {a} term term₁) e1 e2 enveq 
                = (noninterference {Γ} term e1 e2 enveq) (noninterference {Γ} (term₁) e1 e2 enveq)

noninterference {Γ} (plus term term₁) e1 e2 enveq 
                = plus-≡ (noninterference {Γ} term e1 e2 enveq) (noninterference {Γ} (term₁) e1 e2 enveq)

noninterference {Γ} (If term Then term₁ Else term₂) e1 e2 enveq 
                with (noninterference {Γ} term e1 e2 enveq)
... | p with (eval term e1) | (eval term e2)
...     | 𝔹.true | 𝔹.true = noninterference {Γ} term₁ e1 e2 enveq
...     | 𝔹.false | 𝔹.false = noninterference {Γ} term₂ e1 e2 enveq

noninterference {Γ} (η term) e1 e2 enveq = λ x y → noninterference {Γ} term e1 e2 enveq

noninterference {Γ} (flow ↑ term) e1 e2 enveq = λ x y → noninterference {Γ} term e1 e2 enveq (⊑-trans flow x) (⊑-trans flow y)

noninterference {Γ} (label l term) e1 e2 enveq = λ x y → noninterference {Γ} term e1 e2 enveq

noninterference {Γ} (Let_⇐_In_ {a} {l₁} {l₂} term term₁ term₂) e1 e2 enveq with (noninterference {Γ} term e1 e2 enveq) | (noninterference {Γ} term₁ e1 e2 enveq)
... | p | q 
    = λ x y → noninterference {Γ ,ᶜ a} term₂ (e1 , eval term e1) (e2 , eval term e2) (enveq ,' p) (q (⊑-trans (x≤x∨y l₁ l₂) x) (⊑-trans (x≤x∨y l₁ l₂) y)) (⊑-trans (y≤x∨y l₁ l₂) x) ((⊑-trans (y≤x∨y l₁ l₂) y))

noninterference {Γ} (write term []) e1 e2 enveq = λ x y termeq → refl

noninterference {Γ} (write term (x ∷ xs)) e1 e2 enveq 
    = λ x y termeq → λ x' y' xeq → noninterference {Γ} (write term xs) e1 e2 enveq x y termeq