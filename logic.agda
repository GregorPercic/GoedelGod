module logic where
open import Agda.Primitive

private variable
    ℓ ℓ' : Level

data ⊥ {ℓ} : Set ℓ where

infixr 20 ¬_
¬_ : Set ℓ → Set ℓ
¬_ {ℓ} P = P → ⊥ {ℓ}

infixl 18 _∧_
infixl 16 _∨_

record _∧_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ ⊔ ℓ') where
    constructor [_,_]
    field
        proj₁ : P
        proj₂ : Q
-- open _∧_

data _∨_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ ⊔ ℓ') where
    inj₁ : P → P ∨ Q
    inj₂ : Q → P ∨ Q

data Exists (A : Set ℓ) (P : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
    exists : (a : A) → P a → Exists A P
syntax Exists A (λ x → P) = ∃[ x ∈ A ] P
    
infixr 14 _⇒_
_⇒_ : Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
P ⇒ Q = P → Q

postulate
    LEM : (P : Set ℓ) → P ∨ ¬ P

explosion : {P : Set ℓ} → ⊥ {ℓ'} → P
explosion ()

¬∃-∀¬ : {A : Set ℓ} {P : A → Set (ℓ ⊔ ℓ')} → ¬ (∃[ x ∈ A ] P x) → (∀ x → ¬ (P x))
¬∃-∀¬ ¬∃ x Px = ¬∃ (exists x Px)

¬[P∧¬Q]→[P→Q] : {P : Set ℓ} {Q : Set (ℓ ⊔ ℓ')} → ¬ (P ∧ Q) → (P → ¬ Q)
¬[P∧¬Q]→[P→Q] {P = P} {Q = Q} hyp p with LEM Q
... | inj₁ yes = explosion (hyp [ p , yes ])
... | inj₂ no = no