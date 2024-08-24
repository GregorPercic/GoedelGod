module modal-logic where
open import Agda.Primitive
open import logic

postulate
    𝕎 : Set
    𝕀 : Set
    _𝕣_ : 𝕎 → 𝕎 → Set

infixl 80 _𝕣_

private variable
    l k : Level

σ : ∀ l → Set (lsuc l)
σ l = 𝕎 → Set l

postulate
    ℙ : (𝕀 → σ l) → σ l

infixr 70 m¬_
m¬_ : σ l → σ l
m¬_ φ = λ w → ¬ (φ w)

infixl 65 _m∧_
_m∧_ : σ l → σ k → σ _
φ m∧ ψ = λ w → φ w ∧ ψ w

infixl 60 _m∨_
_m∨_ : σ l → σ k → σ _
φ m∨ ψ = λ w → φ w ∨ ψ w

infixr 55 _m→_
_m→_ : σ l → σ k → σ _
φ m→ ψ = λ w → φ w ⇒ ψ w

infixr 45 m∀_
m∀_ : ∀ {A : Set k} → (A → σ l) → σ (l ⊔ k)
m∀_ Φ = λ w → ∀ x → Φ x w

infixr 45 m∃_
m∃_ : ∀ {A : Set k} → (A → σ l) → σ (l ⊔ k)
m∃_ Φ = λ w → ∃[ x ∈ _ ] Φ x w

-- both have precedence 20
□ : σ l → σ l
□ φ = λ w → (v : 𝕎) → w 𝕣 v → φ v

◇ : σ l → σ l
◇ φ = λ w → ∃[ v ∈ 𝕎 ] (w 𝕣 v ∧ φ v)

⟦_⟧ : σ l → Set l
⟦ φ ⟧ = (w : 𝕎) → φ w

G : ∀ l → 𝕀 → σ (lsuc l)
G l x = m∀ (λ (Φ : 𝕀 → σ l) → ℙ Φ m→ Φ x)

infixr 80 ess[_,_][_,_]
ess[_,_][_,_] : ∀ l k → (𝕀 → σ l) → 𝕀 → σ (lsuc k ⊔ l)
ess[ l , k ][ Φ , x ] = Φ x m∧ (m∀ (λ (Ψ : 𝕀 → σ k) → Ψ x m→ □ (m∀ (λ y → Φ y m→ Ψ y))))

NE : ∀ l k → 𝕀 → σ (lsuc l ⊔ lsuc k)
NE l k x = m∀ (λ Φ → ess[ l , k ][ Φ , x ] m→ □ (m∃ Φ))


-- Auxiliary theorems
valid-to-valid-nec : ∀ {Φ : σ l} → ⟦ Φ ⟧ → ⟦ □ Φ ⟧
valid-to-valid-nec valid-Φ w w' w𝕣w' = valid-Φ w'

infixl 10 _⊨_ 
_⊨_ : σ l → σ k → Set _
Φ ⊨ Ψ = ∀ w → Φ w → Ψ w

¬◇-to-□¬ : {Φ : σ l} → m¬ (◇ Φ) ⊨ □ (m¬ Φ)
¬◇-to-□¬ {Φ = Φ} w ¬◇Φw v = ¬[P∧¬Q]→[P→Q] (lemma v)
    where
        lemma : ∀ v → ¬ ((w 𝕣 v) ∧ Φ v)
        lemma = ¬∃-∀¬ ¬◇Φw
        
¬m∃-to-m∀¬ : {Φ : 𝕀 → σ l} → m¬ (m∃ (λ x → Φ x)) ⊨ m∀ (λ x → m¬ Φ x)
¬m∃-to-m∀¬ w ¬∃ x Φx = ¬∃ (exists x Φx)

¬◇∃-to-□∀¬ : {Φ : 𝕀 → σ l} → m¬ (◇ (m∃ (λ x → Φ x))) ⊨ □ (m∀ (λ x → m¬ Φ x))
¬◇∃-to-□∀¬ {Φ = Φ} w ¬◇∃ = λ v w𝕣v → ¬m∃-to-m∀¬ w ((step-one w ¬◇∃) v w𝕣v)
    where
        step-one : m¬ (◇ (m∃ (λ x → Φ x))) ⊨ □ (m¬ (m∃ (λ x → Φ x)))
        step-one = ¬◇-to-□¬

□∀-weakening : {Φ : 𝕀 → σ l} {Ψ : 𝕀 → σ k} → □ (m∀ (λ x → Φ x)) ⊨ □ (m∀ (λ x → Ψ x m→ Φ x))
□∀-weakening w hyp w' w𝕣w' x Ψxw' = hyp w' w𝕣w' x

⊨-MP : {Φ : σ l} {Ψ : σ k} → ⟦ Φ ⟧ → Φ ⊨ Ψ → ⟦ Ψ ⟧
⊨-MP valid-Φ Ψ⊨Φ w = (Ψ⊨Φ w) (valid-Φ w)