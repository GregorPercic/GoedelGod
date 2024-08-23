module goedel-god where
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
    P : (𝕀 → σ l) → σ l

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
m∀_ : ∀ {A : Set k} → (A → σ l) → σ _ -- (l ⊔ k)
m∀_ Φ = λ w → ∀ x → Φ x w

infixr 45 m∃_
m∃_ : ∀ {A : Set k} → (A → σ l) → σ _
m∃_ Φ = λ w → ∃[ x ∈ _ ] Φ x w

-- both have precedence 20
□ : σ l → σ l
□ φ = λ w → (v : 𝕎) → w 𝕣 v → φ v

◇ : σ l → σ l
◇ φ = λ w → ∃[ v ∈ 𝕎 ] (w 𝕣 v ∧ φ v)

⟦_⟧ : σ l → Set l
⟦ φ ⟧ = (w : 𝕎) → φ w

postulate
    A1a : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → P (λ x → m¬ (Φ x)) m→ m¬ (P Φ)) ⟧
    A1b : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m¬ (P Φ) m→ P (λ x → m¬ (Φ x))) ⟧
    A2 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m∀ (λ (Ψ : 𝕀 → σ k) → (□ (m∀ (λ x → Φ x m→ Ψ x)) m∧ P Φ) m→ P Ψ)) ⟧

T1 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → P Φ m→ ◇ (m∃ Φ)) ⟧
T1 w Φ with LEM ((◇ (m∃ Φ)) w) | LEM (P Φ w)
... | inj₁ yes | _ = inj₂ yes
... | _ | inj₂ no  = inj₁ no
... | inj₂ ¬◇∃Φ | inj₁ PΦw = {!   !}

G : ∀ l → 𝕀 → σ (lsuc l)
G l x = m∀ (λ Φ → P Φ m→ Φ x)

postulate
    A3 : ⟦ P (G l) ⟧
    
C : ⟦ ◇ (m∃ (G l)) ⟧
C = {!   !}

postulate
    A4 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → P Φ m→ □ (P Φ)) ⟧
    
infixr 80 _ess_
_ess_ : (𝕀 → σ l) → 𝕀 → σ (lsuc l)
_ess_ Φ x = Φ x m∧ (m∀ (λ (Ψ : 𝕀 → σ _) → Ψ x m→ □ (m∀ (λ y → Φ y m→ Ψ y))))

NE : ∀ l → 𝕀 → σ (lsuc l)
NE l x = m∀ (λ Φ → Φ ess x m→ □ (m∃ Φ))

postulate
    A5 : ⟦ P (NE l) ⟧
    
    symm : ∀ {x y} → x 𝕣 y → y 𝕣 x

T3 : ⟦ □ (m∃ (G l)) ⟧
T3 = {!   !}

C2 : ⟦ m∃ (G l) ⟧
C2 = {!   !}

-- auxiliary
valid-to-nec-valid : ∀ {Φ : σ l} → ⟦ Φ ⟧ → ⟦ □ Φ ⟧
valid-to-nec-valid valid-Φ w w' w𝕣w' = valid-Φ w'

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

□∀-weakening : {Φ : 𝕀 → σ l} {Ψ : 𝕀 → σ k} → □ (m∀ (λ x → Φ x)) ⊨ □ (m∀ (λ x → Ψ x m→ Φ x))
□∀-weakening w hyp w' w𝕣w' x = inj₂ (hyp w' w𝕣w' x)

¬◇∃-to-□∀¬ : {Φ : 𝕀 → σ l} → m¬ (◇ (m∃ (λ x → Φ x))) ⊨ □ (m∀ (λ x → m¬ Φ x))
¬◇∃-to-□∀¬ = {!   !}