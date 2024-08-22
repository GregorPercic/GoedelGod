module goedel-god where
open import Agda.Primitive
open import logic

postulate
    𝕎 : Set
    𝕀 : Set
    _𝕣_ : 𝕎 → 𝕎 → Set

infixl 80 _𝕣_


σ : ∀ {ℓ} → Set (lsuc ℓ)
σ {ℓ} = 𝕎 → Set ℓ

postulate
    P : ∀ {l} → (𝕀 → σ {l}) → σ {l}

infixr 70 m¬_
m¬_ : ∀ {l} → σ {l} → σ
m¬_ φ = λ w → ¬ (φ w)

infixl 65 _m∧_
_m∧_ : ∀ {l k} → σ {l} → σ {k} → σ
φ m∧ ψ = λ w → φ w ∧ ψ w

infixl 60 _m∨_
_m∨_ : ∀ {l k} → σ {l} → σ {k} → σ
φ m∨ ψ = λ w → φ w ∨ ψ w

infixr 55 _m→_
_m→_ : ∀ {l k} → σ {l} → σ {k} → σ
φ m→ ψ = λ w → φ w ⇒ ψ w

infixr 50 _m↔_
_m↔_ : ∀ {l k} → σ {l} → σ {k} → σ
φ m↔ ψ = λ w → φ w ⇔ ψ w

infixr 45 m∀_
m∀_ : ∀ {l k} → ∀ {A : Set k} → (A → σ {l}) → σ {l ⊔ k}
m∀_ {l} {k} {A} Φ = λ w → (x : A) → Φ x w

infixr 45 m∃_
m∃_ : ∀ {l k} → ∀ {A : Set k} → (A → σ {l}) → σ {l ⊔ k}
m∃_ {l} {k} {A} Φ = λ w → ∃[ x ∈ A ] Φ x w

-- both have precedence 20
□ : ∀ {l} → σ {l} → σ
□ φ = λ w → (v : 𝕎) → w 𝕣 v → φ v

◇ : ∀ {l} → σ {l} → σ
◇ φ = λ w → ∃[ v ∈ 𝕎 ] (w 𝕣 v ∧ φ v)

⟦_⟧ : ∀ {ℓ} → σ → Set ℓ
⟦ φ ⟧ = (w : 𝕎) → φ w

postulate
    A1a : ⟦ m∀_ {lzero} (λ Φ → P (λ x → m¬ (Φ x)) m→ m¬ (P Φ)) ⟧ -- {lzero} {lsuc lzero}
    A1b : ⟦ m∀_ {lzero} (λ Φ → m¬ (P Φ) m→ P (λ x → m¬ (Φ x))) ⟧ -- {lzero} {lsuc lzero}
    A2 : ⟦ m∀ (λ Φ → m∀ (λ Ψ → (□ (m∀_ {lzero} (λ x → Φ x m→ Ψ x)) m∧ P Φ) m→ P Ψ)) ⟧ -- {lzero} {lzero}

T1 : ⟦ m∀_ {lzero} (λ Φ → P Φ m→ ◇ (m∃ Φ)) ⟧ -- {lzero} {lsuc lzero}
T1 = {!   !}

G : 𝕀 → σ
G x =  m∀_ {lzero} (λ Φ → P Φ m→ Φ x)

postulate
    A3 : ⟦ P G ⟧
    
C : ⟦ ◇ (m∃ G) ⟧
C = {!   !}

postulate
    A4 : ⟦ m∀_ {lzero} (λ Φ → P Φ m→ □ (P Φ)) ⟧
    
infixr 80 _ess_
_ess_ : (𝕀 → σ {lzero}) → 𝕀 → σ {lsuc lzero}
_ess_ Φ x = Φ x m∧ (m∀_ {A = 𝕀 → σ} (λ Ψ → Ψ x m→ □ (m∀ (λ y → Φ y m→ Ψ y))))

NE : 𝕀 → σ
NE x = m∀ (λ Φ → Φ ess x m→ □ (m∃ Φ))

postulate
    A5 : ⟦ P NE ⟧
    
    symm : ∀ {x y} → x 𝕣 y → y 𝕣 x

T3 : ⟦ □ (m∃ G) ⟧
T3 = {!   !}

C2 : ⟦ m∃ G ⟧
C2 = {!   !}