module goedel-god where
open import Agda.Primitive
open import logic
open import modal-logic

private variable
    l k : Level

postulate
    A1a : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ (λ x → m¬ (Φ x)) m→ m¬ (ℙ Φ)) ⟧
    A1b : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m¬ (ℙ Φ) m→ ℙ (λ x → m¬ (Φ x))) ⟧
    A2 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m∀ (λ (Ψ : 𝕀 → σ k) → □ (m∀ (λ x → Φ x m→ Ψ x)) m→ ℙ Φ m→ ℙ Ψ)) ⟧
    -- A2 is slightly reformulated (curried) to make my functional life easier

T1 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ Φ m→ ◇ (m∃ Φ)) ⟧
T1 w Φ ℙΦw with LEM ((◇ (m∃ Φ)) w)
... | inj₁ yes = yes
... | inj₂ ¬◇∃Φ = explosion (lemma₂ ℙΦw)
    where
        lemma₁ : (ℙ (λ x → m¬ (Φ x))) w
        lemma₁ = A2 w Φ (λ x → m¬ (Φ x)) (□∀-weakening w (¬◇∃-to-□∀¬ w ¬◇∃Φ)) ℙΦw
        
        lemma₂ : (m¬ (ℙ Φ)) w
        lemma₂ = A1a w Φ lemma₁
        
postulate
    A3 : ⟦ ℙ (G l) ⟧
    
C : ⟦ ◇ (m∃ (G l)) ⟧
C w = T1 w (G _) (A3 w)

postulate
    A4 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ Φ m→ □ (ℙ Φ)) ⟧
    A5 : ⟦ ℙ (NE l) ⟧
    
    symm : ∀ {x y} → x 𝕣 y → y 𝕣 x

T3 : ⟦ □ (m∃ (G l)) ⟧
T3 = {!   !}

C2 : ⟦ m∃ (G l) ⟧
C2 = {!   !}