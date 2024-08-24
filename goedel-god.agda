module goedel-god where
open import Agda.Primitive
open import logic
open import modal-logic

private variable
    l k j : Level

postulate
    A1a : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ (λ x → m¬ (Φ x)) m→ m¬ (ℙ Φ)) ⟧
    A1b : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m¬ (ℙ Φ) m→ ℙ (λ x → m¬ (Φ x))) ⟧
    -- A2 is slightly reformulated (curried) to make my functional life easier
    A2 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m∀ (λ (Ψ : 𝕀 → σ k) → □ (m∀ (λ x → Φ x m→ Ψ x)) m→ ℙ Φ m→ ℙ Ψ)) ⟧

T1 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ Φ m→ ◇ (m∃ Φ)) ⟧
T1 w Φ ℙΦw with LEM ((◇ (m∃ Φ)) w)
... | inj₁ yes = yes
... | inj₂ ¬◇∃Φw = explosion (lemma₂ ℙΦw)
    where
        lemma₁ : (ℙ (λ x → m¬ (Φ x))) w
        lemma₁ = A2 w Φ (λ x → m¬ (Φ x)) (□∀-weakening w (¬◇∃-to-□∀¬ w ¬◇∃Φw)) ℙΦw
        
        lemma₂ : (m¬ (ℙ Φ)) w
        lemma₂ = A1a w Φ lemma₁
        
postulate
    A3 : ⟦ ℙ (G l) ⟧
    
C : ⟦ ◇ (m∃ (G l)) ⟧
C w = T1 w (G _) (A3 w)

postulate
    A4 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ Φ m→ □ (ℙ Φ)) ⟧

T2 : ⟦ m∀ (λ x → (G l) x m→ ess[ lsuc l , l ][ G l , x ]) ⟧
T2 {l = l} w x Gx = [ Gx , second-horn ]
    where
        second-horn : (m∀ (λ (Ψ : 𝕀 → σ l) → Ψ x m→ □ (m∀ (λ y → (G l) y m→ Ψ y)))) w
        second-horn Ψ Ψx v w𝕣v y Gy with LEM ((ℙ Ψ) w)
        ... | inj₁ ℙΨw = Gy Ψ ((A4 w Ψ ℙΨw) v w𝕣v)
        ... | inj₂ ¬ℙΨw = explosion ((Gx (λ x → m¬ (Ψ x)) (A1b w Ψ (¬ℙΨw))) Ψx)

postulate
    A5 : ⟦ ℙ (NE l k) ⟧
    
    symm : ∀ {x y} → x 𝕣 y → y 𝕣 x

C2 : ⟦ m∃ (G l) ⟧
C2 {l = l} = ⊨-MP C possible-to-actual
    where
        possible-to-actual : ◇ (m∃ (G l)) ⊨ m∃ (G l)
        possible-to-actual w (exists v [ w𝕣v , (exists x Gx) ])
            = □∃G-at-v w (symm w𝕣v)
            where
                G-ess-x : (ess[ lsuc l , l ][ G l , x ]) v
                G-ess-x = (T2 v) x Gx
                
                NE-x : ((NE (lsuc l) l) x) v
                NE-x = {!   !} -- Gx (NE l l) (A5 v) -- lower (NE l l) from 𝕀 → σ (lsuc l) to 𝕀 → σ l
                
                □∃G-at-v : (□ (m∃ (G l))) v
                □∃G-at-v = NE-x (G _) G-ess-x

T3 : ⟦ □ (m∃ (G l)) ⟧
T3 {l = l} = ⊨-MP C2 actual-to-nec
    where
        actual-to-nec : m∃ (G l) ⊨ □ (m∃ (G l))
        actual-to-nec w (exists x Gx) = □∃G-at-w
            where
                G-ess-x : (ess[ _ , _ ][ G l , x ]) w
                G-ess-x = (T2 w) x Gx
                
                NE-x : ((NE _ _) x) w
                NE-x = {!   !} -- Gx (NE _ _) (A5 w)
                
                □∃G-at-w : (□ (m∃ (G l))) w
                □∃G-at-w = NE-x (G _) G-ess-x