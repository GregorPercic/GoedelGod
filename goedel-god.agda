module goedel-god where
open import Agda.Primitive
open import logic
open import modal-logic

open _∧_

private variable
    l k : Level

-- For reference, all axioms, theorems, and definitions have names from the original Isabelle implementation.

postulate
    -- A negation of a property Φ is positive iff Φ is not positive.
    -- For convenience, the equivalence divided into two axioms.
    A1a : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ (λ x → m¬ (Φ x)) m→ m¬ (ℙ Φ)) ⟧
    A1b : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m¬ (ℙ Φ) m→ ℙ (λ x → m¬ (Φ x))) ⟧
    
    -- If a positive property Φ neccessarily implies a property Ψ, Ψ is also positive.
    -- It is a slightly modified form of the origional axiom in Isabelle; it is curried
    -- to make our lives much easier.
    A2 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → m∀ (λ (Ψ : 𝕀 → σ k) → □ (m∀ (λ x → Φ x m→ Ψ x)) m→ ℙ Φ m→ ℙ Ψ)) ⟧

-- Every positive property Φ is possibly exemplified.
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
    -- Being God-like is a positive property.
    A3 : ⟦ ℙ (G l) ⟧

-- Possibly, a God-like individual exists.
C : ⟦ ◇ (m∃ (G l)) ⟧
C w = T1 w (G _) (A3 w)

postulate
    -- Every positive property Φ is necessarily positive.
    A4 : ⟦ m∀ (λ (Φ : 𝕀 → σ l) → ℙ Φ m→ □ (ℙ Φ)) ⟧

-- The property of being God-like is an essence of every God-like individual
T2 : ⟦ m∀ (λ x → (G l) x m→ ess[ lsuc l , l ][ G l , x ]) ⟧
T2 {l = l} w x Gx = [ Gx , second-horn ]
    where
        second-horn : (m∀ (λ (Ψ : 𝕀 → σ l) → Ψ x m→ □ (m∀ (λ y → (G l) y m→ Ψ y)))) w
        second-horn Ψ Ψx v w𝕣v y Gy with LEM ((ℙ Ψ) w)
        ... | inj₁ ℙΨw = Gy Ψ ((A4 w Ψ ℙΨw) v w𝕣v)
        ... | inj₂ ¬ℙΨw = explosion ((Gx (λ x → m¬ (Ψ x)) (A1b w Ψ (¬ℙΨw))) Ψx)

postulate
    -- Necessary existence is a positive property.
    A5 : ⟦ ℙ (NE l k) ⟧
    
    -- We need to postulate the symmetry of the world accessibility relation
    -- to complete Gödel's proof.
    symm : ∀ {x y} → x 𝕣 y → y 𝕣 x

-- A God-like individual exists.
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
                NE-x = (lift-G x v (lift-G x v Gx)) (NE (lsuc l) l) (A5 v)
                
                □∃G-at-v : (□ (m∃ (G l))) v
                □∃G-at-v = NE-x (G l) G-ess-x

-- Necessarily, a God-like individual exists.
T3 : ⟦ □ (m∃ (G l)) ⟧
T3 {l = l} = ⊨-MP C2 actual-to-nec
    where
        actual-to-nec : m∃ (G l) ⊨ □ (m∃ (G l))
        actual-to-nec w (exists x Gx) = □∃G-at-w
            where
                G-ess-x : (ess[ (lsuc l) , l ][ G l , x ]) w
                G-ess-x = (T2 w) x Gx
                
                NE-x : ((NE (lsuc l) l) x) w
                NE-x = (lift-G x w (lift-G x w Gx)) (NE (lsuc l) l) (A5 w)
                
                □∃G-at-w : (□ (m∃ (G l))) w
                □∃G-at-w = NE-x (G l) G-ess-x


-- Additional results

-- If a property is not positive, a God-like individual does not have it.
Flawlessness : ⟦ m∀ (λ Φ → m∀ (λ x → ((G l) x m→ (m¬ (ℙ Φ) m→ m¬ (Φ x))))) ⟧
Flawlessness w Φ x Gx ¬[ℙΦ] = Gx (λ x → m¬ (Φ x)) ℙ[¬Φ]
    where
        ℙ[¬Φ] : (ℙ (λ x → m¬ (Φ x))) w
        ℙ[¬Φ] = A1b w Φ ¬[ℙΦ]

-- Using Leibniz's equality, every two God-like individuals are identical.
Monotheism : ⟦ m∀ (λ x → m∀ (λ y → ((G l) x m→ ((G l) y m→ (x mL= y))))) ⟧
Monotheism w x y Gx Gy Φ Φx with LEM (ℙ Φ w)
... | inj₁ yes = Gy Φ yes
... | inj₂ no = explosion ((Gx (λ x → m¬ (Φ x)) ℙ[¬Φ]) Φx)
    where
        ℙ[¬Φ] : (ℙ (λ x → m¬ (Φ x))) w
        ℙ[¬Φ] = A1b w Φ no

-- This version of Gödel's ontological proof entails an undesirable consequence: modal collapse;
-- for every proposition Φ, Φ holds necessarily.
MC : ⟦ m∀ (λ (Φ : σ l) → (Φ m→ (□ Φ))) ⟧
MC w Φ proof = lemma (C2 w)
    where
        ω : 𝕀 → σ _
        ω = λ x → Φ
        
        lemma : (m∃ (G _)) w → (□ Φ) w
        lemma (exists x Gx) = nec-Φ
            where
                sublemma₁ : (m∀ (λ Ψ → Ψ x m→ □ (m∀ (λ y → (G _) y m→ Ψ y)))) w
                sublemma₁ = proj₂ (T2 w x Gx)
                
                sublemma₂ : (□ (m∀ (λ y → (G _) y m→ Φ))) w
                sublemma₂ = sublemma₁ ω proof
                
                nec-Φ : (□ Φ) w
                nec-Φ v w𝕣v = subsublemma (C2 v)
                    where
                        subsublemma : (m∃ (G _)) v → Φ v
                        subsublemma (exists y Gy) = sublemma₂ v w𝕣v y Gy