module modal-logic where
open import Agda.Primitive
open import logic

open _∧_

postulate
    -- The type of possible worlds.
    𝕎 : Set
    -- The type of individuals. Since it is fixed, this version of Gödel's proof
    -- uses possibilist quantification.
    𝕀 : Set
    -- The world accessibility relation.
    _𝕣_ : 𝕎 → 𝕎 → Set

infixl 80 _𝕣_

-- Level variables are needed because the definitions of m∀ and m∃ force typing into higher type universes.
-- They need to be explicit because this eases type and level inference for Agda at some points.
-- Unfortunately, this makes the notation very ugly, and for intuitive understanding, you should simply
-- ignore the type variables in axioms, definitions, theorems, and proofs.
private variable
    l k : Level

σ : ∀ l → Set (lsuc l)
σ l = 𝕎 → Set l

postulate
    -- The predicate "being a positive property."
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

infixr 50 _m↔_
_m↔_ : σ l → σ k → σ _
φ m↔ ψ = (φ m→ ψ) m∧ (ψ m→ φ)

infixr 45 m∀_
m∀_ : ∀ {A : Set k} → (A → σ l) → σ (l ⊔ k)
m∀_ Φ = λ w → ∀ x → Φ x w

infixr 45 m∃_
m∃_ : ∀ {A : Set k} → (A → σ l) → σ (l ⊔ k)
m∃_ Φ = λ w → ∃[ x ∈ _ ] Φ x w

-- Leibnizian equality
infixr 90 _mL=_ 
_mL=_ : 𝕀 → 𝕀 → σ (lsuc l)
x mL= y = m∀ (λ (Φ : 𝕀 → σ _) → Φ x m→ Φ y)

-- Both have precedence 20.
□ : σ l → σ l
□ φ = λ w → (v : 𝕎) → w 𝕣 v → φ v

◇ : σ l → σ l
◇ φ = λ w → ∃[ v ∈ 𝕎 ] (w 𝕣 v ∧ φ v)

⟦_⟧ : σ l → Set l
⟦ φ ⟧ = (w : 𝕎) → φ w

-- The definition of the property of being God-like (D1):
-- x is God-like iff x has every positive property Φ.
G : ∀ l → 𝕀 → σ (lsuc l)
G l x = m∀ (λ (Φ : 𝕀 → σ l) → ℙ Φ m→ Φ x)

-- The definition of essence (D2):
-- Φ is an essence of x iff x exemplifies Φ, and for all properties Ψ which x exemplifies,
-- necessarily, for all individuals y, their exemplification of Φ implies their exemplification of ψ.
infixr 80 ess[_,_][_,_]
ess[_,_][_,_] : ∀ l k → (𝕀 → σ l) → 𝕀 → σ _ -- (lsuc k ⊔ l)
ess[ l , k ][ Φ , x ] = Φ x m∧ (m∀ (λ (Ψ : 𝕀 → σ k) → Ψ x m→ □ (m∀ (λ y → Φ y m→ Ψ y))))

-- The definition of necessary existence (D3):
-- x exists necessarily iff all of its essences are necessarily exemplified.
NE : ∀ l k → 𝕀 → σ _ -- (lsuc l ⊔ lsuc k)
NE l k x = m∀ (λ (Φ : 𝕀 → σ _) → ess[ l , k ][ Φ , x ] m→ □ (m∃ Φ))

infixl 10 _⊨_ 
_⊨_ : σ l → σ k → Set _
Φ ⊨ Ψ = ∀ w → Φ w → Ψ w

-- Regrettably, we need this because level requirements become paradoxical
-- when trying to prove ∃x.Gx and □∃x.Gx. Thus far, I have been unable
-- to derive a contradiction from it, which is good.
postulate
    lift-G : (x : 𝕀) → (G l) x ⊨ (G (lsuc l)) x 


-- Auxiliary theorems

-- We don't actually need this one one, but let it stay.
valid-to-valid-nec : ∀ {Φ : σ l} → ⟦ Φ ⟧ → ⟦ □ Φ ⟧
valid-to-valid-nec valid-Φ w w' w𝕣w' = valid-Φ w'

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

-- Since Leibnizian equality is usually defined as x mL= y ≡ ∀Φ.(Φx ↔ Φy), I prove that
-- our definition is equivalent to the classical one.
mL=-is-legit : ∀ x y → ⟦ x mL= y m↔ (m∀ (λ (Φ : 𝕀 → σ l) → Φ x m↔ Φ y)) ⟧
mL=-is-legit x y w = [ (λ x=y φ → [ x=y φ , contraposition (x=y (λ x → m¬ (φ x))) ]) ,
                       (λ equiv φ → proj₁ (equiv φ)) ]