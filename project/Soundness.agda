module Soundness (AtomicFormula : Set) where
  open import KripkeFrame AtomicFormula
  open import HProp
  open import NaturalDeduction AtomicFormula
  import Relation.Binary.PropositionalEquality as Eq
  open Eq renaming ([_] to [|_|])
  open Eq.≡-Reasoning


  module _ (Fr : KripkeFrame) where
    open KripkeFrame Fr
    ℙ = W → HProp

    ⟦_⟧ : Formula → ℙ
    ⟦ ` P ⟧   w = Val w P
    ⟦ ⊤ ⟧     w = ⊤ʰ
    ⟦ ⊥ ⟧     w = ⊥ʰ
    ⟦ φ ∧ ψ ⟧ w = ⟦ φ ⟧ w ∧ʰ ⟦ ψ ⟧ w
    ⟦ φ ∨ ψ ⟧ w = ⟦ φ ⟧ w ∨ʰ ⟦ ψ ⟧ w
    ⟦ φ ⇒ ψ ⟧ w = ⟦ φ ⟧ w ⇒ʰ ⟦ ψ ⟧ w
    ⟦ □ φ ⟧ w = ∀ʰ W (λ w' → (w ≤ₕ w') ⇒ʰ ⟦ φ ⟧ w')
    ⟦ ◇ φ ⟧ w = ∃ʰ W (λ w' → (w ≤ₕ w') ∧ʰ ⟦ φ ⟧ w')

    ⟦_⟧ₑ : Hypotheses  → ℙ             -- unicode \[[ \]] \_e
    ⟦ [] ⟧ₑ    w = ⊤ʰ
    ⟦ φ ∷ Δ ⟧ₑ w = ⟦ φ ⟧ w ∧ʰ ⟦ Δ ⟧ₑ w

    -- helpers

    ++-elim₁ : (Γ Δ : Hypotheses) → {w : W} → proof (⟦ Γ ++ Δ ⟧ₑ w) → proof(⟦ Γ ⟧ₑ w)
    ++-elim₁ [] Δ p = ⊤ʰ-intro
    ++-elim₁ (x ∷ Γ) Δ p = ∧ʰ-intro (∧ʰ-elim₁ p) (++-elim₁ Γ Δ (∧ʰ-elim₂ p))

    ++-elim₂ : (Γ Δ : Hypotheses) → {w : W} → proof (⟦ Γ ++ Δ ⟧ₑ w) → proof(⟦ Δ ⟧ₑ w)
    ++-elim₂ [] Δ p = p
    ++-elim₂ (x ∷ Γ) Δ p = ++-elim₂ Γ Δ (∧ʰ-elim₂ p)

    ++-intro : (Γ Δ : Hypotheses) → {w : W}  → proof(⟦ Γ ⟧ₑ w) → proof(⟦ Δ ⟧ₑ w) → proof (⟦ Γ ++ Δ ⟧ₑ w)
    ++-intro [] Δ p q = q
    ++-intro (x ∷ Γ) Δ p q = ∧ʰ-intro (∧ʰ-elim₁ p) (++-intro Γ Δ (∧ʰ-elim₂ p) q)

    prove-Δ₂ : (Δ₁ Δ₂ : Hypotheses) (φ : Formula) {w : W} → proof (⟦ Δ₁ ++ φ ∷ Δ₂ ⟧ₑ w) → proof (⟦ Δ₂ ⟧ₑ w)
    prove-Δ₂ [] Δ₂ φ p = ∧ʰ-elim₂ p
    prove-Δ₂ (_ ∷ Δ₁) Δ₂ φ p = prove-Δ₂ Δ₁ Δ₂ φ (∧ʰ-elim₂ p)

    proof-exchange : (Γ Δ : Hypotheses) (φ ψ : Formula) {w : W}
                     → proof ( ⟦ Γ ++ φ ∷ ψ ∷ Δ ⟧ₑ w )
                     → proof ( ⟦ Γ ++ ψ ∷ φ ∷ Δ ⟧ₑ w )
    proof-exchange [] Δ φ ψ p =
                   ∧ʰ-intro
                     (∧ʰ-elim₁ (∧ʰ-elim₂ p))
                     (∧ʰ-intro (∧ʰ-elim₁ p) (∧ʰ-elim₂ (∧ʰ-elim₂ p)))
    proof-exchange (x ∷ Γ) Δ φ ψ p = ∧ʰ-intro (∧ʰ-elim₁ p) (proof-exchange Γ Δ φ ψ (∧ʰ-elim₂ p))

    at-world : {w w' : W} {φ : Formula} →
          proof (⟦ □ φ ⟧ w) → w ≤ₖ w' → proof (⟦ φ ⟧ w')
    at-world {w = w} {w' = w'} {φ = φ} p w≤w' = ⇒ʰ-elim w≤w' (∀ʰ-elim p w')

    □-monotonicity : {w w' : W} {φ : Formula} → proof (⟦ □ φ ⟧ w) → proof (w ≤ₕ w') → proof (⟦ □ φ ⟧ w')
    □-monotonicity p q = ∀ʰ-intro (λ w'' → ⇒ʰ-intro (λ r → ⇒ʰ-elim (≤-transitive q r) (∀ʰ-elim p w'')))

    box-∧-map-to-box-map : {As : List Formula} {w w' : W} → w ≤ₖ w' → proof (⟦ box-∧-map As ⟧ w') → proof (⟦ box-map As ⟧ₑ w')
    box-∧-map-to-box-map {[]} w≤w' p = p
    box-∧-map-to-box-map {φ ∷ φs} w≤w' p = ∧ʰ-intro (∧ʰ-elim₁ p) (box-∧-map-to-box-map {φs} w≤w' (∧ʰ-elim₂ p))

    -- soundness

    soundness : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ φ  -- dokaz, da iz hipotez sledi formula
          → {w : W}  -- za vsak svet
          → proof (⟦ Δ ⟧ₑ w)  -- ce vse hipoteze veljajo v w
          → proof (⟦ φ ⟧ w)  -- potem formula velja v svetu w

    soundness {Δ = Δ} (weaken {Δ₁} {Δ₂} φ p) {w = w} δ =
      soundness p (++-intro Δ₁ Δ₂ (++-elim₁ Δ₁ (φ ∷ Δ₂) δ) (prove-Δ₂ Δ₁ Δ₂ φ δ))
        
    soundness {Δ = Δ} (contract {Δ₁} {Δ₂} φ {ψ} d) {w = w} δ = soundness d
              (++-intro Δ₁ (φ ∷ φ ∷ Δ₂) (++-elim₁ Δ₁ (φ ∷ Δ₂) δ)
                (∧ʰ-intro (∧ʰ-elim₁ (++-elim₂ Δ₁ (φ ∷ Δ₂) δ)) (++-elim₂ Δ₁ (φ ∷ Δ₂) δ))) 
    soundness (exchange {Δ₁} {Δ₂} ϕ ψ p) δ  =
      soundness p (proof-exchange Δ₁ Δ₂ ψ ϕ δ)

    soundness (hyp {φ ∷ Δ} φ {{ ∈-here }}) = ∧ʰ-elim₁
    soundness (hyp {ψ ∷ Δ} φ {{ (∈-there {{ p }}) }}) = λ x → soundness (hyp φ {{ p }}) (∧ʰ-elim₂ x)
    soundness ⊤-intro = λ _ → ⊤ʰ-intro
    soundness {φ = φ} (⊥-elim p) {w = w} = λ x → ⊥ʰ-elim {A = ⟦ φ ⟧ w} (soundness p x)
    soundness (∧-intro p p₁) = λ x → ∧ʰ-intro (soundness p x) (soundness p₁ x)
    soundness (∧-elim₁ p) = λ x → ∧ʰ-elim₁ (soundness p x)
    soundness (∧-elim₂ p) = λ x → ∧ʰ-elim₂ (soundness p x)
    soundness (∨-intro₁ p) = λ x → ∨ʰ-intro₁ (soundness p x)
    soundness (∨-intro₂ p) = λ x → ∨ʰ-intro₂ (soundness p x)
    soundness {Δ = Δ} {φ = φ} (∨-elim p p₁ p₂) {w = w} δ =
      ∨ʰ-elim {C = ⟦ φ ⟧ w} (soundness p δ)
         (⇒ʰ-intro (λ q → soundness p₁ (++-intro Δ _ δ (∧ʰ-intro q ⊤ʰ-intro))))
         (⇒ʰ-intro (λ q → soundness p₂ (++-intro Δ _ δ (∧ʰ-intro q ⊤ʰ-intro))))
    soundness {Δ = Δ} (⇒-intro {Δ} {φ} {ψ} p) {w = w} δ =  ⇒ʰ-intro (λ x → soundness p (++-intro Δ [ φ ] δ (∧ʰ-intro x ⊤ʰ-intro))) 
    soundness (⇒-elim p p₁) = λ x → ⇒ʰ-elim (soundness p₁ x) (soundness p x)
    soundness (□-intro As q p) {w = w} δ = ∀ʰ-intro (λ w' → 
      ⇒ʰ-intro λ w≤w' → soundness p (aux As w≤w' (soundness q δ)))
        where
          aux : {w' : W} → (As : List Formula) → (w≤w' : w ≤ₖ w') → (proof (⟦ box-∧-map As ⟧ w)) → (proof (⟦ box-map As ⟧ₑ w'))
          aux [] w≤w' p = p
          aux {w' = w'} (φ ∷ φs) w≤w' p =  ∧ʰ-intro (□-monotonicity {w = w} {φ = φ} (∧ʰ-elim₁ p) w≤w') (aux φs w≤w' ((∧ʰ-elim₂ p)))

    soundness {Δ = Δ} {φ = φ} (□-elim p) δ = at-world {φ = φ} (soundness p δ) ≤-refl
    soundness (◇-intro p) {w = w} δ = ∃ʰ-intro w (∧ʰ-intro ≤-refl (soundness p δ))
    soundness (◇-elim {φ = φ} {ψ = ψ} As f p q) {w = w} δ =
      ∃ʰ-elim
        (∃ʰ W (λ w'' → (w ≤ₕ w'') ∧ʰ ⟦ ψ ⟧ w''))
        (λ w' r →
           ∃ʰ-elim
            (∃ʰ W (λ w'' → (w ≤ₕ w'') ∧ʰ ⟦ ψ ⟧ w''))
            (λ w'' s →  ∃ʰ-intro w'' (∧ʰ-intro (prove-w≤w'' (∧ʰ-elim₁ r) (∧ʰ-elim₁ s)) (∧ʰ-elim₂ s)))
         {-    (soundness q {w = w'} (++-intro (box-map As) [ φ ] (((box-∧-map-to-box-map {As} {} {!   !} {! (soundness f δ) !}))) -}
            (soundness q {w = w'} (++-intro (box-map As) [ φ ] ((aux As (∧ʰ-elim₁ r) (soundness f δ)))
              (∧ʰ-intro (∧ʰ-elim₂ r) ⊤ʰ-intro))))
        (soundness p δ)
      where
        prove-w≤w'' : {w w' w'' : W} → proof (w ≤ₕ w') → proof (w' ≤ₕ w'') → proof (w ≤ₕ w'')
        prove-w≤w'' p q = ≤-transitive p q

        aux : {w' : W} → (As : List Formula) → (w≤w' : w ≤ₖ w') → (proof (⟦ box-∧-map As ⟧ w)) → (proof (⟦ box-map As ⟧ₑ w'))
        aux [] w≤w' p = p
        aux {w' = w'} (φ ∷ φs) w≤w' p =  ∧ʰ-intro (□-monotonicity {w = w} {φ = φ} (∧ʰ-elim₁ p) w≤w') (aux φs w≤w' ((∧ʰ-elim₂ p)))
        
