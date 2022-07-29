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
    ++-elim₁ Γ Δ p = {!!}

    ++-elim₂ : (Γ Δ : Hypotheses) → {w : W} → proof (⟦ Γ ++ Δ ⟧ₑ w) → proof(⟦ Δ ⟧ₑ w)
    ++-elim₂ Γ Δ p = {!!}

    ++-intro : (Γ Δ : Hypotheses) → {w : W}  → proof(⟦ Γ ⟧ₑ w) → proof(⟦ Δ ⟧ₑ w) → proof (⟦ Γ ++ Δ ⟧ₑ w)
    ++-intro Γ Δ p q = {!!}

    elim-last : {Δ : Hypotheses} {φ : Formula} {w : W} → proof (⟦ Δ ++ φ ∷ [] ⟧ₑ w) → proof (⟦ φ ⟧ w)
    elim-last {[]} p = ∧ʰ-elim₁ p 
    elim-last {_ ∷ Δ} p = elim-last {Δ} (∧ʰ-elim₂ p)

    elim-but-last : {Δ : Hypotheses} {φ : Formula} {w : W} → proof (⟦ Δ ++ φ ∷ [] ⟧ₑ w) → proof (⟦ Δ ⟧ₑ w)
    elim-but-last {[]} p = ⊤ʰ-intro
    elim-but-last {ψ ∷ Δ} p = ∧ʰ-intro (∧ʰ-elim₁ p) (elim-but-last {Δ} (∧ʰ-elim₂ p))

    unravel-list : {Δ : Hypotheses} {φ : Formula} {w : W} → proof (⟦ Δ ++ φ ∷ [] ⟧ₑ w) → proof (⟦ Δ ⟧ₑ w ∧ʰ ⟦ φ ⟧ w)
    unravel-list {Δ} {φ} {w} p = ∧ʰ-intro (elim-but-last {Δ} p) (elim-last {Δ} p)
         
    swap-formulas : {Δ : Hypotheses} {φ : Formula} {w : W} → proof(⟦ Δ ++ φ ∷ [] ⟧ₑ w) → proof(⟦ φ ∷ Δ ⟧ₑ w)
    swap-formulas {Δ} {φ} {w} p = ∧ʰ-intro
      (∧ʰ-elim₂ {⟦ Δ ⟧ₑ w} {⟦ φ ⟧ w} (unravel-list {Δ} p))
      (∧ʰ-elim₁ {⟦ Δ ⟧ₑ w} {⟦ φ ⟧ w} (unravel-list {Δ} p)) 
        
    concat-proofs-⟦⟧ₑ : (Δ : Hypotheses) {w : W} → (∀ φ → φ ∈ Δ → proof (⟦ φ ⟧ w)) → proof (⟦ Δ ⟧ₑ w)
    concat-proofs-⟦⟧ₑ [] f = ⊤ʰ-intro
    concat-proofs-⟦⟧ₑ (y ∷ Δ) {w = w} f = ∧ʰ-intro (f y ∈-here)
                                           (concat-proofs-⟦⟧ₑ Δ {w} λ x p → f x (∈-there {{p}} ) )

    ⟦⟧ₑ-++ : (Δ₁ Δ₂ : Hypotheses) {w : W} → proof (⟦ Δ₁ ⟧ₑ w) → proof (⟦ Δ₂ ⟧ₑ w) → proof (⟦ Δ₁ ++ Δ₂ ⟧ₑ w)
    ⟦⟧ₑ-++ [] Δ₂ δ₁ δ₂ = δ₂
    ⟦⟧ₑ-++ (_ ∷ Δ₁) Δ₂ δ₁ δ₂ = ∧ʰ-intro (∧ʰ-elim₁ δ₁) (⟦⟧ₑ-++ Δ₁ Δ₂ (∧ʰ-elim₂ δ₁) δ₂)

    -- remove-specific-⟦⟧ₑ : {Δ₁ Δ₂ : Hypotheses} {φ : Formula} {w : W}
    --                       → proof (⟦ Δ₁ ++ φ ∷ Δ₂ ⟧ₑ w)
    --                       → proof (⟦ Δ₁ ++ Δ₂ ⟧ₑ w)
    -- remove-specific-⟦⟧ₑ {Δ₁} {Δ₂} {φ} {w} p = ⟦⟧ₑ-++ Δ₁ Δ₂ (prove-Δ₁ {Δ₁} {Δ₂} {φ} p) (prove-Δ₂ {Δ₁} {Δ₂} {φ} p)
    --   where
    --     prove-Δ₁ : {Δ₁ Δ₂ : Hypotheses} {φ : Formula} → proof (⟦ Δ₁ ++ φ ∷ Δ₂ ⟧ₑ w) → proof(⟦ Δ₁ ⟧ₑ w)
    --     prove-Δ₁ {Δ₁} {[]} {φ} p = ∧ʰ-elim₂ (swap-formulas {Δ₁} p) 
    --     prove-Δ₁ {Δ₁} {x ∷ Δ₂} {φ} p = prove-Δ₁ {Δ₁} {Δ₂} {φ} (remove-specific-⟦⟧ₑ p)

    --     prove-Δ₂ : {Δ₁ Δ₂ : Hypotheses} {φ : Formula} → proof (⟦ Δ₁ ++ φ ∷ Δ₂ ⟧ₑ w) → proof(⟦ Δ₂ ⟧ₑ w)
    --     prove-Δ₂ {[]} {Δ₂} {φ} p = ∧ʰ-elim₂ p
    --     prove-Δ₂ {x ∷ Δ₁} {Δ₂} {φ} p = prove-Δ₂ {Δ₁} {Δ₂} {φ} (∧ʰ-elim₂ p)

    --     prove-φ : {Δ₁ Δ₂ : Hypotheses} {φ : Formula} → proof (⟦ Δ₁ ++ φ ∷ Δ₂ ⟧ₑ w) → proof(⟦ φ ⟧ w)
    --     prove-φ {[]} {Δ₂} {φ} p = ∧ʰ-elim₁ p
    --     prove-φ {x ∷ Δ₁} {Δ₂} {φ} p = prove-φ {Δ₁} {Δ₂} {φ} (∧ʰ-elim₂ p)

    remove-specific-⟦⟧ₑ : {Δ₁ Δ₂ : Hypotheses} {φ : Formula} {w : W}
                          → proof (⟦ Δ₁ ++ φ ∷ Δ₂ ⟧ₑ w)
                          → proof (⟦ Δ₁ ++ Δ₂ ⟧ₑ w)
    remove-specific-⟦⟧ₑ {[]} {Δ₂} {φ} {w} p = {!!}
    remove-specific-⟦⟧ₑ {ψ ∷ Δ₁} {Δ₂} {φ} {w} p = {!!}

    at-world : {w w' : W} {φ : Formula} →
          proof (⟦ □ φ ⟧ w) → w ≤ₖ w' → proof (⟦ φ ⟧ w')
    at-world {w = w} {w' = w'} {φ = φ} p w≤w' = ⇒ʰ-elim w≤w' (∀ʰ-elim p w')

    □-monotonicity : {w w' : W} {φ : Formula} → proof (⟦ □ φ ⟧ w) → proof (w ≤ₕ w') → proof (⟦ □ φ ⟧ w')
    □-monotonicity p q = ∀ʰ-intro (λ w'' → ⇒ʰ-intro (λ r → ⇒ʰ-elim (≤-transitive q r) (∀ʰ-elim p w'')))

    -- soundness

    soundness : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ φ  -- dokaz, da iz hipotez sledi formula
          → {w : W}  -- za vsak svet
          → proof (⟦ Δ ⟧ₑ w)  -- ce vse hipoteze veljajo v w
          → proof (⟦ φ ⟧ w)  -- potem formula velja v svetu w

    soundness {Δ = Δ} {φ = φ₁} (weaken {Δ₁} {Δ₂} φ p) {w = w} δ = soundness p {w = w}
      (remove-specific-⟦⟧ₑ {Δ₁} {Δ₂} {φ} δ)
    soundness {Δ = Δ} (contract {Δ₁} {Δ₂} φ {ψ} d) {w = w} δ = soundness d
              (++-intro Δ₁ (φ ∷ φ ∷ Δ₂) (++-elim₁ Δ₁ (φ ∷ Δ₂) δ)
                (∧ʰ-intro (∧ʰ-elim₁ (++-elim₂ Δ₁ (φ ∷ Δ₂) δ)) (++-elim₂ Δ₁ (φ ∷ Δ₂) δ))) 
    soundness (exchange φ₁ φ₂ p) = {!!}

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
         (⇒ʰ-intro (λ q → soundness p₁ (⟦⟧ₑ-++ Δ _ δ (∧ʰ-intro q ⊤ʰ-intro))))
         (⇒ʰ-intro (λ q → soundness p₂ (⟦⟧ₑ-++ Δ _ δ (∧ʰ-intro q ⊤ʰ-intro))))
    soundness {Δ = Δ} (⇒-intro {Δ} {φ} {ψ} p) {w = w} δ =  ⇒ʰ-intro (λ x → soundness p (⟦⟧ₑ-++ Δ [ φ ] δ (∧ʰ-intro x ⊤ʰ-intro))) 
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
            (λ w'' s →  ∃ʰ-intro w'' (∧ʰ-intro {!!} {!!}) )
            (soundness q {w = w'} (++-intro (box-map As) [ φ ] {!!} {!!})) )
        (soundness p δ)
      where
        w' : W
        w' = {!!}

        prove-□As-phi : proof (⟦ box-map As ++ φ ∷ [] ⟧ₑ w)
        prove-□As-phi = ⟦⟧ₑ-++ (box-map As) [ φ ] {w} {!soundness f δ!}
          (∧ʰ-intro (∃ʰ-elim (⟦ φ ⟧ w) (λ w' e → {!!}) (soundness p δ)) ⊤ʰ-intro)
        

 
