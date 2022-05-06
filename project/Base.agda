module Base (AtomicFormula : Set) where 
  open import KripkeFrame AtomicFormula
  open import HProp
  open import NaturalDeduction AtomicFormula
  {- 
  open module ND = NaturalDeduction AtomicFormula
  -}

  import Relation.Binary.PropositionalEquality as Eq
  open Eq renaming ([_] to [|_|])
  open Eq.≡-Reasoning

  module _ (Fr : KripkeFrame) where
    open KripkeFrame Fr
    ℙ = W → HProp

    ⟦_⟧ : Formula → ℙ
    ⟦ ` P ⟧    w = Val w P
    ⟦ ⊤ ⟧     w = ⊤ʰ
    ⟦ ⊥ ⟧     w = ⊥ʰ
    ⟦ φ ∧ ψ ⟧ w = ⟦ φ ⟧ w ∧ʰ ⟦ ψ ⟧ w
    ⟦ φ ∨ ψ ⟧ w = ⟦ φ ⟧ w ∨ʰ ⟦ ψ ⟧ w
    ⟦ φ ⇒ ψ ⟧ w = ⟦ φ ⟧ w ⇒ʰ ⟦ ψ ⟧ w
    ⟦ □ ϕ ⟧ w = ∀ʰ W (λ w' → (w ≤ₕ w') ⇒ʰ ⟦ ϕ ⟧ w')
    ⟦ ⋄ ϕ ⟧ w = ∃ʰ W (λ w' → (w ≤ₕ w') ∧ʰ ⟦ ϕ ⟧ w')

    ⟦_⟧ₑ : Hypotheses  → ℙ             -- unicode \[[ \]] \_e
    ⟦ [] ⟧ₑ    w = ⊤ʰ 
    ⟦ φ ∷ Δ ⟧ₑ w = ⟦ φ ⟧ w ∧ʰ ⟦ Δ ⟧ₑ w

    -- soundness

    soundness : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ φ
          → {w : W}
          → proof (⟦ Δ ⟧ₑ w)
          → proof (⟦ φ ⟧ w)

    soundness (weaken φ p) = {!soundness p!}
    soundness (contract φ p) = {!!}
    soundness (exchange φ₁ φ₂ p) = {!!}
    soundness (hyp _) = {!!}
    soundness ⊤-intro = λ _ → ⊤ʰ-intro

    soundness (⊥-elim p) = {!!}
    soundness (∧-intro p p₁) = {!!}
    soundness (∧-elim₁ p) = {!!}
    soundness (∧-elim₂ p) = {!!}
    soundness (∨-intro₁ p) = {!!}
    soundness (∨-intro₂ p) = {!!}
    soundness (∨-elim p p₁ p₂) = {!!}
    soundness (⇒-intro p) = {!!}
    soundness (⇒-elim p p₁) = {!!}
    soundness (□-intro As x p) = {!!}
    soundness (□-elim p) = {!!}
    soundness (⋄-intro p) = {!!}
    soundness (⋄-elim As x p p₁) = {!!}
