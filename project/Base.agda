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
    ⟦ [] ⟧ₑ    w = ⊥ʰ 
    ⟦ φ ∷ Δ ⟧ₑ η = ⟦ φ ⟧ η ∧ʰ ⟦ Δ ⟧ₑ η

    ⟦⟧ₑ-++ : (Δ₁ Δ₂ : Hypotheses) {η : W}
       → ⟦ Δ₁ ++ Δ₂ ⟧ₑ η ≡ ⟦ Δ₁ ⟧ₑ η ∧ʰ ⟦ Δ₂ ⟧ₑ η

    ⟦⟧ₑ-++ [] Δ₂ {η} =
      begin
       ⟦ [] ++ Δ₂ ⟧ₑ η
       ≡⟨ cong {!⊥ʰ ∧ʰ_!}  refl ⟩ -- tu mislim da je problem, da se ⊥ʰ ∧ʰ_ ne pokrajsa v HProp, morava dokazati?
       ⟦ [] ⟧ₑ η ∧ʰ ⟦ Δ₂ ⟧ₑ η
      ∎
      
    ⟦⟧ₑ-++ (φ ∷ Δ₁) Δ₂ {η} = {!!}
