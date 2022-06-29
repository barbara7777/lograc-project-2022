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

    concat-proofs-⟦⟧ₑ : (Δ : Hypotheses) {w : W} → (∀ φ → φ ∈ Δ → proof (⟦ φ ⟧ w)) → proof (⟦ Δ ⟧ₑ w)
    concat-proofs-⟦⟧ₑ [] f = ⊤ʰ-intro
    concat-proofs-⟦⟧ₑ (y ∷ Δ) {w = w} f = ∧ʰ-intro (f y ∈-here)
                                           (concat-proofs-⟦⟧ₑ Δ {w} λ x p → f x (∈-there {{p}} ) )

    ⟦⟧ₑ-++ : (Δ₁ Δ₂ : Hypotheses) {w : W} → proof (⟦ Δ₁ ⟧ₑ w) → proof (⟦ Δ₂ ⟧ₑ w) → proof (⟦ Δ₁ ++ Δ₂ ⟧ₑ w)
    ⟦⟧ₑ-++ [] Δ₂ δ₁ δ₂ = δ₂
    ⟦⟧ₑ-++ (_ ∷ Δ₁) Δ₂ δ₁ δ₂ = ∧ʰ-intro (∧ʰ-elim₁ δ₁) (⟦⟧ₑ-++ Δ₁ Δ₂ (∧ʰ-elim₂ δ₁) δ₂)
 

    test : (Δ₁ Δ₂ : Hypotheses) {w : W} → proof (⟦ Δ₁ ++ Δ₂ ⟧ₑ w) → proof (⟦ Δ₂ ⟧ₑ w) 
    test = {!   !}

    at-world : {w w' : W} {φ : Formula} →
          proof (⟦ □ φ ⟧ w) → w ≤ₖ w' → proof (⟦ φ ⟧ w')
    at-world {w = w} {w' = w'} {φ = φ} p w≤w' = ⇒ʰ-elim w≤w' (∀ʰ-elim p w')

    -- soundness

    soundness : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ φ  -- dokaz, da iz hipotez sledi formula
          → {w : W}  -- za vsak svet
          → proof (⟦ Δ ⟧ₑ w)  -- ce vse hipoteze veljajo v w
          → proof (⟦ φ ⟧ w)  -- potem formula velja v svetu w

    soundness (weaken φ p) x = {!soundness p!}
    soundness (contract {Δ₁} {Δ₂} φ {ψ} d) = {!soundness d!}
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
    soundness (□-intro As f p) δ =
      ∀ʰ-intro (λ w' → ⇒ʰ-intro
                         (λ w≤w' → soundness p (concat-proofs-⟦⟧ₑ (box-map As) {w = w'}
                           λ φ elem → at-world {φ = φ} (extract-boxed φ elem) w≤w' )))
      where
        extract-boxed : {w : W} (φ : Formula) → φ ∈ box-map As → proof (⟦ □ φ ⟧ w)
        extract-boxed {w = w} φ p = ∀ʰ-intro {!   !}

    soundness {Δ = Δ} {φ = φ} (□-elim p) δ = at-world {φ = φ} (soundness p δ) ≤-refl
    soundness (◇-intro p) δ = {!   !}
    soundness (◇-elim {ψ = ψ} As f p q) {w = w} δ = {!!}

{-

  δ         soundness p δ
  w -------->    w'

  Δ              φ
                                        soundness q
                 box-map As ++ [ φ ] -----------------> w''
                                                        ψ

-}