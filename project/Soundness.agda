module Soundness (AtomicFormula : Set) where 
  open import KripkeFrame AtomicFormula
  open import HProp
  open import NaturalDeduction AtomicFormula
  {- 
  open module ND = NaturalDeduction AtomicFormula
  -}

  import Relation.Binary.PropositionalEquality as Eq
  open Eq renaming ([_] to [|_|])
  open Eq.≡-Reasoning
  {- open import Data.List renaming (List to L.List; [] to List.[]; _∷_ to _List.∷_; [_] to List.[_]; _++_ to _List.++_) -} 

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

    -- helpers
    
    ⟦⟧ₑ-++ : (Δ₁ Δ₂ : Hypotheses) {w : W}
       → proof (⟦ Δ₁ ++ Δ₂ ⟧ₑ w) → proof (⟦ Δ₁ ⟧ₑ w ∧ʰ ⟦ Δ₂ ⟧ₑ w)
    ⟦⟧ₑ-++ [] Δ₂ = λ p → ∧ʰ-intro ⊤ʰ-intro p
    ⟦⟧ₑ-++ (x ∷ Δ₁) Δ₂ = {!λ p → ∧ʰ-intro (∧ʰ-elim₁ p) ( ⟦⟧ₑ-++ Δ₁ Δ₂ (∧ʰ-elim₂ p))!}


    and-concat : {Δ₁ Δ₂ : Hypotheses}
          → {w : W}
          → proof (⟦ Δ₁ ⟧ₑ w ∧ʰ ⟦ Δ₂ ⟧ₑ w) → proof (⟦ Δ₁ ++ Δ₂ ⟧ₑ w)
    and-concat {[]} p = {!   !}   -- tole je bil split po Δ₁
    and-concat {ϕ ∷ Δ₁} p = {!   !}

    exchange-hyp : {Δ : Hypotheses} {ϕ : Formula} {w : W} → proof (⟦ Δ ++ [ ϕ ] ⟧ₑ w) → proof (⟦ [ ϕ ] ++  Δ ⟧ₑ w)
    exchange-hyp p = {!!}

    test : {A B : HProp} → proof A → (proof A → proof B) → proof B
    test p f = {!   !}

    ∀ʰ-elim : {Δ : Hypotheses} {w : W} {ϕ : Formula} →
          proof (∀ʰ W (λ w' → (w ≤ₕ w') ⇒ʰ ⟦ ϕ ⟧ w')) → proof (⟦ ϕ ⟧ w)
    ∀ʰ-elim {Δ} {w} {ϕ} p = {!∀ʰ W (λ w' → (w ≤ₕ w') ⇒ʰ ⟦ ϕ ⟧ w')!}
    
    -- soundness

    soundness : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ φ  -- dokaz, da iz hipotez sledi formula
          → {w : W}  -- za vsak svet
          → proof (⟦ Δ ⟧ₑ w)  -- ce vse hipoteze veljajo v w
          → proof (⟦ φ ⟧ w)  -- potem formula velja v svetu w

    soundness (weaken φ p) x = {!soundness p!}
    
    soundness (contract {Δ₁} {Δ₂} φ {ψ} d) = {!soundness d!}
      where
        aux :{Δ₁ Δ₂ : Hypotheses} {w : W} {ϕ : Formula} → proof (⟦ Δ₁ ++ φ ∷ φ ∷ Δ₂ ⟧ₑ w) → proof (⟦ Δ₁ ⟧ₑ w ∧ʰ ⟦ φ ∷ Δ₂ ⟧ₑ w)
        aux {Δ₁} {Δ₂} p = {! ⟦⟧ₑ-++ !}
    soundness (exchange φ₁ φ₂ p) = {!!}

    soundness (hyp {φ ∷ Δ} φ {{ ∈-here }}) = ∧ʰ-elim₁
    soundness (hyp {ψ ∷ Δ} ϕ {{ (∈-there {{ p }}) }}) = λ x → soundness (hyp ϕ {{ p }}) (∧ʰ-elim₂ x)

    soundness ⊤-intro = λ _ → ⊤ʰ-intro

    soundness (⊥-elim p) = λ x → ⊥ʰ-elim (soundness p x)
    soundness (∧-intro p p₁) = λ x → ∧ʰ-intro (soundness p x) (soundness p₁ x)
    soundness (∧-elim₁ p) = λ x → ∧ʰ-elim₁ (soundness p x)
    soundness (∧-elim₂ p) = λ x → ∧ʰ-elim₂ (soundness p x)
    soundness (∨-intro₁ p) = λ x → ∨ʰ-intro₁ (soundness p x)
    soundness (∨-intro₂ p) = λ x → ∨ʰ-intro₂ (soundness p x)

    soundness (∨-elim p p₁ p₂) = λ x → {!   !} --  (soundness p x) {!   !} (soundness p₁ ?) -- ∨ʰ-elim (soundness p x) (soundness p₁ x) (soundness p₂ x ) 
    soundness (⇒-intro {Δ} {φ} p) {w} δ = ⇒ʰ-intro λ q → soundness p (aux q)
      where
        aux : proof (⟦ φ ⟧ w) → proof (⟦ Δ ++ [ φ ] ⟧ₑ w)
        aux q = and-concat  {Δ} {[ φ ]} {w} (∧ʰ-intro δ (∧ʰ-intro q ⊤ʰ-intro)) 
    soundness (⇒-elim p p₁) = λ x → ⇒ʰ-elim (soundness p₁ x) (soundness p x)
    soundness (□-intro As x p) = {!!}
    soundness (□-elim p) δ = ∀ʰ-elim (soundness p δ)
    soundness (⋄-intro p) = aux p
      where
        aux : {Δ : Hypotheses} → {w : W} → {ϕ : Formula} → Δ ⊢ ϕ → proof (⟦ Δ ⟧ₑ w)
                   → proof (∃ʰ W (λ w' → (w ≤ₕ w') ∧ʰ ⟦ ϕ ⟧ w'))
        aux p x = {!!}
    soundness (⋄-elim As x p p₁) = {!!}

 
