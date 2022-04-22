module Proofs (AtomicFormula : Set) where
  open import NaturalDeduction AtomicFormula

  □□-to-□ : (f : Formula) →  [ □ □ f ]  ⊢ □ f -- a je to sploh prav, bi moralo biti obrnjeno? to je itak samo elimination
  □□-to-□ f = {!□-elim (hyp (□ □ f))!} -- No instance of type (□ □ f) ∈ [ □ □ f ] was found in scope. Wat?

  □-dist : (a b : Formula) → [ □ (a ⇒ b) ] ⊢ (□ a) ⇒ (□ b) --\vdash
  □-dist a b = {!!} 
