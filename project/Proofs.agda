{-# OPTIONS --overlapping-instances #-}

module Proofs (AtomicFormula : Set) where
  import NaturalDeduction
  open module ND = NaturalDeduction AtomicFormula

  □□-to-□ : (A : Formula) →  (□ □ A) ∷ []  ⊢ □ A -- a je to sploh prav, bi moralo biti obrnjeno? to je itak samo elimination
  □□-to-□ A = □-elim (hyp (□ □ A)) -- No instance of type (□ □ f) ∈ [ □ □ f ] was found in scope. Wat?

  □-dist : (A B : Formula) → [ □ (A ⇒ B) ] ⊢ (□ A) ⇒ (□ B) --\vdash
  □-dist A B = {!!} 
