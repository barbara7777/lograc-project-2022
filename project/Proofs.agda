{-# OPTIONS --overlapping-instances #-}

module Proofs (AtomicFormula : Set) where
  import NaturalDeduction
  open module ND = NaturalDeduction AtomicFormula
  open import Data.Vec   using (Vec; []; _∷_)
  open import Data.Fin   using (Fin; zero; suc)


  □-dist : (A B : Formula) → [ □ (A ⇒ B) ] ⊢ (□ A) ⇒ (□ B) --\vdash
  □-dist A B = {!!}

  □-elim-proof : (A : Formula) →  [ □ A ]  ⊢ A 
  □-elim-proof A = □-elim (hyp (□ A))

  □-to-□□ : (A : Formula) →  [ □ A ]  ⊢ □ □ A 
  □-to-□□ A = □-intro (A ∷ []) aux  (hyp (□ A))
    where
      aux : (i : Fin 1) → [ □ A ] ⊢ □ lookup (A ∷ []) i
      aux zero = hyp (□ A)

  □-⋄-rel : (A B : Formula) → [ □ ( A ⇒ (⋄ B)) ] ⊢ (⋄ A) ⇒ (⋄ B)
  □-⋄-rel A B = {!!}

  ⋄-intro-proof : (A : Formula) → [ A ] ⊢ (⋄ A)
  ⋄-intro-proof A = ⋄-intro (hyp A)
