{-# OPTIONS --overlapping-instances #-}

module Proofs (AtomicFormula : Set) where
  import NaturalDeduction
  open module ND = NaturalDeduction AtomicFormula
  open import Data.Vec   using (Vec; []; _∷_)
  open import Data.Fin   using (Fin; zero; suc)


  □-dist : (A B : Formula) → [ □ (A ⇒ B) ] ⊢ □ A ⇒ □ B --\vdash
  □-dist A B = {!⇒-elim (□-elim (hyp (□ (A ⇒ B)))) (hyp (□ A)))!}

  □-elim-proof : (A : Formula) →  [ □ A ]  ⊢ A 
  □-elim-proof A = □-elim (hyp (□ A))

  □-to-□□ : (A : Formula) →  [ □ A ]  ⊢ □ □ A 
  □-to-□□ A = □-intro (A ∷ []) aux  (hyp (□ A))
    where
      aux : (i : Fin 1) → [ □ A ] ⊢ □ lookup (A ∷ []) i
      aux zero = hyp (□ A)

  □-⋄-rel : (A B : Formula) → [ □ ( A ⇒ ⋄ B) ] ⊢ ⋄ A ⇒ ⋄ B
  -- □-⋄-rel A B = ⇒-intro (weaken (⋄ A) (⇒-elim (□-elim (hyp ( □ ( A ⇒ ⋄ B)))) (hyp A)))
  □-⋄-rel A B = {!⇒-elim (hyp ( □ ( A ⇒ ⋄ B))) (hyp A)!}
    where
      aux₁ :  (C D : Formula) → [ □ ( C ⇒ ⋄ D) ] ++ [ C ] ⊢ ⋄ D
      aux₁ C D = ⇒-elim (□-elim (hyp ( □ ( C ⇒ ⋄ D)))) (hyp C)

  -- (hyp ( □ ( A ⇒ (⋄ B))) -- [ □ ( A ⇒ (⋄ B)) ] ⊢ □ ( A ⇒ (⋄ B))
  -- □-elim [ □ ( A ⇒ (⋄ B)) ] ⊢ A ⇒ (⋄ B)
  -- ⇒-elim
  -- ⇒-intro

  ⋄-intro-proof : (A : Formula) → [ A ] ⊢ ⋄ A
  ⋄-intro-proof A = ⋄-intro (hyp A)
