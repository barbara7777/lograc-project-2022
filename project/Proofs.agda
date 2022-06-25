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
  □-to-□□ A =  □-intro {Δ = [ □ A ]} {φ = □ A} {n = 1} [ A ]
    aux (hyp (□ A))
    where
      aux : (B : Formula) (p : B ∈ [ A ]) → [ □ A ] ⊢ □ B
      aux B ∈-here = hyp (□ B)

  □-◇-rel : (A B : Formula) → [ □ ( A ⇒ ◇ B) ] ⊢ ◇ A ⇒ ◇ B
  □-◇-rel A B = {!◇-elim (aux₁ A B)!}
    where
      aux₁ :  (C D : Formula) → [ □ ( C ⇒ ◇ D) ] ++ [ C ] ⊢ ◇ D
      aux₁ C D = ⇒-elim (□-elim (hyp ( □ ( C ⇒ ◇ D)))) (hyp C)

  ◇-intro-proof : (A : Formula) → [ A ] ⊢ ◇ A
  ◇-intro-proof A = ◇-intro (hyp A)
