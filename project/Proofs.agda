{-# OPTIONS --overlapping-instances #-}

module Proofs (AtomicFormula : Set) where
  import NaturalDeduction
  open module ND = NaturalDeduction AtomicFormula
  open import Data.Vec   using (Vec; []; _∷_)
  open import Data.Fin   using (Fin; zero; suc)

  □-dist : (A B : Formula) → [ □ (A ⇒ B) ] ⊢ □ A ⇒ □ B --\vdash
  □-dist A B = ⇒-intro (prove-□B A B)
    where
      prove-□B : (A B : Formula) → □ (A ⇒ B) ∷ □ A ∷ []  ⊢ □ B
      prove-□B A B = □-intro {Δ = □ (A ⇒ B) ∷ □ A ∷ []} {φ = B} {n = 1} ((A ⇒ B) ∷ A ∷ [])
        (∧-intro (hyp (□ (A ⇒ B))) (∧-intro (hyp (□ A)) ⊤-intro))
        (⇒-elim (□-elim (hyp {Δ = □ (A ⇒ B) ∷ □ A ∷ [] }(□ (A ⇒ B))))
          (□-elim (hyp {Δ = □ (A ⇒ B) ∷ □ A ∷ []}(□ A))))

  □-elim-proof : (A : Formula) →  [ □ A ]  ⊢ A 
  □-elim-proof A = □-elim (hyp (□ A))

  □-to-□□ : (A : Formula) →  [ □ A ]  ⊢ □ □ A 
  □-to-□□ A =  □-intro {Δ = [ □ A ]} {φ = □ A} {n = 1} [ A ] (∧-intro (hyp {[ □ A ]} (□ A)) ⊤-intro) (hyp (□ A))

  □-◇-rel : (A B : Formula) → [ □ ( A ⇒ ◇ B) ] ⊢ ◇ A ⇒ ◇ B
  □-◇-rel A B = ⇒-intro (prove-◇B A B)
      where
        prove-◇B : (A B : Formula) → □ (A ⇒ ◇ B) ∷ ◇ A ∷ [] ⊢ ◇ B
        prove-◇B A B = ◇-elim {ψ = B} {n = 1} [ (A ⇒ ◇ B) ]
          (∧-intro (hyp (□ (A ⇒ ◇ B))) ⊤-intro) (hyp {Δ =  □ (A ⇒ ◇ B) ∷ ◇ A ∷ []} (◇ A))
          (⇒-elim (□-elim (hyp (□ (A ⇒ ◇ B)))) (hyp A))

  ◇-intro-proof : (A : Formula) → [ A ] ⊢ ◇ A
  ◇-intro-proof A = ◇-intro (hyp A)
