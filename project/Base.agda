{- najprej: vzem navadno logiko brez dodatnih dveh stvari iz vaj in sam spremen da ne gre v Bool ampak v KProp
ker bom to rabla

pol pa ⟦ ϕ ⟧ -> Bool/HProp za svoj ⟦ ϕ ⟧_(W, U, L)  spremen, da bo slo v W -> HProp
 -}

module Base (AtomicFormula : Set) where 
  open import KripkeFrame AtomicFormula
  open import HProp
  open import NaturalDeduction AtomicFormula
  {- 
  open module ND = NaturalDeduction AtomicFormula
  -}

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
    ⟦ □ ϕ ⟧ w = ∀ʰ W (λ w' → (w ≤ₕ w') ⇒ʰ ⟦ ϕ ⟧ w')
    -- ⟦ □ ϕ ⟧ w =  ∀ʰ W {! ? ≤ₖ ?!}


