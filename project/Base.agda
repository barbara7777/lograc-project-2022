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
    ℙ = KripkeFrame → HProp
    Env = AtomicFormula → ℙ

    {- [[_]] : Formula -> Env -> HProp -}

    ⟦_⟧ : Formula → ℙ
    ⟦ ` P ⟧   η = η P
    ⟦ ⊤ ⟧     η = ⊤ʰ
    ⟦ ⊥ ⟧     η = ⊥ʰ
    ⟦ φ ∧ ψ ⟧ η = ⟦ φ ⟧ η ∧ʰ ⟦ ψ ⟧ η
    ⟦ φ ∨ ψ ⟧ η = ⟦ φ ⟧ η ∨ʰ ⟦ ψ ⟧ η
    ⟦ φ ⇒ ψ ⟧ η = ⟦ φ ⟧ η ⇒ʰ ⟦ ψ ⟧ η
    -- ⟦ □ ϕ ⟧ η = ⟦ ϕ ⟧ η


