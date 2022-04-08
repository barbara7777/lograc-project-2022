{- najprej: vzem navadno logiko brez dodatnih dveh stvari iz vaj in sam spremen da ne gre v Bool ampak v KProp
ker bom to rabla

pol pa [| phi |] -> Bool/HProp za svoj [[ phi ]]_(W, U; L)  spremen, da bo slo v W -> HProp
 -}

module Base (AtomicFormula : Set) where 


open import HProp
open import NaturalDeduction AtomicFormula
{- 
open module ND = NaturalDeduction AtomicFormula
 -}

ℙ = HProp
Env = AtomicFormula → ℙ

{- [[_]] : Formula -> Env -> HProp -}

⟦_⟧ : Formula → Env → ℙ
⟦ ` P ⟧   η = η P
⟦ ⊤ ⟧     η = ⊤ʰ
⟦ ⊥ ⟧     η = ⊥ʰ
⟦ φ ∧ ψ ⟧ η = ⟦ φ ⟧ η ∧ʰ ⟦ ψ ⟧ η
⟦ φ ∨ ψ ⟧ η = ⟦ φ ⟧ η ∨ʰ ⟦ ψ ⟧ η
⟦ φ ⇒ ψ ⟧ η = ⟦ φ ⟧ η ⇒ʰ ⟦ ψ ⟧ η

{- todo: ⟦ □  ⟧   -}
