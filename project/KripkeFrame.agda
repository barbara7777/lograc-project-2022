module KripkeFrame (AtomicFormula : Set) where

open import NaturalDeduction AtomicFormula



record KripkeFrame : Set₁ where 
    field
        W : Set₀
        _≤_ : W → W → Set₀  
        {- ≤-is-prop : (w w' : W) → is-prop (w ≤ w') -}
        Val : W → AtomicFormula → Set

        {- Dokazi: 
        ≤-refl : ∀ w. w ≤ w' 
        ≤-transitive : ∀ w w' w'' .....
        -}


        