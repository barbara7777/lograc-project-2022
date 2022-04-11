{-
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

-}

-- https://en.wikipedia.org/wiki/Kripke_semantics
module KripkeFrame (AtomicFormula : Set) where 

  open import HProp
  open import NaturalDeduction AtomicFormula

  record KripkeFrame : Set₁ where
    field
      W : Set₀
      _≤_ : W → W → Set₀
      ≤-is-prop : ( w w₁ : W ) → is-proposition( w ≤ w₁ ) -- tu ne vem zakaj je to uporabno
      Val : W → AtomicFormula → Set
      ≤-refl : ∀ {w} → w ≤ w -- tuki je na tabli napisal w ≤ w', ampak a ni refl tako kot sem jaz napisal?
      ≤-transitive : ∀ {w w₁ w₂} → w ≤ w₁ → w₁ ≤ w₂ → w ≤ w₂
