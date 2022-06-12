{-# OPTIONS --overlapping-instances #-}

{-
   Notice that we parametrise the deeply embedded propositional logic
   and its natural deduction proof system over a type of atomic formulaes.
-}

module NaturalDeduction (AtomicFormula : Set) where

open import Data.Fin   using (Fin; zero; suc)
open import Data.Nat   using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
open import Data.List  using (List; []; _∷_; [_]; _++_) public
open import Data.Vec   using (Vec; []; _∷_)

data Formula : Set where
  `_  : AtomicFormula → Formula           -- atomic formula
  ⊤   : Formula                           -- truth (unicode \top)
  ⊥   : Formula                           -- falsehood (unicode \bot)
  _∧_ : Formula → Formula → Formula       -- conjunction (unicode \wedge)
  _∨_ : Formula → Formula → Formula       -- disjunction (unicode \vee)
  _⇒_ : Formula → Formula → Formula       -- implication (unicode \=>)
  □_ : Formula → Formula                   -- necessity (unicode \square)
  ◇_ : Formula → Formula                  -- possibility (unicode \diamond)

infixr 6 _∧_
infixr 5 _∨_
infixr 4 _⇒_
infixr 7 □_
infixr 7 ◇_


Hypotheses = List (Formula)

{-
   We use constructor instances when defining the formula-in-hypotheses
   membership relation `∈`. This way we will be able to use instance
   search to fill in these arguments when constructing derivations.

   Note: Agda will report an error if instance search is used to try to
   provide a witness of `{{x ∈ xs}}` when `xs` contains multiple copies
   of `x`, because in that case there isn't a unique proof of `x ∈ xs`.
   In those cases you can provide an explicit proof of the form `{{p}}`.

   You shouldn't be running into such errors in this week's exercises
   as their most concise solutions will involve repeated hypotheses.
-}

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  instance
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)

lookup : {n : ℕ} → {A : Set} → Vec A n → Fin n → A
lookup (a ∷ as) zero = a
lookup (a ∷ as) (suc i) = lookup as i

box-map : Hypotheses → Hypotheses
box-map [] = []
box-map (x ∷ xs) = (□ x) ∷ box-map xs

{-
   Below is a natural deduction style proof calculus for **intuitionistic**
   propositional logic, formalised as an inductive relation.
-}

infixl 2 _⊢_
data _⊢_ : (Δ : Hypotheses) → (φ : Formula) → Set where    -- unicode \vdash

  -- structural rules

  weaken   : {Δ₁ Δ₂ : Hypotheses}
           → (φ : Formula)
           → {ψ : Formula}
           → Δ₁ ++ Δ₂ ⊢ ψ
           -----------------------
           → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

  contract : {Δ₁ Δ₂ : Hypotheses}
           → (φ : Formula)
           → {ψ : Formula}
           → Δ₁ ++ [ φ ] ++ [ φ ] ++ Δ₂ ⊢ ψ
           --------------------------------
           → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

  exchange : {Δ₁ Δ₂ : Hypotheses}
           → (φ₁ φ₂ : Formula)
           → {ψ : Formula}
           → Δ₁ ++ [ φ₁ ] ++ [ φ₂ ] ++ Δ₂ ⊢ ψ
           -----------------------------------------
           → Δ₁ ++ [ φ₂ ] ++ [ φ₁ ] ++ Δ₂ ⊢ ψ

  -- hypotheses

  hyp      : {Δ : Hypotheses}
           → (φ : Formula)
           → {{φ ∈ Δ}}
           -----------------
           → Δ ⊢ φ

  -- truth

  ⊤-intro  : {Δ : Hypotheses}
           ------------------
           → Δ ⊢ ⊤

  -- falsehood

  ⊥-elim   : {Δ : Hypotheses}
           → {φ : Formula}
           → Δ ⊢ ⊥
           -------------------
           → Δ ⊢ φ

  -- conjunction

  ∧-intro  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ
           → Δ ⊢ ψ
           -------------------
           → Δ ⊢ φ ∧ ψ

  ∧-elim₁  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ ∧ ψ
           -------------------
           → Δ ⊢ φ

  ∧-elim₂  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ ∧ ψ
           -------------------
           → Δ ⊢ ψ

  -- disjunction

  ∨-intro₁ : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ
           ------------------
           → Δ ⊢ φ ∨ ψ

  ∨-intro₂ : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ ψ
           -------------------
           → Δ ⊢ φ ∨ ψ

  ∨-elim   : {Δ : Hypotheses}
           → {φ₁ φ₂ ψ : Formula}
           → Δ ⊢ φ₁ ∨ φ₂
           → Δ ++ [ φ₁ ] ⊢ ψ
           → Δ ++ [ φ₂ ] ⊢ ψ
           ---------------------
           → Δ ⊢ ψ

  -- implication

  ⇒-intro  : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ++ [ φ ] ⊢ ψ
           --------------------
           → Δ ⊢ φ ⇒ ψ

  ⇒-elim   : {Δ : Hypotheses}
           → {φ ψ : Formula}
           → Δ ⊢ φ ⇒ ψ
           → Δ ⊢ φ
           -------------------
           → Δ ⊢ ψ

  -- square

  □-intro : {Δ : Hypotheses}
          → {φ : Formula}
          → {n : ℕ}
          → (As : Hypotheses)
          → (∀ A → A ∈ As → Δ ⊢ □ A)
          → box-map As ⊢ φ
          ------------------
          → Δ ⊢ □ φ

  □-elim : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ □ φ
          -------------------
          → Δ ⊢ φ

  -- diamond

  ◇-intro : {Δ : Hypotheses}
          → {φ : Formula}
          → Δ ⊢ φ
          -------------------
          → Δ ⊢ ◇ φ

  ◇-elim : {Δ : Hypotheses}
         → {φ ψ : Formula}
         → {n : ℕ}
         → (As : Hypotheses)
         → (∀ A → A ∈ As → Δ ⊢ □ A)
         → Δ ⊢ ◇ φ
         → (box-map As) ++  [ φ ] ⊢ ◇ ψ
         ------------------
         → Δ ⊢ ◇ ψ

{-
   We define negation and logical equivalence as syntactic sugar.
   These definitions are standard logical encodings of `¬` and `⇔`.
-}

¬_ : Formula → Formula              -- unicode \neg
¬ φ = φ ⇒ ⊥

_⇔_ : Formula → Formula → Formula    -- unicode \<=>
φ ⇔ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)

infix 7 ¬_
infix 3 _⇔_


¬-intro : {Δ : Hypotheses}
        → {φ : Formula}
        → Δ ++ [ φ ] ⊢ ⊥
        → Δ ⊢ ¬ φ

¬-intro d = ⇒-intro d

¬-elim : {Δ : Hypotheses}
       → {φ : Formula}
       → Δ ⊢ φ
       → Δ ⊢ ¬ φ
       → Δ ⊢ ⊥

¬-elim d₁ d₂ = ⇒-elim d₂ d₁
