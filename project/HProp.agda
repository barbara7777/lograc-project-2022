{-# OPTIONS --allow-unsolved-metas #-}

module HProp where

open import Level

open import Data.Product hiding (∃)
open import Data.Sum
open import Data.Empty
open import Data.Unit

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Relation.Binary.PropositionalEquality as Eq
open Eq renaming ([_] to [|_|])
open Eq.≡-Reasoning

open import Axiom.Extensionality.Propositional renaming (Extensionality to Extensionality-axiom)
postulate fun-ext : ∀ {a b} → Extensionality-axiom a b

-- Propositions are (Set₀) types with at most one inhabitant

is-proposition : Set → Set
is-proposition A = (x y : A) → x ≡ y

-- Truncation structure

postulate
  ∥_∥ : Set → Set
  ∥∥-is-proposition : (A : Set) → is-proposition ∥ A ∥
  ∣_∣ : {A : Set} → A → ∥ A ∥
  ∥∥-elim : {A : Set} {B : Set} → is-proposition B → (A → B) → ∥ A ∥ → B

infix 0 ∥_∥

-- Computation rule for truncation

∥∥-compute : {A : Set} {B : Set}
          → (i : (x y : B) → x ≡ y) (p : A → B) (a : A)
          → ∥∥-elim i p ∣ a ∣ ≡ p a
∥∥-compute i p a = i (∥∥-elim i p ∣ a ∣) (p a)

-- Propositions

record HProp : Set₁ where
  constructor ⟨_,_⟩
  field
    proof : Set
    is-prop : is-proposition proof

open HProp public

abstract
  -- Logic of propositions

  -- truth

  ⊤ʰ : HProp
  ⊤ʰ = ⟨ ⊤ , (λ _ _ → refl) ⟩

  -- falsehood

  ⊥ʰ : HProp
  ⊥ʰ = ⟨ ⊥ , (λ x y → ⊥-elim x) ⟩

  -- conjunction

  _∧ʰ_ : HProp → HProp → HProp
  ⟨ p , ξ ⟩ ∧ʰ ⟨ q , ζ ⟩ = ⟨ p × q , θ ⟩
    where
      θ : (x y : p × q) → x ≡ y
      θ (x₁ , y₁) (x₂ , y₂) with ξ x₁ x₂ | ζ y₁ y₂
      ... | refl | refl = refl

  -- disjunction

  _∨ʰ_ : HProp → HProp → HProp
  ⟨ p , ξ ⟩ ∨ʰ ⟨ q , ζ ⟩ = ⟨ ∥ p ⊎ q ∥ , θ ⟩
    where
      θ : is-proposition ∥ p ⊎ q ∥
      θ = ∥∥-is-proposition _

  -- implication

  _⇒ʰ_ : HProp → HProp → HProp
  ⟨ p , ξ ⟩ ⇒ʰ ⟨ q , ζ ⟩ = ⟨ (p → q) , θ ⟩
    where
      θ : is-proposition (p → q)
      θ f g = fun-ext λ x → ζ(f x) (g x)

  -- existential quantification

  ∃ʰ : (A : Set) → (A → HProp) → HProp
  ∃ʰ A φ = ⟨ ∥ Σ[ x ∈ A ] proof (φ x) ∥ , ∥∥-is-proposition _ ⟩

  -- universal quantification

  ∀ʰ : (A : Set) → (A → HProp) → HProp
  ∀ʰ A φ = ⟨ (∀ x → proof (φ x)) , (λ f g → fun-ext (λ x → is-prop (φ x) (f x) (g x))) ⟩

  -- proofs
  --truth
  ⊤ʰ-intro : proof ⊤ʰ
  ⊤ʰ-intro = tt

  -- falsehood
  ⊥ʰ-elim : {A : HProp} → proof ⊥ʰ → proof A
  ⊥ʰ-elim ()

  -- conjunction
  ∧ʰ-intro : {A B : HProp} → proof A → proof B → proof (A ∧ʰ B)
  ∧ʰ-intro pa pb = pa , pb

  ∧ʰ-elim₁ : {A B : HProp} → proof (A ∧ʰ B) → proof A
  ∧ʰ-elim₁ p = proj₁ p

  ∧ʰ-elim₂ : {A B : HProp} → proof (A ∧ʰ B) → proof B
  ∧ʰ-elim₂ p = proj₂ p

  -- disjunction
  ∨ʰ-intro₁ : {A B : HProp} → proof A → proof (A ∨ʰ B)
  ∨ʰ-intro₁ p = ∣ inj₁ p ∣

  ∨ʰ-intro₂ : {A B : HProp} → proof B → proof (A ∨ʰ B)
  ∨ʰ-intro₂ p =  ∣ inj₂ p ∣

  ∨ʰ-elim : {A B C : HProp} → proof (A ∨ʰ B) → proof (A ⇒ʰ C) → proof (B ⇒ʰ C) → proof C
  ∨ʰ-elim {A} {B} {C} por pac pbc = ∥∥-elim (is-prop C) [ pac , pbc ] por

  -- implication
  ⇒ʰ-intro : {A B : HProp} → (proof A → proof B) → proof (A ⇒ʰ B)
  ⇒ʰ-intro {A} p = p

  ⇒ʰ-elim : {A B : HProp} → proof A → proof (A ⇒ʰ B) → proof B
  ⇒ʰ-elim {B} p q = q p

  -- quantifiers
  ∃ʰ-elim : {A : Set} {φ : A → HProp} (ψ : HProp) →
            ((x : A) → proof (φ x) → proof ψ) → proof (∃ʰ A φ) → proof ψ
  ∃ʰ-elim ψ f p = ∥∥-elim (is-prop ψ) (λ { (x , q) → f x q }) p

  ∃ʰ-intro : {A : Set} {φ : A → HProp} (a : A) → proof (φ a) → proof (∃ʰ A φ)
  ∃ʰ-intro a p = ∣ a , p ∣

  ∀ʰ-elim : {A : Set} {φ : A → HProp} → proof (∀ʰ A φ) → (a : A) → proof (φ a)
  ∀ʰ-elim p a = p a

  ∀ʰ-intro : {A : Set} {φ : A → HProp} → ((a : A) → proof (φ a)) → proof (∀ʰ A φ)
  ∀ʰ-intro p = λ x → p x
