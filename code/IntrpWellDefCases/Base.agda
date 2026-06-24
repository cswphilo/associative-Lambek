{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.Base where

open import Data.Sum using (inj₁; inj₂) public
open import Data.List using (List; []; _∷_; _++_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst) public
open import Data.Product public

open import SeqCalc public
open import Cut public
open import Utilities public
open import Mip public
open import IntrpTriples public

{-
Shared context for the split-out `mip≗` congruence cases.

Each case file in `IntrpWellDefCases/` isolates one congruence generator of
`_≗_`. The goal is to record the list-equality geometry without having to keep
all twenty cases in one module while the proofs are still incomplete.
-}

record MIP≗ (Γ Δ Λ : Cxt) (C : Fma) (n n' : MIP Γ Δ Λ C) : Set where
  constructor intrp≗
  field
    eq : n ~ n'

mip[]≗ : ∀ Γ Λ {Ω : Cxt} {C : Fma} {f f' : Ω ⊢ C}
  → (eq : Ω ≡ Γ ++ Λ)
  → f ≗ f'
  → MIP≗ Γ [] Λ C (mip Γ [] Λ f eq) (mip Γ [] Λ f' eq)
mip[]≗ Γ Λ refl p = intrp≗ (g~ (IL p))

mipIL~Λ : ∀ Γ Δ Λ₀ Λ₁ {C} {f : Γ ++ Δ ++ Λ₀ ++ Λ₁ ⊢ C}
  → mip Γ Δ (Λ₀ ++ I ∷ Λ₁) (IL {Γ ++ Δ ++ Λ₀} {Λ₁} f) refl
      ~ IL~Λ' {Γ} {Δ} {Λ₀} {Λ₁} (mip Γ Δ (Λ₀ ++ Λ₁) f refl)
mipIL~Λ Γ [] Λ₀ Λ₁ = g~ (~ ILIL)
mipIL~Λ Γ (A ∷ Δ) Λ₀ Λ₁
  rewrite ++?-inj₂ Γ (Δ ++ Λ₀) (I ∷ Λ₁) A |
          cases++-inj₂ Λ₀ Δ Λ₁ I = refl

mipIL~Δ : ∀ Γ Δ₀ Δ₁ Λ {C} {f : Γ ++ Δ₀ ++ Δ₁ ++ Λ ⊢ C}
  → mip Γ (Δ₀ ++ I ∷ Δ₁) Λ (IL {Γ ++ Δ₀} {Δ₁ ++ Λ} f) refl
      ~ IL~Δ' {Γ} {Δ₀} {Δ₁} {Λ} (mip Γ (Δ₀ ++ Δ₁) Λ f refl)
mipIL~Δ Γ [] Δ₁ Λ
  rewrite ++?-inj₁ [] Γ (I ∷ Δ₁ ++ Λ) = refl
mipIL~Δ Γ (A ∷ Δ₀) Δ₁ Λ
  rewrite ++?-inj₂ Γ Δ₀ (I ∷ Δ₁ ++ Λ) A |
          cases++-inj₁ Δ₀ Δ₁ Λ I = refl

mip⇒R~ : ∀ Γ Δ Λ {A B : Fma} {f : A ∷ Γ ++ Δ ++ Λ ⊢ B}
  → mip Γ Δ Λ (⇒R f) refl ~ ⇒R~' (mip (A ∷ Γ) Δ Λ f refl)
mip⇒R~ Γ [] Λ = g~ IL⇒R
mip⇒R~ Γ (E ∷ Δ) Λ = refl

mip⊗R₂~ : ∀ Γ₁ Δ₁ Δ Λ {A B : Fma}
  {f : Γ₁ ⊢ A} {g : Δ₁ ++ Δ ++ Λ ⊢ B}
  → mip (Γ₁ ++ Δ₁) Δ Λ (⊗R f g) refl
      ~ ⊗R~₂' (mip Δ₁ Δ Λ g refl) f
mip⊗R₂~ Γ₁ Δ₁ [] Λ = g~ IL⊗R₂
mip⊗R₂~ Γ₁ Δ₁ (E ∷ Δ) Λ
  rewrite ++?-inj₁ Δ₁ Γ₁ (E ∷ Δ ++ Λ) = refl

mip⇒L~⇒ : ∀ Γ₁ Δ₀ Δ₁ Λ₀ Λ
  {A B C : Fma}
  {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₀ ++ Λ ⊢ C}
  → mip (Γ₁ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Λ₀) Λ (⇒L {Γ₁} {Δ₀ ++ Δ₁} {Λ₀ ++ Λ} f g) refl
      ~ ⇒L~⇒' (mip [] Δ₀ Δ₁ f refl) (mip Γ₁ (B ∷ Λ₀) Λ g refl)
mip⇒L~⇒ Γ₁ Δ₀ [] Λ₀ Λ {A} {B}
  rewrite ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Λ₀ ++ Λ) = refl
mip⇒L~⇒ Γ₁ Δ₀ (D ∷ Δ₁) Λ₀ Λ {A} {B}
  rewrite ++?-inj₂ (Γ₁ ++ Δ₀) Δ₁ (A ⇒ B ∷ Λ₀ ++ Λ) D |
          cases++-inj₂ Δ₀ Γ₁ Δ₁ D |
          cases++-inj₁ Δ₁ Λ₀ Λ (A ⇒ B) = refl

mip⇒L~Δ : ∀ Γ₁ Δ Λ₀ Λ₁
  {A B C : Fma}
  {f : Δ ++ Λ₀ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → mip Γ₁ Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (⇒L {Γ₁} {Δ ++ Λ₀} {Λ₁} f g) refl
      ~ ⇒L~Δ' (mip [] Δ Λ₀ f refl) g
mip⇒L~Δ Γ₁ [] Λ₀ Λ₁ = g~ IL⇒L-assoc
mip⇒L~Δ Γ₁ (D ∷ Δ) Λ₀ Λ₁ {A} {B}
  rewrite ++?-inj₂ Γ₁ (Δ ++ Λ₀) (A ⇒ B ∷ Λ₁) D |
          cases++-inj₂ [] Γ₁ (Δ ++ Λ₀) D |
          cases++-inj₂ Λ₀ Δ Λ₁ (A ⇒ B) = refl

mip⇒L~ΔΓ : ∀ Γ₁ Δ₀ Δ Λ₀ Λ₁
  {A B C : Fma}
  {f : Δ₀ ++ Δ ++ Λ₀ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → mip (Γ₁ ++ Δ₀) Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (⇒L {Γ₁} {Δ₀ ++ Δ ++ Λ₀} {Λ₁} f g) refl
      ~ ⇒L~Δ' (mip Δ₀ Δ Λ₀ f refl) g
mip⇒L~ΔΓ Γ₁ Δ₀ [] Λ₀ Λ₁ = g~ IL⇒L-assoc
mip⇒L~ΔΓ Γ₁ Δ₀ (D ∷ Δ) Λ₀ Λ₁ {A} {B}
  rewrite ++?-inj₂ (Γ₁ ++ Δ₀) (Δ ++ Λ₀) (A ⇒ B ∷ Λ₁) D |
          cases++-inj₂ Δ₀ Γ₁ (Δ ++ Λ₀) D |
          cases++-inj₂ Λ₀ Δ Λ₁ (A ⇒ B) = refl

mip⊗L~Λ : ∀ Γ Δ Λ₀ Λ₁ {A' B' C}
  {f : Γ ++ Δ ++ Λ₀ ++ A' ∷ B' ∷ Λ₁ ⊢ C}
  → mip Γ Δ (Λ₀ ++ A' ⊗ B' ∷ Λ₁) (⊗L {Γ ++ Δ ++ Λ₀} f) refl
      ~ ⊗L~Λ' {Γ} {Δ} {Λ₀} {Λ₁} (mip Γ Δ (Λ₀ ++ A' ∷ B' ∷ Λ₁) f refl)
mip⊗L~Λ Γ [] Λ₀ Λ₁ = g~ IL⊗L-comm₁
mip⊗L~Λ Γ (E ∷ Δ) Λ₀ Λ₁ {A'} {B'}
  rewrite ++?-inj₂ Γ (Δ ++ Λ₀) (A' ⊗ B' ∷ Λ₁) E |
          cases++-inj₂ Λ₀ Δ Λ₁ (A' ⊗ B') = refl

mip⊗L~Δ : ∀ Γ Δ₀ Δ₁ Λ {A' B' C}
  {f : Γ ++ Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Λ ⊢ C}
  → mip Γ (Δ₀ ++ A' ⊗ B' ∷ Δ₁) Λ (⊗L {Γ ++ Δ₀} f) refl
      ~ ⊗L~Δ' {Γ} {Δ₀} {Δ₁} {Λ} (mip Γ (Δ₀ ++ A' ∷ B' ∷ Δ₁) Λ f refl)
mip⊗L~Δ Γ [] Δ₁ Λ {A'} {B'}
  rewrite ++?-inj₁ [] Γ (A' ⊗ B' ∷ Δ₁ ++ Λ) = refl
mip⊗L~Δ Γ (E ∷ Δ₀) Δ₁ Λ {A'} {B'}
  rewrite ++?-inj₂ Γ Δ₀ (A' ⊗ B' ∷ Δ₁ ++ Λ) E |
          cases++-inj₁ Δ₀ Δ₁ Λ (A' ⊗ B') = refl

mip⊗L~Γ : ∀ Γ₀ Γ₁ Δ Λ {A' B' C}
  {f : Γ₀ ++ A' ∷ B' ∷ Γ₁ ++ Δ ++ Λ ⊢ C}
  → mip (Γ₀ ++ A' ⊗ B' ∷ Γ₁) Δ Λ (⊗L {Γ₀} {Γ₁ ++ Δ ++ Λ} f) refl
      ~ ⊗L~Γ' {Γ₀} {Γ₁} {Δ} {Λ} (mip (Γ₀ ++ A' ∷ B' ∷ Γ₁) Δ Λ f refl)
mip⊗L~Γ Γ₀ Γ₁ [] Λ = g~ IL⊗L-comm₂
mip⊗L~Γ Γ₀ Γ₁ (E ∷ Δ) Λ {A'} {B'}
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Γ₁) Γ₀ (E ∷ Δ ++ Λ) = refl
