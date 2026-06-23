{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.Base where

open import Data.Sum using (inj₁; inj₂) public
open import Data.List using (List; []; _∷_; _++_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst) public
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