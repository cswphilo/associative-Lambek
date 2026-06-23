{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ImpLImpR where

open import Data.Sum
open import IntrpWellDefCases.Base

mip≗⇒L⇒R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : A' ∷ Γ₁ ++ B ∷ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⇒ B')
      (mip Γ Δ Λ (⇒L f (⇒R g)) eq)
      (mip Γ Δ Λ (⇒R (⇒L {A' ∷ Γ₁} f g)) eq)
mip≗⇒L⇒R Γ Δ Λ = {!!}
