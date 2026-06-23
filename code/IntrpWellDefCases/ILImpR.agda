{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILImpR where

open import IntrpWellDefCases.Base

mip≗IL⇒R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ : Cxt} {A B : Fma}
  {f : A ∷ Γ₁ ++ Δ₁ ⊢ B}
  → (eq : Γ₁ ++ I ∷ Δ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A ⇒ B)
      (mip Γ Δ Λ (IL (⇒R f)) eq)
      (mip Γ Δ Λ (⇒R (IL {_ ∷ _} f)) eq)
mip≗IL⇒R Γ Δ Λ = {!!}
