{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ImpLTensorR1 where

open import IntrpWellDefCases.Base

mip≗⇒L⊗R₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ A'} {h : Ω₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⇒L f (⊗R g h)) eq)
      (mip Γ Δ Λ (⊗R (⇒L f g) h) eq)
mip≗⇒L⊗R₁ Γ Δ Λ eq = {!   !}
