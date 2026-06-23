{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLTensorR1 where

open import IntrpWellDefCases.Base

mip≗⊗L⊗R₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Γ₁ ++ A ∷ B ∷ Δ₁ ⊢ A'} {g : Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⊗L (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R (⊗L f) g) eq)
mip≗⊗L⊗R₁ Γ Δ Λ = {!!}
