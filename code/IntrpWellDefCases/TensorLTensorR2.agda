{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLTensorR2 where

open import IntrpWellDefCases.Base

mip≗⊗L⊗R₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Γ₁ ⊢ A'} {g : Δ₁ ++ A ∷ B ∷ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⊗ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⊗L {Γ₁ ++ Δ₁} (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R f (⊗L g)) eq)
mip≗⊗L⊗R₂ Γ Δ Λ = {!!}
