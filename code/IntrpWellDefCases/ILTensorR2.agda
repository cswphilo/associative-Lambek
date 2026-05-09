{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILTensorR2 where

open import IntrpWellDefCases.Base

mip≗IL⊗R₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A' B' : Fma}
  {f : Γ₁ ⊢ A'} {g : Δ₁ ++ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ I ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (IL {Γ₁ ++ Δ₁} {Λ₁} (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R f (IL {Δ₁} {Λ₁} g)) eq)
mip≗IL⊗R₂ Γ Δ Λ eq = {!   !}
