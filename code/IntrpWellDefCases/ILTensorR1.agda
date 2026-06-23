{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILTensorR1 where

open import IntrpWellDefCases.Base

mip≗IL⊗R₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A' B' : Fma}
  {f : Γ₁ ++ Δ₁ ⊢ A'} {g : Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ I ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁ ++ Λ₁} (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R (IL {Γ₁} {Δ₁} f) g) eq)
mip≗IL⊗R₁ Γ Δ Λ = {!!}
