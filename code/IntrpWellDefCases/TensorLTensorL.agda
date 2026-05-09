{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLTensorL where

open import IntrpWellDefCases.Base

mip≗⊗L⊗L : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Γ₁ ++ A ∷ B ∷ Δ₁ ++ A' ∷ B' ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁ ++ A ⊗ B ∷ Δ₁} (⊗L f)) eq)
      (mip Γ Δ Λ (⊗L (⊗L {Γ₁ ++ A ∷ B ∷ Δ₁} f)) eq)
mip≗⊗L⊗L Γ Δ Λ eq = {!   !}
