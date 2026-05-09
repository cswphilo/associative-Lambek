{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLImpLAssoc where

open import IntrpWellDefCases.Base

mip≗⊗L⇒L-assoc : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ++ A' ∷ B' ∷ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁ ++ Δ₀} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L (⊗L f) g) eq)
mip≗⊗L⇒L-assoc Γ Δ Λ eq = {!   !}
