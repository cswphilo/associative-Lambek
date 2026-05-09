{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLImpLComm2 where

open import IntrpWellDefCases.Base

mip≗⊗L⇒L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L f (⊗L {Γ₁ ++ B ∷ Λ₁} g)) eq)
mip≗⊗L⇒L-comm₂ Γ Δ Λ eq = {!   !}
