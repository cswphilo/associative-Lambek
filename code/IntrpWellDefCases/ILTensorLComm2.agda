{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILTensorLComm2 where

open import IntrpWellDefCases.Base

mip≗IL⊗L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B C : Fma}
  {f : Γ₁ ++ A ∷ B ∷ Δ₁ ++ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ++ I ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ A ⊗ B ∷ Δ₁} {Λ₁} (⊗L f)) eq)
      (mip Γ Δ Λ (⊗L (IL {Γ₁ ++ A ∷ B ∷ Δ₁} {Λ₁} f)) eq)
mip≗IL⊗L-comm₂ Γ Δ Λ = {!!}
