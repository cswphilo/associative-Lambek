{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILTensorLComm1 where

open import IntrpWellDefCases.Base


mip≗IL⊗L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B C : Fma}
  {f : Γ₁ ++ Δ₁ ++ A ∷ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Δ₁ ++ A ⊗ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁ ++ A ⊗ B ∷ Λ₁} (⊗L {Γ₁ ++ Δ₁} f)) eq)
      (mip Γ Δ Λ (⊗L {Γ₁ ++ I ∷ Δ₁} (IL {Γ₁} {Δ₁ ++ A ∷ B ∷ Λ₁} f)) eq)
mip≗IL⊗L-comm₁ Γ Δ Λ = {!!}
