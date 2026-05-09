{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILIL where

open import IntrpWellDefCases.Base
open import Utilities

mip≗ILIL : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {C : Fma}
  {f : Γ₁ ++ Δ₁ ++ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Δ₁ ++ I ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ I ∷ Δ₁} {Λ₁} (IL {Γ₁} {Δ₁ ++ Λ₁} f)) eq)
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁ ++ I ∷ Λ₁} (IL {Γ₁ ++ Δ₁} {Λ₁} f)) eq)
mip≗ILIL Γ Δ Λ eq = {!   !}
