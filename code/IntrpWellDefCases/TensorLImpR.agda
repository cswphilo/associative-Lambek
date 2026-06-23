{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLImpR where

open import IntrpWellDefCases.Base
open import Data.Sum

mip≗⊗L⇒R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ : Cxt} {A B A' B' : Fma}
  {f : A' ∷ Γ₁ ++ A ∷ B ∷ Δ₁ ⊢ B'}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⇒ B')
      (mip Γ Δ Λ (⊗L (⇒R f)) eq)
      (mip Γ Δ Λ (⇒R (⊗L {_ ∷ _} f)) eq)
mip≗⊗L⇒R Γ Δ Λ = {!!}
