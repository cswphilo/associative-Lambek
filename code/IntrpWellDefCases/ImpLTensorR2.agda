{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ImpLTensorR2 where

open import IntrpWellDefCases.Base

mip≗⇒L⊗R₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Ω₁ ⊢ A'} {h : Γ₁ ++ B ∷ Λ₁ ⊢ B'}
  → (eq : Ω₁ ++ Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⇒L {Ω₁ ++ Γ₁} f (⊗R g h)) eq)
      (mip Γ Δ Λ (⊗R g (⇒L f h)) eq)
mip≗⇒L⊗R₂ Γ Δ Λ = {!!}
