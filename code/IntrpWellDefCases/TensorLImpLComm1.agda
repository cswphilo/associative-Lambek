{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLImpLComm1 where

open import IntrpWellDefCases.Base


mip≗⊗L⇒L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ B ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L (⇒L {Γ₁ ++ A' ∷ B' ∷ Λ₁} f g)) eq)
      (mip Γ Δ Λ (⇒L {Γ₁ ++ A' ⊗ B' ∷ Λ₁} f (⊗L g)) eq)
mip≗⊗L⇒L-comm₁ Γ Δ Λ eq = {!   !}
