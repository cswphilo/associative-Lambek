{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILImpLAssoc where

open import IntrpWellDefCases.Base


mip≗IL⇒L-assoc : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ : Cxt} {A B C : Fma}
  {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ Δ₀} {Δ₁ ++ A ⇒ B ∷ Λ₁} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L (IL {Δ₀} {Δ₁} f) g) eq)
mip≗IL⇒L-assoc Γ Δ Λ eq = {!   !}
