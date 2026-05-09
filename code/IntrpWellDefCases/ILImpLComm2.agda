{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILImpLComm2 where

open import IntrpWellDefCases.Base


mip≗IL⇒L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁} {Ω₁} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L f (IL {Γ₁ ++ B ∷ Λ₁} {Ω₁} g)) eq)
mip≗IL⇒L-comm₂ Γ Δ Λ eq = {!   !}
