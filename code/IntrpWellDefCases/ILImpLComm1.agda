{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ILImpLComm1 where

open import IntrpWellDefCases.Base

mip≗IL⇒L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ Λ₁ ++ B ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁} {Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁} (⇒L {Γ₁ ++ Λ₁} f g)) eq)
      (mip Γ Δ Λ (⇒L {Γ₁ ++ I ∷ Λ₁} f (IL {Γ₁} {Λ₁ ++ B ∷ Ω₁} g)) eq)
mip≗IL⇒L-comm₁ Γ Δ Λ eq = {!   !}
