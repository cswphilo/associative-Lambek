{-# OPTIONS --rewriting #-}

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
mip≗⊗L⇒R Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⇒R
mip≗⊗L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {A'} {B'} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (A ⊗ B ∷ Δ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗⊗L⇒R Γ (A ⊗ B ∷ Δ) Λ {Γ} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {f = f} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (A' ∷ Γ) (A ⊗ B ∷ Δ ++ Λ) =
    intrp≗ refl
mip≗⊗L⇒R .(Γ₁ ++ A ⊗ B ∷ Ω') (E ∷ Δ) Λ {Γ₁} {.(Ω' ++ E ∷ Δ ++ Λ)}
  {A} {B} {A'} {B'} {f = f} refl
  | inj₁ (.(A ⊗ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A ⊗ B ∷ Ω') Γ₁ (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⊗L⇒R)
mip≗⊗L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip≗⊗L⇒R Γ (E ∷ .(Ω ++ A ⊗ B ∷ Ω')) Λ {.(Γ ++ E ∷ Ω)} {.(Ω' ++ Λ)}
  {A} {B} {A'} {B'} {f = f} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Ω' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ (A ⊗ B) |
          ++?-inj₂ Γ Ω (A ⊗ B ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω Ω' Λ (A ⊗ B) =
    intrp≗ refl
mip≗⊗L⇒R Γ (E ∷ Δ) .(Ω' ++ A ⊗ B ∷ Δ₁) {.(Γ ++ E ∷ Δ ++ Ω')} {Δ₁}
  {A} {B} {A'} {B'} {f = f} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Δ₁ (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω') (A ⊗ B ∷ Δ₁) E |
          cases++-inj₂ Ω' Δ Δ₁ (A ⊗ B) =
    let H = mip (A' ∷ Γ) (E ∷ Δ) (Ω' ++ A ∷ B ∷ Δ₁) f refl
    in intrp≗ (g~ (⊗L⇒R {Γ = Γ ++ MIP.D H ∷ Ω'}))
