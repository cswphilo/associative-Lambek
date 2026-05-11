{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ImpLImpR where

open import Data.Sum
open import IntrpWellDefCases.Base

mip≗⇒L⇒R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : A' ∷ Γ₁ ++ B ∷ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⇒ B')
      (mip Γ Δ Λ (⇒L f (⇒R g)) eq)
      (mip Γ Δ Λ (⇒R (⇒L f g)) eq)
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} eq with ++? (Γ ++ Δ) Γ₁ Λ (Δ₁ ++ A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq1 , eq2) with cases++ Δ₁ Ω Λ₁ Λ (sym eq1)
... | inj₁ (Ω' , refl , refl) with cases++ (Γ₁ ++ Δ₁) Γ Ω' Δ eq2
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {.(Ω' ++ Λ)} {A} {B} refl | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (Δ₁ ++ A ⇒ B ∷ Ω'' ++ Δ) Γ₁ Λ = {!!}
... | inj₂ (Ω'' , refl , eq3) with ++? Γ Γ₁ Ω'' Δ₁ eq3
mip≗⇒L⇒R Γ .(Ω'' ++ A ⇒ B ∷ Ω') Λ {Γ₁} {Δ₁} {.(Ω' ++ Λ)} {A} {B} refl | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω') , eq1 , eq2) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq3) | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ (Ω''' ++ Ω'' ++ A ⇒ B ∷ Ω') Γ₁ Λ = {!!}
... | inj₂ (C' , Ω''' , refl , refl) = {!!}
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} eq | inj₁ (Ω , eq1 , eq2) | inj₂ (Ω' , refl , refl) = {!!}
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} eq | inj₂ y = {!!}
