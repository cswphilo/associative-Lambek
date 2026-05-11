{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLImpR where

open import Data.Sum
open import IntrpWellDefCases.Base

mip≗⇒L⇒R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : A' ∷ Γ₁ ++ B ∷ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⇒ B')
      (mip Γ Δ Λ (⇒L f (⇒R g)) eq)
      (mip Γ Δ Λ (⇒R (⇒L {A' ∷ Γ₁} f g)) eq)
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} eq with ++? (Γ ++ Δ) Γ₁ Λ (Δ₁ ++ A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq1 , eq2) with cases++ Δ₁ Ω Λ₁ Λ (sym eq1)
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} eq | inj₁ (Ω , refl , eq2) | inj₁ (Ω' , refl , refl) with cases++ (Γ₁ ++ Δ₁) Γ Ω' Δ eq2
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {.(Ω' ++ Λ)} {A} {B} {A'} {f = f} {g} refl | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (Δ₁ ++ A ⇒ B ∷ Ω'' ++ Δ) Γ₁ Λ |
          cases++-inj₁ Δ₁ (Ω'' ++ Δ) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₁) Ω'' Δ (A ⇒ B) 
            = intrp≗ (g~ ⇒L⇒R)
... | inj₂ (Ω'' , refl , eq3) with ++? Γ Γ₁ Ω'' Δ₁ eq3
mip≗⇒L⇒R Γ .(Ω'' ++ A ⇒ B ∷ Ω') Λ {Γ₁} {Δ₁} {.(Ω' ++ Λ)} {A} {B} refl | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) 
  rewrite ++?-inj₁ (Ω''' ++ Ω'' ++ A ⇒ B ∷ Ω') Γ₁ Λ |
          cases++-inj₁ (Ω''' ++ Ω'') Ω' Λ (A ⇒ B) |
          cases++-inj₂ Ω'' (Γ₁ ++ Ω''') Ω' (A ⇒ B) |
          ++?-inj₁ Ω''' Γ₁ Ω''
            = intrp≗ (g~ ⇒L⇒R)
mip≗⇒L⇒R Γ .(Ω'' ++ A ⇒ B ∷ Ω') Λ {Γ₁} {Δ₁} {.(Ω' ++ Λ)} {A} {B} refl | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₂ (C' , Ω''' , refl , refl)
  rewrite ++?-inj₁ (Δ₁ ++ A ⇒ B ∷ Ω') (Γ ++ C' ∷ Ω''') Λ |
          cases++-inj₁ Δ₁ Ω' Λ (A ⇒ B) |
          cases++-inj₂ (C' ∷ Ω''' ++ Δ₁) Γ Ω' (A ⇒ B) |
          ++?-inj₂ Γ Ω''' Δ₁ C'
            = intrp≗ refl
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} eq | inj₁ (Ω , refl , eq2) | inj₂ (Ω' , refl , refl) with ++? Γ₁ Γ Ω Δ eq2
mip≗⇒L⇒R Γ Δ .(Ω' ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(Ω ++ Ω')} {Λ₁} {A} {B} {A'} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₁ Ω (Γ ++ Ω'') (Ω' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω' Ω Λ₁ (A ⇒ B) |
          ++?-inj₁ Ω'' Γ Ω
            = intrp≗ (g~ (⊗L ⇒L⇒R ∘ ⊗L⇒R))
mip≗⇒L⇒R Γ Δ .(Ω' ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(Ω ++ Ω')} {Λ₁} {A} {B} {A'} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (C' , Ω'' , refl , refl)
  rewrite ++?-inj₁ (C' ∷ Ω'' ++ Δ) Γ₁ (Ω' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω' (Ω'' ++ Δ) Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ₁ Ω'' Δ C'
            = intrp≗ (g~ ⇒L⇒R)
mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} refl | inj₂ (C' , Ω , refl , refl)
  rewrite ++?-inj₂ (Γ ++ Δ) Ω (Δ₁ ++ A ⇒ B ∷ Λ₁) C'
    = intrp≗ (g~ ⇒L⇒R)
 
