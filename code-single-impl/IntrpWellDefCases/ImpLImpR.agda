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
mip≗⇒L⇒R Γ [] Λ eq = mip[]≗ Γ Λ eq ⇒L⇒R
mip≗⇒L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  with ++? Γ (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) (A ⇒ B ∷ Λ₁) eq
mip≗⇒L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗⇒L⇒R .(Γ₁ ++ Δ₁) (.(A ⇒ B) ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Λ) =
    intrp≗
      (⇒L⇒R~⇒
        (mip [] Δ₁ [] f refl)
        (mip (A' ∷ Γ₁) (B ∷ Δ) Λ g refl))
mip≗⇒L⇒R .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⇒ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A ⇒ B ∷ Ω') (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) =
    intrp≗
      (⇒L⇒R~Γ
        (mip (A' ∷ Γ₁ ++ B ∷ Ω') (E ∷ Δ) Λ g refl)
        f)
mip≗⇒L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with cases++ Γ Γ₁ Ω Δ₁ eq1
mip≗⇒L⇒R Γ (E ∷ Δ) Λ
  {.(Γ ++ F ∷ Ω')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , .(Ω' ++ Δ₁) , eq1 , eq2)
  | inj₁ (Ω' , refl , refl)
  with inj∷ eq2
mip≗⇒L⇒R Γ (E ∷ Δ) Λ
  {.(Γ ++ E ∷ Ω')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (E , .(Ω' ++ Δ₁) , eq1 , eq2)
  | inj₁ (Ω' , refl , refl)
  | refl , eq5
  with cases++ (Ω' ++ Δ₁) Δ Λ₁ Λ eq5
mip≗⇒L⇒R Γ (E ∷ .(Ω' ++ Δ₁ ++ A ⇒ B ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω')} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ Δ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω' ++ Δ₁) (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₁ Γ Ω' Δ₁ E |
          cases++-inj₁ (Ω' ++ Δ₁) Ω'' Λ (A ⇒ B) =
    intrp≗ refl
... | inj₂ (Ω'' , eq6 , eq7)
  with ++? Δ Ω' Ω'' Δ₁ eq7
mip≗⇒L⇒R Γ (E ∷ .(Ω' ++ Ω''')) .(Ω'' ++ A ⇒ B ∷ Λ₁)
  {.(Γ ++ E ∷ Ω')} {.(Ω''' ++ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ Ω''' ++ Ω'') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | refl , refl
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ Ω''' Ω' Ω'' |
          ++?-inj₂ Γ (Ω' ++ Ω''' ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Γ Ω' (Ω''' ++ Ω'') E |
          cases++-inj₂ Ω'' (Ω' ++ Ω''') Λ₁ (A ⇒ B) |
          ++?-inj₁ Ω''' Ω' Ω'' =
    intrp≗
      (⇒L⇒R~⊗
          (mip [] Ω''' Ω'' f refl)
          (mip (A' ∷ Γ) (E ∷ Ω') (B ∷ Λ₁) g refl))
mip≗⇒L⇒R Γ (E ∷ Δ) .(F ∷ Ω''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁)
  {.(Γ ++ E ∷ Δ ++ F ∷ Ω''')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ F ∷ Ω''' ++ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω''') , refl , refl)
  | refl , refl
  | inj₂ (.(F ∷ Ω''' ++ Δ₁) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ Δ Ω''' Δ₁ F |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''' ++ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Γ (Δ ++ F ∷ Ω''') Δ₁ E |
          cases++-inj₂ (F ∷ Ω''' ++ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω''' Δ₁ F =
    intrp≗ (g~ ⇒L⇒R)
mip≗⇒L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  with inj∷ eq2
mip≗⇒L⇒R .(Γ₁ ++ Ω') (E ∷ Δ) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , refl , eq2)
  | inj₂ (Ω' , refl , refl)
  | refl , eq5
  with cases++ Ω Δ Λ₁ Λ eq5
mip≗⇒L⇒R .(Γ₁ ++ Ω') (E ∷ .(Ω ++ A ⇒ B ∷ Ω'')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω Ω'' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Ω') Ω (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ Ω' (A' ∷ Γ₁) Ω E |
          cases++-inj₁ Ω Ω'' Λ (A ⇒ B) =
    intrp≗ (g~ ⇒L⇒R)
mip≗⇒L⇒R .(Γ₁ ++ Ω') (E ∷ Δ) .(Ω'' ++ A ⇒ B ∷ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ Ω'') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | refl , refl
  | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ Ω' (A' ∷ Γ₁) (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) =
    intrp≗ (g~ ⇒L⇒R)
