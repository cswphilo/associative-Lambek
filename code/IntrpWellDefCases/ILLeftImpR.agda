{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILLeftImpR where

open import IntrpWellDefCases.Base

mip≗IL⇐R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ : Cxt} {A B : Fma}
  {f : Γ₁ ++ Δ₁ ++ A ∷ [] ⊢ B}
  → (eq : Γ₁ ++ I ∷ Δ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (B ⇐ A)
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁} (⇐R {Γ₁ ++ Δ₁} f)) eq)
      (mip Γ Δ Λ (⇐R {Γ₁ ++ I ∷ Δ₁} (IL {Γ₁} {Δ₁ ++ A ∷ []} f)) eq)
mip≗IL⇐R Γ [] Λ eq = mip[]≗ Γ Λ eq IL⇐R
mip≗IL⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {f} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (I ∷ Δ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗IL⇐R Γ (I ∷ Δ) Λ {Γ} {.(Δ ++ Λ)} {A} {B} {f = f} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] Γ (I ∷ Δ ++ Λ ++ A ∷ []) =
    intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⇐R~ Γ Δ Λ))
mip≗IL⇐R .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) Λ {Γ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {f = f} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Δ ++ Λ ++ A ∷ []) =
    intrp≗ (g~ IL⇐R)
mip≗IL⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {f} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip≗IL⇐R Γ (E ∷ .(Ω ++ I ∷ Ω')) Λ {.(Γ ++ E ∷ Ω)} {.(Ω' ++ Λ)} {A} {B} {f = f} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Ω' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ I |
          ++?-inj₂ Γ Ω (I ∷ Ω' ++ Λ ++ A ∷ []) E |
          cases++-inj₁ Ω Ω' (Λ ++ A ∷ []) I =
    intrp≗ refl
mip≗IL⇐R Γ (E ∷ Δ) .(Ω' ++ I ∷ Δ₁) {.(Γ ++ E ∷ Δ ++ Ω')} {Δ₁} {A} {B} {f = f} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Δ₁ I |
          ++?-inj₂ Γ (Δ ++ Ω') (I ∷ Δ₁ ++ A ∷ []) E |
          cases++-inj₂ Ω' Δ (Δ₁ ++ A ∷ []) I =
    let H = mip Γ (E ∷ Δ) (Ω' ++ Δ₁ ++ A ∷ []) f refl
    in intrp≗ (g~ (IL⇐R {Γ = Γ ++ MIP.D H ∷ Ω'} {Δ = Δ₁}))
