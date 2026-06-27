{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLLeftImpR where

open import IntrpWellDefCases.Base

mip≗⊗L⇐R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ : Cxt} {A B A' B' : Fma}
  {f : Γ₁ ++ A ∷ B ∷ Δ₁ ++ A' ∷ [] ⊢ B'}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (B' ⇐ A')
      (mip Γ Δ Λ (⊗L {Γ₁} {Δ₁} {A} {B} (⇐R {Γ₁ ++ A ∷ B ∷ Δ₁} f)) eq)
      (mip Γ Δ Λ (⇐R {Γ₁ ++ A ⊗ B ∷ Δ₁} (⊗L {Γ₁} {Δ₁ ++ A' ∷ []} f)) eq)
mip≗⊗L⇐R Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⇐R
mip≗⊗L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {A'} {B'} {f} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (A ⊗ B ∷ Δ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗⊗L⇐R Γ (A ⊗ B ∷ Δ) Λ {Γ} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {f = f} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] Γ (A ⊗ B ∷ Δ ++ Λ ++ A' ∷ []) =
    intrp≗ refl
mip≗⊗L⇐R .(Γ₁ ++ A ⊗ B ∷ Ω') (E ∷ Δ) Λ {Γ₁} {.(Ω' ++ E ∷ Δ ++ Λ)}
  {A} {B} {A'} {B'} {f = f} refl
  | inj₁ (.(A ⊗ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A ⊗ B ∷ Ω') Γ₁ (E ∷ Δ ++ Λ ++ A' ∷ []) =
    intrp≗ (g~ ⊗L⇐R)
mip≗⊗L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {A'} {B'} {f} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip≗⊗L⇐R Γ (E ∷ .(Ω ++ A ⊗ B ∷ Ω')) Λ {.(Γ ++ E ∷ Ω)} {.(Ω' ++ Λ)}
  {A} {B} {A'} {B'} {f = f} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Ω' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ (A ⊗ B) |
          ++?-inj₂ Γ Ω (A ⊗ B ∷ Ω' ++ Λ ++ A' ∷ []) E |
          cases++-inj₁ Ω Ω' (Λ ++ A' ∷ []) (A ⊗ B) =
    intrp≗ refl
mip≗⊗L⇐R Γ (E ∷ Δ) .(Ω' ++ A ⊗ B ∷ Δ₁) {.(Γ ++ E ∷ Δ ++ Ω')} {Δ₁}
  {A} {B} {A'} {B'} {f = f} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Δ₁ (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω') (A ⊗ B ∷ Δ₁ ++ A' ∷ []) E |
          cases++-inj₂ Ω' Δ (Δ₁ ++ A' ∷ []) (A ⊗ B) =
    let H = mip Γ (E ∷ Δ) (Ω' ++ A ∷ B ∷ Δ₁ ++ A' ∷ []) f refl
    in intrp≗ (g~ (⊗L⇐R {Γ = Γ ++ MIP.D H ∷ Ω'}))
