{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLLeftImpR where

open import IntrpWellDefCases.Base

mip≗⇒L⇐R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ A' ∷ [] ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (B' ⇐ A')
      (mip Γ Δ Λ (⇒L {Γ₁} {Δ₁} {Λ₁} f (⇐R {Γ₁ ++ B ∷ Λ₁} g)) eq)
      (mip Γ Δ Λ (⇐R {Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁} (⇒L {Γ₁} {Δ₁} {Λ₁ ++ A' ∷ []} f g)) eq)
mip≗⇒L⇐R Γ [] Λ eq = mip[]≗ Γ Λ eq ⇒L⇐R
mip≗⇒L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  with ++? Γ (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) (A ⇒ B ∷ Λ₁) eq
mip≗⇒L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  with cases∷ Ω eq₁
mip≗⇒L⇐R .(Γ₁ ++ Δ₁) (.(A ⇒ B) ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Λ ++ A' ∷ []) =
    intrp≗ (g~ ⇒L⇐R)
mip≗⇒L⇐R .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⇒ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A ⇒ B ∷ Ω') (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ ++ A' ∷ []) =
    intrp≗ (g~ ⇒L⇐R)
mip≗⇒L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  with cases++ Γ Γ₁ Ω Δ₁ eq₁
mip≗⇒L⇐R Γ (E ∷ Δ) Λ
  {.(Γ ++ F ∷ Ω')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , .(Ω' ++ Δ₁) , eq₁ , eq₂)
  | inj₁ (Ω' , refl , refl)
  with inj∷ eq₂
mip≗⇒L⇐R Γ (E ∷ Δ) Λ
  {.(Γ ++ E ∷ Ω')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (E , .(Ω' ++ Δ₁) , eq₁ , eq₂)
  | inj₁ (Ω' , refl , refl)
  | refl , eq₅
  with cases++ (Ω' ++ Δ₁) Δ Λ₁ Λ eq₅
mip≗⇒L⇐R Γ (E ∷ .(Ω' ++ Δ₁ ++ A ⇒ B ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω')} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ Δ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω' ++ Δ₁) (A ⇒ B ∷ Ω'' ++ Λ ++ A' ∷ []) E |
          cases++-inj₁ Γ Ω' Δ₁ E |
          cases++-inj₁ (Ω' ++ Δ₁) Ω'' (Λ ++ A' ∷ []) (A ⇒ B) =
    intrp≗ refl
mip≗⇒L⇐R Γ (E ∷ Δ) Λ
  {.(Γ ++ E ∷ Ω')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (E , .(Ω' ++ Δ₁) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  | refl , eq₅
  | inj₂ (Ω'' , eq₆ , eq₇)
  with ++? Δ Ω' Ω'' Δ₁ eq₇
mip≗⇒L⇐R Γ (E ∷ .(Ω' ++ Ω''')) .(Ω'' ++ A ⇒ B ∷ Λ₁)
  {.(Γ ++ E ∷ Ω')} {.(Ω''' ++ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ Ω''' ++ Ω'') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | refl , refl
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ Ω''' Ω' Ω'' |
          ++?-inj₂ Γ (Ω' ++ Ω''' ++ Ω'') (A ⇒ B ∷ Λ₁ ++ A' ∷ []) E |
          cases++-inj₁ Γ Ω' (Ω''' ++ Ω'') E |
          cases++-inj₂ Ω'' (Ω' ++ Ω''') (Λ₁ ++ A' ∷ []) (A ⇒ B) |
          ++?-inj₁ Ω''' Ω' Ω'' =
    intrp≗ (g~ (⊗L ⇒L⇐R ∘ ⊗L⇐R))
mip≗⇒L⇐R Γ (E ∷ Δ) .(F ∷ Ω''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁)
  {.(Γ ++ E ∷ Δ ++ F ∷ Ω''')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ F ∷ Ω''' ++ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω''') , refl , refl)
  | refl , refl
  | inj₂ (.(F ∷ Ω''' ++ Δ₁) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ Δ Ω''' Δ₁ F |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''' ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ A' ∷ []) E |
          cases++-inj₁ Γ (Δ ++ F ∷ Ω''') Δ₁ E |
          cases++-inj₂ (F ∷ Ω''' ++ Δ₁) Δ (Λ₁ ++ A' ∷ []) (A ⇒ B) |
          ++?-inj₂ Δ Ω''' Δ₁ F =
    intrp≗ (g~ ⇒L⇐R)
mip≗⇒L⇐R Γ (E ∷ Δ) Λ
  {Γ₁} {.(Ω' ++ F ∷ Ω)} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₂ (Ω' , refl , refl)
  with inj∷ eq₂
mip≗⇒L⇐R .(Γ₁ ++ Ω') (E ∷ Δ) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , refl , eq₂)
  | inj₂ (Ω' , refl , refl)
  | refl , eq₅
  with cases++ Ω Δ Λ₁ Λ eq₅
mip≗⇒L⇐R .(Γ₁ ++ Ω') (E ∷ .(Ω ++ A ⇒ B ∷ Ω'')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') Ω (A ⇒ B ∷ Ω'' ++ Λ ++ A' ∷ []) E |
          cases++-inj₂ Ω' Γ₁ Ω E |
          cases++-inj₁ Ω Ω'' (Λ ++ A' ∷ []) (A ⇒ B) =
    intrp≗ (g~ ⇒L⇐R)
mip≗⇒L⇐R .(Γ₁ ++ Ω') (E ∷ Δ) .(Ω'' ++ A ⇒ B ∷ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ Ω'') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | refl , refl
  | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ Ω'') (A ⇒ B ∷ Λ₁ ++ A' ∷ []) E |
          cases++-inj₂ Ω' Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ (Λ₁ ++ A' ∷ []) (A ⇒ B) =
    intrp≗ (g~ ⇒L⇐R)
