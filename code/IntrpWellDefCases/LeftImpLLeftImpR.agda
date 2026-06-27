{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.LeftImpLLeftImpR where

open import IntrpWellDefCases.Base

mip≗⇐L⇐R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ A' ∷ [] ⊢ B'}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (B' ⇐ A')
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₁} {Λ₁} f (⇐R {Γ₁ ++ B ∷ Λ₁} g)) eq)
      (mip Γ Δ Λ (⇐R {Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁} (⇐L {Γ₁} {Δ₁} {Λ₁ ++ A' ∷ []} f g)) eq)
mip≗⇐L⇐R Γ [] Λ eq = mip[]≗ Γ Λ eq ⇐L⇐R
mip≗⇐L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  with cases++ Γ₁ (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁) Λ (sym eq)
mip≗⇐L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  with cases++ Γ₁ Γ Ω (E ∷ Δ) eq₁
mip≗⇐L⇐R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  with ++? (Ω' ++ E ∷ Δ) Δ₁ Λ Λ₁ eq₂
mip≗⇐L⇐R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , eq₅)
  with ++? Δ₁ Ω' Ω'' (E ∷ Δ) eq₅
mip≗⇐L⇐R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {.(Ω' ++ Ω''')} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , eq₅)
  | inj₁ (Ω''' , eq₆ , refl)
  with cases++ [] Ω''' Δ Ω'' (sym eq₆)
mip≗⇐L⇐R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω'''' ++ Ω'')) Λ {Γ₁} {.(Ω' ++ E ∷ Ω'''')} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Ω' ++ E ∷ Ω'''' ++ Ω'') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (.(E ∷ Ω'''') , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω'''' ++ Ω'') (Λ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Ω'''' ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' (Ω' ++ E ∷ Ω'''') (Λ ++ A' ∷ []) |
          ++?-inj₁ (E ∷ Ω'''') Ω' Ω'' =
    intrp≗
      (~-trans
        (⇐L~⊗ refl (mip⇐R~ (Γ₁ ++ B ∷ []) Ω'' Λ))
        (⇐L⇐R~⊗ {Γ₀ = Γ₁} {Γ₁ = Ω'} {Λ = Λ}
          (mip Ω' (E ∷ Ω'''') [] f refl)
          (mip (Γ₁ ++ B ∷ []) Ω'' (Λ ++ A' ∷ []) g refl)))
mip≗⇐L⇐R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Ω'} {.(E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Δ) , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) (Λ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) Ω' (Λ ++ A' ∷ []) |
          ++?-inj₁ [] Ω' (E ∷ Δ) =
    intrp≗
      (⇐L⇐R~⊗ {Γ₀ = Γ₁} {Γ₁ = Ω'} {Λ = Λ}
        (mip Ω' [] [] f refl)
        (mip (Γ₁ ++ B ∷ []) (E ∷ Δ) (Λ ++ A' ∷ []) g refl))
mip≗⇐L⇐R .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ Δ) Λ {Γ₁} {Δ₁} {.(F ∷ Ω''' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) (Λ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω''' ++ E ∷ Δ) Δ₁ (Λ ++ A' ∷ []) |
          ++?-inj₂ Δ₁ Ω''' (E ∷ Δ) F =
    intrp≗ (g~ ⇐L⇐R)
mip≗⇐L⇐R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) .(F ∷ Ω'' ++ Λ₁) {Γ₁} {.(Ω' ++ E ∷ Δ ++ F ∷ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) (F ∷ Ω'' ++ Λ₁ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ω' ++ E ∷ Δ) Ω'' (Λ₁ ++ A' ∷ []) F =
    intrp≗ (g~ ⇐L⇐R)
mip≗⇐L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , eq₄)
  with ++? Ω Δ₁ Λ Λ₁ eq₂
mip≗⇐L⇐R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , eq₄)
  | inj₁ (Ω'' , eq₅ , eq₆)
  with cases∷ Ω' eq₃
mip≗⇐L⇐R Γ .(B ⇐ A ∷ Δ₁ ++ Ω'') Λ {Γ} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Δ₁ ++ Ω'') , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ Ω'' Δ₁ Λ |
          cases++-inj₁ Γ (Δ₁ ++ Ω'') (Λ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₂ [] Γ (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ (Λ ++ A' ∷ []) =
    intrp≗ refl
mip≗⇐L⇐R Γ (E ∷ .(Ω₀ ++ B ⇐ A ∷ Δ₁ ++ Ω'')) Λ {.(Γ ++ E ∷ Ω₀)} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Δ₁ ++ Ω'') , refl , refl)
  | inj₂ (.(E ∷ Ω₀) , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite ++?-inj₁ Ω'' Δ₁ Λ |
          cases++-inj₁ (Γ ++ E ∷ Ω₀) (Δ₁ ++ Ω'') (Λ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₀) Γ (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ (Λ ++ A' ∷ []) =
    intrp≗ refl
mip≗⇐L⇐R Γ (E ∷ Δ) .(F ∷ Ω'' ++ Λ₁) {Γ₁} {.(Ω ++ F ∷ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , refl)
  | inj₂ (Ω' , eq₃ , refl)
  | inj₂ (F , Ω'' , refl , refl)
  with cases∷ Ω' eq₃
mip≗⇐L⇐R Γ .(B ⇐ A ∷ Ω) .(F ∷ Ω'' ++ Λ₁) {Γ} {.(Ω ++ F ∷ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (Ω , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ Ω Ω'' Λ₁ F |
          cases++-inj₁ Γ Ω (F ∷ Ω'' ++ Λ₁ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₂ [] Γ Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω'' (Λ₁ ++ A' ∷ []) F =
    intrp≗ (g~ ⇐L⇐R)
mip≗⇐L⇐R Γ (E ∷ .(Ω₀ ++ B ⇐ A ∷ Ω)) .(F ∷ Ω'' ++ Λ₁) {.(Γ ++ E ∷ Ω₀)} {.(Ω ++ F ∷ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (Ω , refl , refl)
  | inj₂ (.(E ∷ Ω₀) , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite ++?-inj₂ Ω Ω'' Λ₁ F |
          cases++-inj₁ (Γ ++ E ∷ Ω₀) Ω (F ∷ Ω'' ++ Λ₁ ++ A' ∷ []) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₀) Γ Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω'' (Λ₁ ++ A' ∷ []) F =
    intrp≗ (g~ ⇐L⇐R)
mip≗⇐L⇐R Γ (E ∷ Δ) .(Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁) {.(Γ ++ E ∷ Δ ++ Ω)} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (Ω , refl , refl)
  rewrite cases++-inj₂ Ω (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁ ++ A' ∷ []) (B ⇐ A) =
    let intrp D g0 h0 = mip Γ (E ∷ Δ) (Ω ++ B ∷ Λ₁ ++ A' ∷ []) g refl
    in intrp≗ (g~ (⇐L⇐R {Γ = Γ ++ D ∷ Ω}))
