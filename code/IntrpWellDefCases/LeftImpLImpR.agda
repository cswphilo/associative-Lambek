{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.LeftImpLImpR where

open import IntrpWellDefCases.Base
open import Relation.Binary.PropositionalEquality using (inspect; [_])

idCxt : Cxt → Cxt
idCxt Γ = Γ

mip≗⇐L⇒R-slice[] : ∀ Γ₁ Ω' Ω'' Λ E Δ
  {A B A' B' : Fma}
  {f : Ω' ⊢ A} {g : A' ∷ Γ₁ ++ B ∷ Ω'' ++ Λ ⊢ B'}
  → (eq₆ : E ∷ Δ ≡ Ω'')
  → (eq : Γ₁ ++ B ⇐ A ∷ Ω' ++ Ω'' ++ Λ
        ≡ Γ₁ ++ B ⇐ A ∷ Ω' ++ E ∷ Δ ++ Λ)
  → MIP≗ (Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ (A' ⇒ B')
      (mip (Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ
        (⇐L {Γ₁} {Ω'} {Ω'' ++ Λ} f (⇒R g)) eq)
      (mip (Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ
        (⇒R (⇐L {A' ∷ Γ₁} {Ω'} {Ω'' ++ Λ} f g)) eq)
mip≗⇐L⇒R-slice[] Γ₁ Ω' .(E ∷ Δ) Λ E Δ {A} {B} {A'} {B'} {f} {g} refl refl
  rewrite cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) Ω' Λ |
          ++?-inj₁ [] Ω' (E ∷ Δ) =
    intrp≗
      (⇐L⇒R~⊗
        (mip Ω' [] [] f refl)
        (mip (A' ∷ Γ₁ ++ B ∷ []) (E ∷ Δ) Λ g refl))

mip≗⇐L⇒R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : A' ∷ Γ₁ ++ B ∷ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⇒ B')
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₁} {Λ₁} f (⇒R {Γ₁ ++ B ∷ Λ₁} g)) eq)
      (mip Γ Δ Λ (⇒R {Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁} (⇐L {A' ∷ Γ₁} {Δ₁} {Λ₁} f g)) eq)
mip≗⇐L⇒R Γ [] Λ eq = mip[]≗ Γ Λ eq ⇐L⇒R
mip≗⇐L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  with cases++ Γ₁ (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁) Λ (sym eq)
mip≗⇐L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  with cases++ Γ₁ Γ Ω (E ∷ Δ) eq₁
mip≗⇐L⇒R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  with ++? (Ω' ++ E ∷ Δ) Δ₁ Λ Λ₁ eq₂
mip≗⇐L⇒R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , eq₅)
  with ++? Δ₁ Ω' Ω'' (E ∷ Δ) eq₅
mip≗⇐L⇒R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {.(Ω' ++ Ω''')} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , eq₅)
  | inj₁ (Ω''' , eq₆ , refl)
  with cases++ [] Ω''' Δ Ω'' (sym eq₆)
mip≗⇐L⇒R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω'''' ++ Ω'')) Λ {Γ₁} {.(Ω' ++ E ∷ Ω'''')} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Ω' ++ E ∷ Ω'''' ++ Ω'') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (.(E ∷ Ω'''') , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω'''' ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Ω'''' ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' (Ω' ++ E ∷ Ω'''') Λ |
          ++?-inj₁ (E ∷ Ω'''') Ω' Ω'' =
    intrp≗
      (~-trans
        (⇐L~⊗ refl (mip⇒R~ (Γ₁ ++ B ∷ []) Ω'' Λ))
        (⇐L⇒R~⊗
          (mip Ω' (E ∷ Ω'''') [] f refl)
          (mip (A' ∷ Γ₁ ++ B ∷ []) Ω'' Λ g refl)))
mip≗⇐L⇒R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Ω'} {.(E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Δ) , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) Ω' Λ |
          ++?-inj₁ [] Ω' (E ∷ Δ) =
    intrp≗
      (⇐L⇒R~⊗
        (mip Ω' [] [] f refl)
        (mip (A' ∷ Γ₁ ++ B ∷ []) (E ∷ Δ) Λ g refl))
mip≗⇐L⇒R .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {.(F ∷ Ω₀ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω₀ ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω₀) , refl , refl)
  | inj₁ (.(F ∷ Ω₀ ++ E ∷ Δ) , refl , refl)
  | inj₂ (F , Ω₀ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω₀ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω₀) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω₀ ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ Ω₀ (E ∷ Δ) F =
    intrp≗
      (⇐L⇒R~Γ
        (mip (A' ∷ Γ₁ ++ B ∷ F ∷ Ω₀) (E ∷ Δ) Λ g refl)
        f)
mip≗⇐L⇒R .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) .(F ∷ Ω₀ ++ Λ₁) {Γ₁} {.(Ω' ++ E ∷ Δ ++ F ∷ Ω₀)} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (F , Ω₀ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) (F ∷ Ω₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ω' ++ E ∷ Δ) Ω₀ Λ₁ F =
    intrp≗
      (⇐L⇒R~Δ
        (mip Ω' (E ∷ Δ) (F ∷ Ω₀) f refl)
        g)
mip≗⇐L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , eq₄)
  with ++? Ω Δ₁ Λ Λ₁ eq₂
mip≗⇐L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , eq₄)
  | inj₁ (Ω'' , eq₅ , eq₆)
  with cases∷ Ω' eq₃
mip≗⇐L⇒R Γ .(B ⇐ A ∷ Δ₁ ++ Ω'') Λ {Γ} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Δ₁ ++ Ω'') , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ Ω'' Δ₁ Λ |
          cases++-inj₁ Γ (Δ₁ ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₂ [] Γ (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ Λ =
    intrp≗ refl
mip≗⇐L⇒R Γ (E ∷ .(Ω₀ ++ B ⇐ A ∷ Δ₁ ++ Ω'')) Λ {.(Γ ++ E ∷ Ω₀)} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(Δ₁ ++ Ω'') , refl , refl)
  | inj₂ (.(E ∷ Ω₀) , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite ++?-inj₁ Ω'' Δ₁ Λ |
          cases++-inj₁ (Γ ++ E ∷ Ω₀) (Δ₁ ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₀) Γ (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ Λ =
    intrp≗ refl
mip≗⇐L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq₁ , refl)
  | inj₂ (Ω' , eq₃ , refl)
  | inj₂ (F , Ω'' , refl , refl)
  with cases∷ Ω' eq₃
mip≗⇐L⇒R Γ .(B ⇐ A ∷ Ω) .(F ∷ Ω'' ++ Λ₁) {Γ} {.(Ω ++ F ∷ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (Ω , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ Ω Ω'' Λ₁ F |
          cases++-inj₁ Γ Ω (F ∷ Ω'' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω'' Λ₁ F =
    intrp≗ (g~ ⇐L⇒R)
mip≗⇐L⇒R Γ (E ∷ .(Ω₀ ++ B ⇐ A ∷ Ω)) .(F ∷ Ω'' ++ Λ₁) {.(Γ ++ E ∷ Ω₀)} {.(Ω ++ F ∷ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (Ω , refl , refl)
  | inj₂ (.(E ∷ Ω₀) , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite ++?-inj₂ Ω Ω'' Λ₁ F |
          cases++-inj₁ (Γ ++ E ∷ Ω₀) Ω (F ∷ Ω'' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₀) Γ Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω'' Λ₁ F =
    intrp≗ (g~ ⇐L⇒R)
mip≗⇐L⇒R Γ (E ∷ Δ) .(Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁) {.(Γ ++ E ∷ Δ ++ Ω)} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (Ω , refl , refl)
  rewrite cases++-inj₂ Ω (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁) (B ⇐ A) =
    let intrp D g0 h0 = mip (A' ∷ Γ) (E ∷ Δ) (Ω ++ B ∷ Λ₁) g refl
    in intrp≗ (g~ (⇐L⇒R {Γ = Γ ++ D ∷ Ω}))
