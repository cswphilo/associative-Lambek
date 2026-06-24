{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLTensorL where

open import IntrpWellDefCases.Base

mip≗⊗L⊗L : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Γ₁ ++ A ∷ B ∷ Δ₁ ++ A' ∷ B' ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁ ++ A ⊗ B ∷ Δ₁} (⊗L f)) eq)
      (mip Γ Δ Λ (⊗L (⊗L {Γ₁ ++ A ∷ B ∷ Δ₁} f)) eq)
mip≗⊗L⊗L Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⊗L
mip≗⊗L⊗L Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  with ++? Γ (Γ₁ ++ A ⊗ B ∷ Δ₁) (E ∷ Δ ++ Λ) (A' ⊗ B' ∷ Λ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗⊗L⊗L .(Γ₁ ++ A ⊗ B ∷ Δ₁) (A' ⊗ B' ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ (A ⊗ B ∷ Δ₁) Γ₁ (A' ∷ B' ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⊗ B ∷ Δ₁) Γ₁ (A' ⊗ B' ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ A ∷ B ∷ Δ₁) (A' ⊗ B' ∷ Δ ++ Λ) =
    intrp≗ refl
mip≗⊗L⊗L .(Γ₁ ++ A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₁ (.(A' ⊗ B' ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A ⊗ B ∷ Δ₁ ++ A' ∷ B' ∷ Ω') Γ₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Ω') Γ₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A' ⊗ B' ∷ Ω') (Γ₁ ++ A ∷ B ∷ Δ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⊗L⊗L)
mip≗⊗L⊗L Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
mip≗⊗L⊗L Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  with cases++ Ω Δ Λ₁ Λ eq3
... | inj₁ (Ω' , eq4 , eq5)
  with ++? Γ Γ₁ (E ∷ Ω) (A ⊗ B ∷ Δ₁) eq1
... | inj₁ (Ξ , eq6 , eq7)
  with cases∷ Ξ eq6
mip≗⊗L⊗L Γ (A ⊗ B ∷ .(Δ₁ ++ A' ⊗ B' ∷ Ω')) Λ
  {Γ} {Δ₁} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (A ⊗ B , Δ₁ , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₁ Δ₁ Ω' Λ (A' ⊗ B') |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Ω' ++ Λ) |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ₁ ++ A' ∷ B' ∷ Ω' ++ Λ) |
          ++?-inj₂ Γ (B ∷ Δ₁) (A' ⊗ B' ∷ Ω' ++ Λ) A |
          cases++-inj₁ Δ₁ Ω' Λ (A' ⊗ B') =
    intrp≗
      (h~ ⊗L⊗L)
mip≗⊗L⊗L .(Γ₁ ++ A ⊗ B ∷ Ω₀) (E ∷ .(Ω ++ A' ⊗ B' ∷ Ω')) Λ
  {Γ₁} {.(Ω₀ ++ E ∷ Ω)} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(A ⊗ B ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ (A' ⊗ B') |
          ++?-inj₁ (A ⊗ B ∷ Ω₀) Γ₁ (E ∷ Ω ++ A' ∷ B' ∷ Ω' ++ Λ) |
          ++?-inj₁ (A ⊗ B ∷ Ω₀) Γ₁ (E ∷ Ω ++ A' ⊗ B' ∷ Ω' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ A ∷ B ∷ Ω₀) Ω (A' ⊗ B' ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω Ω' Λ (A' ⊗ B') =
    intrp≗ refl
mip≗⊗L⊗L Γ (E ∷ .(Ω₀ ++ A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Ω')) Λ
  {.(Γ ++ E ∷ Ω₀)} {Δ₁} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (E , .(Ω₀ ++ A ⊗ B ∷ Δ₁) , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ (E , Ω₀ , refl , refl)
  rewrite cases++-inj₁ (Ω₀ ++ A ⊗ B ∷ Δ₁) Ω' Λ (A' ⊗ B') |
          ++?-inj₂ Γ Ω₀ (A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Ω' ++ Λ) E |
          ++?-inj₂ Γ Ω₀ (A ⊗ B ∷ Δ₁ ++ A' ∷ B' ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω₀ (Δ₁ ++ A' ⊗ B' ∷ Ω') Λ (A ⊗ B) |
          cases++-inj₁ Ω₀ (Δ₁ ++ A' ∷ B' ∷ Ω') Λ (A ⊗ B) |
          ++?-inj₂ Γ (Ω₀ ++ A ∷ B ∷ Δ₁) (A' ⊗ B' ∷ Ω' ++ Λ) E |
          cases++-inj₁ (Ω₀ ++ A ∷ B ∷ Δ₁) Ω' Λ (A' ⊗ B') =
    intrp≗ (h~ ⊗L⊗L)
mip≗⊗L⊗L Γ (E ∷ Δ) .(Ω' ++ A' ⊗ B' ∷ Λ₁)
  {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (E , .(Δ ++ Ω') , eq1 , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  with ++? Γ Γ₁ (E ∷ Δ ++ Ω') (A ⊗ B ∷ Δ₁) eq1
... | inj₁ (Ξ , eq4 , eq5)
  with cases∷ Ξ eq4
mip≗⊗L⊗L Γ (A ⊗ B ∷ Δ) .(Ω' ++ A' ⊗ B' ∷ Λ₁)
  {Γ} {.(Δ ++ Ω')} {Λ₁} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (A ⊗ B , .(Δ ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Λ₁ (A' ⊗ B') |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ ++ Ω' ++ A' ⊗ B' ∷ Λ₁) |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ ++ Ω' ++ A' ∷ B' ∷ Λ₁) |
          ++?-inj₂ Γ (B ∷ Δ ++ Ω') (A' ⊗ B' ∷ Λ₁) A |
          cases++-inj₂ Ω' Δ Λ₁ (A' ⊗ B') =
    intrp≗ refl
mip≗⊗L⊗L .(Γ₁ ++ A ⊗ B ∷ Ω₀) (E ∷ Δ) .(Ω' ++ A' ⊗ B' ∷ Λ₁)
  {Γ₁} {.(Ω₀ ++ E ∷ Δ ++ Ω')} {Λ₁} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(A ⊗ B ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Λ₁ (A' ⊗ B') |
          ++?-inj₁ (A ⊗ B ∷ Ω₀) Γ₁ (E ∷ Δ ++ Ω' ++ A' ⊗ B' ∷ Λ₁) |
          ++?-inj₁ (A ⊗ B ∷ Ω₀) Γ₁ (E ∷ Δ ++ Ω' ++ A' ∷ B' ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ A ∷ B ∷ Ω₀) (Δ ++ Ω') (A' ⊗ B' ∷ Λ₁) E |
          cases++-inj₂ Ω' Δ Λ₁ (A' ⊗ B') =
    let H = mip (Γ₁ ++ A ∷ B ∷ Ω₀) (E ∷ Δ) (Ω' ++ A' ∷ B' ∷ Λ₁) f refl
    in intrp≗ (g~ (⊗L⊗L {Γ = Γ₁} {Δ = Ω₀ ++ MIP.D H ∷ Ω'} {Λ = Λ₁}))
mip≗⊗L⊗L Γ (E ∷ Δ) .(Ω' ++ A' ⊗ B' ∷ Λ₁)
  {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (E , .(Δ ++ Ω') , eq1 , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₂ (F , Ω₀ , eq4 , eq5)
  with inj∷ eq5
mip≗⊗L⊗L Γ (E ∷ Δ) .(Ω' ++ A' ⊗ B' ∷ Λ₁)
  {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (E , .(Δ ++ Ω') , eq1 , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₂ (E , Ω₀ , eq4 , eq5)
  | refl , eq6
  with cases++ Ω₀ Δ Δ₁ Ω' eq6
mip≗⊗L⊗L Γ (E ∷ .(Ω₀ ++ A ⊗ B ∷ Ω'')) .(Ω' ++ A' ⊗ B' ∷ Λ₁)
  {.(Γ ++ E ∷ Ω₀)} {.(Ω'' ++ Ω')} {Λ₁} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (E , .(Ω₀ ++ A ⊗ B ∷ Ω'' ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₂ (E , Ω₀ , refl , refl)
  | refl , refl
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₂ Ω' (Ω₀ ++ A ⊗ B ∷ Ω'') Λ₁ (A' ⊗ B') |
          ++?-inj₂ Γ Ω₀ (A ⊗ B ∷ Ω'' ++ Ω' ++ A' ⊗ B' ∷ Λ₁) E |
          ++?-inj₂ Γ Ω₀ (A ⊗ B ∷ Ω'' ++ Ω' ++ A' ∷ B' ∷ Λ₁) E |
          cases++-inj₁ Ω₀ Ω'' (Ω' ++ A' ⊗ B' ∷ Λ₁) (A ⊗ B) |
          cases++-inj₁ Ω₀ Ω'' (Ω' ++ A' ∷ B' ∷ Λ₁) (A ⊗ B) |
          ++?-inj₂ Γ (Ω₀ ++ A ∷ B ∷ Ω'' ++ Ω') (A' ⊗ B' ∷ Λ₁) E |
          cases++-inj₂ Ω' (Ω₀ ++ A ∷ B ∷ Ω'') Λ₁ (A' ⊗ B') =
    intrp≗ refl
mip≗⊗L⊗L Γ (E ∷ Δ) .(Ω'' ++ A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Λ₁)
  {.(Γ ++ E ∷ Δ ++ Ω'')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (E , .(Δ ++ Ω'' ++ A ⊗ B ∷ Δ₁) , refl , refl)
  | refl , refl
  | inj₂ (.(Ω'' ++ A ⊗ B ∷ Δ₁) , refl , refl)
  | inj₂ (E , .(Δ ++ Ω'') , refl , refl)
  | refl , refl
  | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₂ (Ω'' ++ A ⊗ B ∷ Δ₁) Δ Λ₁ (A' ⊗ B') |
          ++?-inj₂ Γ (Δ ++ Ω'') (A ⊗ B ∷ Δ₁ ++ A' ⊗ B' ∷ Λ₁) E |
          ++?-inj₂ Γ (Δ ++ Ω'') (A ⊗ B ∷ Δ₁ ++ A' ∷ B' ∷ Λ₁) E |
          cases++-inj₂ Ω'' Δ (Δ₁ ++ A' ⊗ B' ∷ Λ₁) (A ⊗ B) |
          cases++-inj₂ Ω'' Δ (Δ₁ ++ A' ∷ B' ∷ Λ₁) (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω'' ++ A ∷ B ∷ Δ₁) (A' ⊗ B' ∷ Λ₁) E |
          cases++-inj₂ (Ω'' ++ A ∷ B ∷ Δ₁) Δ Λ₁ (A' ⊗ B') =
    let H = mip Γ (E ∷ Δ) (Ω'' ++ A ∷ B ∷ Δ₁ ++ A' ∷ B' ∷ Λ₁) f refl
    in intrp≗ (g~ (⊗L⊗L {Γ = Γ ++ MIP.D H ∷ Ω''} {Δ = Δ₁} {Λ = Λ₁}))
