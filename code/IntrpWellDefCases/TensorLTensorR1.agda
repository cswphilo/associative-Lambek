{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLTensorR1 where

open import IntrpWellDefCases.Base

mip≗⊗L⊗R₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Γ₁ ++ A ∷ B ∷ Δ₁ ⊢ A'} {g : Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⊗L (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R (⊗L f) g) eq)
mip≗⊗L⊗R₁ Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⊗R₁
mip≗⊗L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (A ⊗ B ∷ Δ₁ ++ Λ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
... | inj₁ (eq3 , eq4 , eq5)
  with ++? Δ Δ₁ Λ Λ₁ (sym eq5)
mip≗⊗L⊗R₁ Γ (.(A ⊗ B) ∷ Δ₁) Λ
  {Γ} {Δ₁} {Λ} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ Δ₁ Λ (A ⊗ B) |
          ++?-inj₂ Γ (B ∷ Δ₁) Λ A |
          ++?-inj₁ [] Δ₁ Λ |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ₁) =
    intrp≗ refl
mip≗⊗L⊗R₁ Γ (.(A ⊗ B) ∷ .(Δ₁ ++ F ∷ Ω')) Λ
  {Γ} {Δ₁} {.(F ∷ Ω' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (F ∷ Ω' , refl , refl)
  rewrite ++?-inj₂ Γ Δ₁ (F ∷ Ω' ++ Λ) (A ⊗ B) |
          ++?-inj₂ Γ (B ∷ Δ₁) (F ∷ Ω' ++ Λ) A |
          ++?-inj₂ Δ₁ Ω' Λ F |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ₁) =
    intrp≗ (h~ ⊗L⊗R₁)
mip≗⊗L⊗R₁ Γ (.(A ⊗ B) ∷ Δ) .(F ∷ Ω' ++ Λ₁)
  {Γ} {.(Δ ++ F ∷ Ω')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ F ∷ Ω') Λ₁ (A ⊗ B) |
          ++?-inj₂ Γ (B ∷ Δ ++ F ∷ Ω') Λ₁ A |
          ++?-inj₁ (F ∷ Ω') (B ∷ Δ) Λ₁ |
          ++?-inj₁ (F ∷ Ω') Δ Λ₁ |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ ++ F ∷ Ω') =
    intrp≗ refl
mip≗⊗L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  with ++? Δ₁ Ω' Λ₁ (E ∷ Δ ++ Λ) (sym eq3)
... | inj₁ (Ω'' , eq5 , eq6)
  with ++? [] Ω'' (E ∷ Δ ++ Λ) Λ₁ (sym eq5)
mip≗⊗L⊗R₁ .(Γ₁ ++ A ⊗ B ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Ω'} {.(E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⊗ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ A ∷ B ∷ Ω') (E ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ A ⊗ B ∷ Ω') (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⊗L⊗R₁)
mip≗⊗L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  | inj₁ (Ω'' , eq5 , eq6)
  | inj₂ (F , Ω''' , eq7 , eq8)
  with inj∷ eq8
... | refl , eq9
  with ++? Δ Ω''' Λ Λ₁ (sym eq9)
mip≗⊗L⊗R₁ .(Γ₁ ++ A ⊗ B ∷ Ω') (E ∷ .(Ω''' ++ [])) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {Λ} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⊗ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Ω''') , refl , refl)
  | inj₂ (E , Ω''' , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A ∷ B ∷ Ω') Ω''' Λ E |
          ++?-inj₁ [] Ω''' Λ |
          ++?-inj₂ (Γ₁ ++ A ⊗ B ∷ Ω') Ω''' Λ E |
          ++?-inj₁ [] Ω''' Λ |
          ++?-inj₁ (A ⊗ B ∷ Ω') Γ₁ (E ∷ Ω''' ++ []) =
    intrp≗
      (⊗L⊗R₁~Γ
        (mip (Γ₁ ++ A ∷ B ∷ Ω') (E ∷ Ω''') [] f refl)
        g)
mip≗⊗L⊗R₁ .(Γ₁ ++ A ⊗ B ∷ Ω') (E ∷ .(Ω''' ++ G ∷ Ω'''')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {.(G ∷ Ω'''' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⊗ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Ω''') , refl , refl)
  | inj₂ (E , Ω''' , refl , refl)
  | refl , refl
  | inj₁ (G ∷ Ω'''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A ∷ B ∷ Ω') Ω''' (G ∷ Ω'''' ++ Λ) E |
          ++?-inj₂ Ω''' Ω'''' Λ G |
          ++?-inj₂ (Γ₁ ++ A ⊗ B ∷ Ω') Ω''' (G ∷ Ω'''' ++ Λ) E |
          ++?-inj₂ Ω''' Ω'''' Λ G |
          ++?-inj₁ (A ⊗ B ∷ Ω') Γ₁ (E ∷ Ω''' ++ []) =
    intrp≗
      (⊗L⊗R₁~Γ⊗R
        (mip (Γ₁ ++ A ∷ B ∷ Ω') (E ∷ Ω''') [] f refl)
        (mip [] (G ∷ Ω'''') Λ g refl))
mip≗⊗L⊗R₁ .(Γ₁ ++ A ⊗ B ∷ Ω') (E ∷ Δ) .(G ∷ Ω'''' ++ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ G ∷ Ω'''')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⊗ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Δ ++ G ∷ Ω'''') , refl , refl)
  | inj₂ (E , .(Δ ++ G ∷ Ω'''') , refl , refl)
  | refl , refl
  | inj₂ (G , Ω'''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A ∷ B ∷ Ω') (Δ ++ G ∷ Ω'''') Λ₁ E |
          ++?-inj₁ (G ∷ Ω'''') Δ Λ₁ |
          ++?-inj₂ (Γ₁ ++ A ⊗ B ∷ Ω') (Δ ++ G ∷ Ω'''') Λ₁ E |
          ++?-inj₁ (G ∷ Ω'''') Δ Λ₁ |
          ++?-inj₁ (A ⊗ B ∷ Ω') Γ₁ (E ∷ Δ ++ G ∷ Ω'''') =
    intrp≗
      (⊗L⊗R₁~Γ
        (mip (Γ₁ ++ A ∷ B ∷ Ω') (E ∷ Δ) (G ∷ Ω'''') f refl)
        g)
mip≗⊗L⊗R₁ .(Γ₁ ++ A ⊗ B ∷ Δ₁ ++ F ∷ Ω'') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(F ∷ Ω'' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⊗ B ∷ Δ₁ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (.(Δ₁ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₁ (F ∷ Ω'') (Γ₁ ++ A ∷ B ∷ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (F ∷ Ω'') (Γ₁ ++ A ⊗ B ∷ Δ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⊗L⊗R₁)
mip≗⊗L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
... | refl , eq3
  with cases++ Ω Δ (Δ₁ ++ Λ₁) Λ eq3
... | inj₁ (Ω' , eq4 , eq5)
  with ++? Δ₁ Ω' Λ₁ Λ (sym eq5)
mip≗⊗L⊗R₁ Γ (E ∷ .(Ω ++ A ⊗ B ∷ Ω')) .(Ω'' ++ Λ₁)
  {.(Γ ++ E ∷ Ω)} {.(Ω' ++ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' (Ω'' ++ Λ₁) (A ⊗ B) |
          ++?-inj₂ Γ (Ω ++ A ∷ B ∷ Ω' ++ Ω'') Λ₁ E |
          ++?-inj₁ Ω'' (Ω ++ A ∷ B ∷ Ω') Λ₁ |
          ++?-inj₂ Γ (Ω ++ A ⊗ B ∷ Ω' ++ Ω'') Λ₁ E |
          ++?-inj₁ Ω'' (Ω ++ A ⊗ B ∷ Ω') Λ₁ =
    intrp≗ (⊗R~₁ (~-sym (mip⊗L~Δ Γ (E ∷ Ω) Ω' Ω'')) refl)
mip≗⊗L⊗R₁ Γ (E ∷ .(Ω ++ A ⊗ B ∷ Δ₁ ++ F ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω)} {Δ₁} {.(F ∷ Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω (Δ₁ ++ F ∷ Ω'') Λ (A ⊗ B) |
          ++?-inj₂ Γ (Ω ++ A ∷ B ∷ Δ₁) (F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ (Ω ++ A ∷ B ∷ Δ₁) Ω'' Λ F |
          ++?-inj₂ Γ (Ω ++ A ⊗ B ∷ Δ₁) (F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ (Ω ++ A ⊗ B ∷ Δ₁) Ω'' Λ F |
          ++?-inj₂ Γ Ω (A ⊗ B ∷ Δ₁) E |
          cases++-inj₁ Ω Δ₁ [] (A ⊗ B) =
    intrp≗ (h~ ⊗L⊗R₁)
mip≗⊗L⊗R₁ Γ (E ∷ Δ) .(Ω' ++ A ⊗ B ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Δ ++ Ω')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ (Δ₁ ++ Λ₁) (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω' ++ A ∷ B ∷ Δ₁) Λ₁ E |
          ++?-inj₁ (Ω' ++ A ∷ B ∷ Δ₁) Δ Λ₁ |
          ++?-inj₂ Γ (Δ ++ Ω' ++ A ⊗ B ∷ Δ₁) Λ₁ E |
          ++?-inj₁ (Ω' ++ A ⊗ B ∷ Δ₁) Δ Λ₁ |
          ++?-inj₂ Γ (Δ ++ Ω') (A ⊗ B ∷ Δ₁) E |
          cases++-inj₂ Ω' Δ Δ₁ (A ⊗ B) =
    let H = mip Γ (E ∷ Δ) (Ω' ++ A ∷ B ∷ Δ₁) f refl
    in intrp≗ (g~ (⊗L⊗R₁ {Γ = Γ ++ MIP.D H ∷ Ω'} {Δ = Δ₁} {Λ = Λ₁}))
