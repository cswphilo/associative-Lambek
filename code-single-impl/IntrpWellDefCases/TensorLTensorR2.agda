{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLTensorR2 where

open import IntrpWellDefCases.Base

mip≗⊗L⊗R₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B A' B' : Fma}
  {f : Γ₁ ⊢ A'} {g : Δ₁ ++ A ∷ B ∷ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⊗ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⊗L {Γ₁ ++ Δ₁} (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R f (⊗L g)) eq)
mip≗⊗L⊗R₂ Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⊗R₂
mip≗⊗L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  with ++? Γ (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) (A ⊗ B ∷ Λ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗⊗L⊗R₂ .(Γ₁ ++ Δ₁) (.(A ⊗ B) ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ Δ₁ Γ₁ (A ⊗ B ∷ Δ ++ Λ) =
    intrp≗
      (~-trans
        (⊗L~Δ (mip⊗R₂~ Γ₁ Δ₁ (A ∷ B ∷ Δ) Λ))
        (⊗R~₂ (~-sym (mip⊗L~Δ Δ₁ [] Δ Λ)) refl))
mip≗⊗L⊗R₂ .(Γ₁ ++ Δ₁ ++ A ⊗ B ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₁ (.(A ⊗ B ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (Δ₁ ++ A ⊗ B ∷ Ω') Γ₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⊗ B ∷ Ω') Δ₁ (E ∷ Δ ++ Λ) =
    intrp≗
      (~-trans
        (⊗L~Γ {Γ₀ = Γ₁ ++ Δ₁} {Γ₁ = Ω'}
          (mip⊗R₂~ Γ₁ (Δ₁ ++ A ∷ B ∷ Ω') (E ∷ Δ) Λ))
        (~-trans
          (⊗L⊗R₂~Γ
            {Γ₀ = Δ₁} {Γ₁ = Ω'}
            (mip (Δ₁ ++ A ∷ B ∷ Ω') (E ∷ Δ) Λ g refl)
            f)
          refl))
mip≗⊗L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
... | refl , eq3
  with cases++ Γ Γ₁ Ω Δ₁ eq1
... | inj₁ (Ω' , eq4 , eq5)
  with cases++ Ω Δ Λ₁ Λ eq3
mip≗⊗L⊗R₂ Γ (E ∷ .(Ω' ++ A ⊗ B ∷ [])) Λ
  {.(Γ ++ E ∷ Ω')} {[]} {Λ} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Ω' [] Λ (A ⊗ B) |
          ++?-inj₂ Γ Ω' (A ∷ B ∷ Λ) E |
          ++?-inj₂ Ω' (B ∷ []) Λ A |
          ++?-inj₂ Γ Ω' (A ⊗ B ∷ Λ) E |
          ++?-inj₂ Ω' [] Λ (A ⊗ B) = intrp≗ (h~ ⊗L⊗R₂)
mip≗⊗L⊗R₂ Γ (E ∷ .(Ω' ++ A ⊗ B ∷ F ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω')} {[]} {.(F ∷ Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (F ∷ Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω' (F ∷ Ω'') Λ (A ⊗ B) |
          ++?-inj₂ Γ Ω' (A ∷ B ∷ F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' (B ∷ F ∷ Ω'') Λ A |
          ++?-inj₂ Γ Ω' (A ⊗ B ∷ F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' (F ∷ Ω'') Λ (A ⊗ B) |
          ++?-inj₁ [] [] (A ⊗ B ∷ F ∷ Ω'' ++ Λ) =
    intrp≗ (h~ ⊗L⊗R₂)
mip≗⊗L⊗R₂ Γ (E ∷ .((Ω' ++ F ∷ Δ₁) ++ A ⊗ B ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω')} {F ∷ Δ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ F ∷ Δ₁) , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Ω' ++ F ∷ Δ₁) Ω'' Λ (A ⊗ B) |
          ++?-inj₂ Γ Ω' (F ∷ Δ₁ ++ A ∷ B ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' (Δ₁ ++ A ∷ B ∷ Ω'') Λ F |
          ++?-inj₂ Γ Ω' (F ∷ Δ₁ ++ A ⊗ B ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' (Δ₁ ++ A ⊗ B ∷ Ω'') Λ F |
          ++?-inj₂ [] Δ₁ (A ⊗ B ∷ Ω'' ++ Λ) F |
          cases++-inj₁ Δ₁ Ω'' Λ (A ⊗ B) =
    intrp≗ (h~ ⊗L⊗R₂)
mip≗⊗L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₁ (Ω' , eq4 , eq5)
  | inj₂ (Ω'' , eq6 , eq7)
  with ++? Δ Ω' Ω'' Δ₁ (trans (sym eq5) eq7)
mip≗⊗L⊗R₂ Γ (E ∷ Ω') .(Ω'' ++ A ⊗ B ∷ Λ₁)
  {.(Γ ++ E ∷ Ω')} {Ω''} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ Ω'') , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ Ω'' Ω' Λ₁ (A ⊗ B) |
          ++?-inj₂ Γ Ω' (Ω'' ++ A ∷ B ∷ Λ₁) E |
          ++?-inj₁ [] Ω' (Ω'' ++ A ∷ B ∷ Λ₁) |
          ++?-inj₂ Γ Ω' (Ω'' ++ A ⊗ B ∷ Λ₁) E |
          ++?-inj₁ [] Ω' (Ω'' ++ A ⊗ B ∷ Λ₁) =
    intrp≗ (g~ ⊗L⊗R₂)
mip≗⊗L⊗R₂ Γ (E ∷ .(Ω' ++ F ∷ Ω'''')) .(Ω'' ++ A ⊗ B ∷ Λ₁)
  {.(Γ ++ E ∷ Ω')} {.(F ∷ Ω'''' ++ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ F ∷ Ω'''' ++ Ω'') , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (F ∷ Ω'''' , refl , refl)
  rewrite cases++-inj₂ Ω'' (Ω' ++ F ∷ Ω'''') Λ₁ (A ⊗ B) |
          ++?-inj₂ Γ Ω' (F ∷ Ω'''' ++ Ω'' ++ A ∷ B ∷ Λ₁) E |
          ++?-inj₂ Ω' Ω'''' (Ω'' ++ A ∷ B ∷ Λ₁) F |
          ++?-inj₂ Γ Ω' (F ∷ Ω'''' ++ Ω'' ++ A ⊗ B ∷ Λ₁) E |
          ++?-inj₂ Ω' Ω'''' (Ω'' ++ A ⊗ B ∷ Λ₁) F |
          cases++-inj₂ Ω'' Ω'''' Λ₁ (A ⊗ B) =
    let H = mip Γ (E ∷ Ω') [] f refl
        K = mip [] (F ∷ Ω'''') (Ω'' ++ A ∷ B ∷ Λ₁) g refl
    in intrp≗
      (g~
        ((⊗L⊗L {Γ = Γ} {Δ = Ω''} {Λ = Λ₁} {A = MIP.D H} {B = MIP.D K}
            {A' = A} {B' = B}
            {f = ⊗R (MIP.g H) (MIP.g K)})
        ∘ ⊗L {Γ = Γ} {Δ = Ω'' ++ A ⊗ B ∷ Λ₁} {A = MIP.D H} {B = MIP.D K}
            (⊗L⊗R₂ {Γ = Γ ++ MIP.D H ∷ []} {Δ = MIP.D K ∷ Ω''} {Λ = Λ₁}
              {A = A} {B = B} {A' = A'} {B' = B'} {f = MIP.g H} {g = MIP.g K})))
mip≗⊗L⊗R₂ Γ (E ∷ Δ) .(F ∷ Ω''' ++ Δ₁ ++ A ⊗ B ∷ Λ₁)
  {.(Γ ++ E ∷ Δ ++ F ∷ Ω''')} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ F ∷ Ω''' ++ Δ₁) , refl , refl)
  | refl , refl
  | inj₁ (.(Δ ++ F ∷ Ω''') , refl , refl)
  | inj₂ (.(F ∷ Ω''' ++ Δ₁) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₂ (F ∷ Ω''' ++ Δ₁) Δ Λ₁ (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''') (Δ₁ ++ A ∷ B ∷ Λ₁) E |
          ++?-inj₁ (F ∷ Ω''') Δ (Δ₁ ++ A ∷ B ∷ Λ₁) |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''') (Δ₁ ++ A ⊗ B ∷ Λ₁) E |
          ++?-inj₁ (F ∷ Ω''') Δ (Δ₁ ++ A ⊗ B ∷ Λ₁) =
    intrp≗ (g~ ⊗L⊗R₂)
mip≗⊗L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₂ (Ω' , eq4 , eq5)
  with cases++ Ω Δ Λ₁ Λ eq3
mip≗⊗L⊗R₂ .(Γ₁ ++ Ω') (E ∷ .(Ω ++ A ⊗ B ∷ Ω'')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω Ω'' Λ (A ⊗ B) |
          ++?-inj₁ Ω' Γ₁ (E ∷ Ω ++ A ∷ B ∷ Ω'' ++ Λ) |
          ++?-inj₁ Ω' Γ₁ (E ∷ Ω ++ A ⊗ B ∷ Ω'' ++ Λ) =
    intrp≗ (⊗R~₂ (~-sym (mip⊗L~Δ Ω' (E ∷ Ω) Ω'' Λ {f = g})) refl)
mip≗⊗L⊗R₂ .(Γ₁ ++ Ω') (E ∷ Δ) .(Ω'' ++ A ⊗ B ∷ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ Ω'')} {Λ₁} {A} {B} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ Ω'') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₂ Ω'' Δ Λ₁ (A ⊗ B) |
          ++?-inj₁ Ω' Γ₁ (E ∷ Δ ++ Ω'' ++ A ∷ B ∷ Λ₁) |
          ++?-inj₁ Ω' Γ₁ (E ∷ Δ ++ Ω'' ++ A ⊗ B ∷ Λ₁) =
    intrp≗
      (~-trans
        (⊗L⊗R₂~Λ
          (mip Ω' (E ∷ Δ) (Ω'' ++ A ∷ B ∷ Λ₁) g refl)
          f)
        (⊗R~₂
          (~-sym (mip⊗L~Λ Ω' (E ∷ Δ) Ω'' Λ₁ {f = g}))
          refl))
