{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILTensorR1 where

open import IntrpWellDefCases.Base

cut⊗RIR⊗L⊗R : ∀ Γ Δ Λ {A B D : Fma}
  {f : Γ ⊢ A} {g : D ∷ Δ ++ Λ ⊢ B}
  → ⊗R f g ≗
      cut Γ (⊗R IR ax)
        (⊗L {Γ} {Δ ++ Λ} (⊗R (IL {Γ} {[]} f) g)) refl
cut⊗RIR⊗L⊗R Γ Δ Λ {D = D} {g = g}
  rewrite cases++-inj₂ [] Γ (Δ ++ Λ) (I ⊗ D) |
          cases++-inj₂ [] (Γ ++ I ∷ []) (Δ ++ Λ) D |
          cases++-inj₁ Γ [] (D ∷ Δ ++ Λ) I |
          cases++-inj₂ [] Γ [] I =
    ⊗R refl (~ cutaxA-left [] g refl)

mip≗IL⊗R₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A' B' : Fma}
  {f : Γ₁ ++ Δ₁ ⊢ A'} {g : Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ I ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁ ++ Λ₁} (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R (IL {Γ₁} {Δ₁} f) g) eq)
mip≗IL⊗R₁ Γ [] Λ eq = mip[]≗ Γ Λ eq IL⊗R₁
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (I ∷ Δ₁ ++ Λ₁) eq
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₁ (eq3 , eq4 , eq5)
  with ++? Δ Δ₁ Λ Λ₁ (sym eq5)
mip≗IL⊗R₁ Γ (.(I) ∷ []) Λ
  {Γ} {[]} {Λ} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ [] Λ I |
          ++?-inj₁ [] [] Λ |
          ++?-inj₁ [] Γ (I ∷ []) =
    intrp≗ (g~ IL⊗R₁)
mip≗IL⊗R₁ Γ (.(I) ∷ F ∷ Ω') Λ
  {Γ} {[]} {.(F ∷ Ω' ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (F ∷ Ω' , refl , refl)
  rewrite ++?-inj₁ [] Γ (F ∷ Ω' ++ Λ) |
          ++?-inj₂ Γ [] (F ∷ Ω' ++ Λ) I |
          ++?-inj₂ [] Ω' Λ F |
          ++?-inj₁ [] Γ (I ∷ []) =
    let H = mip [] (F ∷ Ω') Λ g refl
    in intrp≗
      (↝∷
        (⊗R IR ax ,
         cut⊗RIR⊗L⊗R Γ [] Λ ,
         (~ IL⊗R₂) ∘ IL⊗R₁)
        refl)
mip≗IL⊗R₁ Γ (.(I) ∷ .(F ∷ Δ₁)) Λ
  {Γ} {F ∷ Δ₁} {Λ} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ Δ₁ Λ F |
          ++?-inj₁ [] Δ₁ Λ |
          ++?-inj₂ Γ (F ∷ Δ₁) Λ I |
          ++?-inj₁ [] (F ∷ Δ₁) Λ |
          ++?-inj₁ [] Γ (I ∷ F ∷ Δ₁) =
    intrp≗ refl
mip≗IL⊗R₁ Γ (.(I) ∷ .((F ∷ Δ₁) ++ G ∷ Ω')) Λ
  {Γ} {F ∷ Δ₁} {.(G ∷ Ω' ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (G ∷ Ω' , refl , refl)
  rewrite ++?-inj₂ Γ Δ₁ (G ∷ Ω' ++ Λ) F |
          ++?-inj₂ Δ₁ Ω' Λ G |
          ++?-inj₂ Γ (F ∷ Δ₁) (G ∷ Ω' ++ Λ) I |
          ++?-inj₂ (F ∷ Δ₁) Ω' Λ G |
          ++?-inj₁ [] Γ (I ∷ F ∷ Δ₁) =
    intrp≗
      (IL⊗R₁~Δ
        (mip Γ (F ∷ Δ₁) [] f refl)
        (mip [] (G ∷ Ω') Λ g refl))
mip≗IL⊗R₁ Γ (.(I) ∷ []) .(F ∷ Ω' ++ Λ₁)
  {Γ} {.(F ∷ Ω')} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (F ∷ Ω') Λ₁ I |
          ++?-inj₁ (F ∷ Ω') [] Λ₁ |
          ++?-inj₁ [] Γ (I ∷ F ∷ Ω') =
    intrp≗ (g~ IL⊗R₁)
mip≗IL⊗R₁ Γ (.(I) ∷ G ∷ Δ) .(F ∷ Ω' ++ Λ₁)
  {Γ} {.(G ∷ Δ ++ F ∷ Ω')} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (G ∷ Δ ++ F ∷ Ω') Λ₁ I |
          ++?-inj₁ (F ∷ Ω') (G ∷ Δ) Λ₁ |
          ++?-inj₁ [] Γ (I ∷ G ∷ Δ ++ F ∷ Ω') |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω') Λ₁ G |
          ++?-inj₁ (F ∷ Ω') Δ Λ₁ =
    intrp≗ refl
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  with ++? Δ₁ Ω' Λ₁ (E ∷ Δ ++ Λ) (sym eq3)
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  | inj₁ (Ω'' , eq5 , eq6)
  with ++? [] Ω'' (E ∷ Δ ++ Λ) Λ₁ (sym eq5)
mip≗IL⊗R₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Ω'} {.(E ∷ Δ ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Ω') (E ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ I ∷ Ω') (E ∷ Δ ++ Λ) =
    intrp≗ (g~ IL⊗R₁)
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  | inj₁ (Ω'' , eq5 , eq6)
  | inj₂ (F , Ω''' , eq7 , eq8)
  with inj∷ eq8
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  | inj₁ (Ω'' , eq5 , eq6)
  | inj₂ (E , Ω''' , eq7 , eq8)
  | refl , eq9
  with ++? Δ Ω''' Λ Λ₁ (sym eq9)
mip≗IL⊗R₁ .(Γ₁ ++ I ∷ Ω') (E ∷ .(Ω''' ++ [])) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {Λ} {A'} {B'} {f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Ω''') , refl , refl)
  | inj₂ (E , Ω''' , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') Ω''' Λ E |
          ++?-inj₁ [] Ω''' Λ |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω') Ω''' Λ E |
          ++?-inj₁ [] Ω''' Λ |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Ω''' ++ []) =
    intrp≗
      (IL⊗R₁~Γ
        (mip (Γ₁ ++ Ω') (E ∷ Ω''') [] f refl)
        g)
mip≗IL⊗R₁ .(Γ₁ ++ I ∷ Ω') (E ∷ .(Ω''' ++ F ∷ Ω''''')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {.(F ∷ Ω''''' ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Ω''') , refl , refl)
  | inj₂ (E , Ω''' , refl , refl)
  | refl , refl
  | inj₁ (F ∷ Ω''''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') Ω''' (F ∷ Ω''''' ++ Λ) E |
          ++?-inj₂ Ω''' Ω''''' Λ F |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω') Ω''' (F ∷ Ω''''' ++ Λ) E |
          ++?-inj₂ Ω''' Ω''''' Λ F |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Ω''' ++ []) =
    intrp≗
      (IL⊗R₁~Γ⊗R
        (mip (Γ₁ ++ Ω') (E ∷ Ω''') [] f refl)
        (mip [] (F ∷ Ω''''') Λ g refl))
mip≗IL⊗R₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) .(F ∷ Ω'''' ++ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ F ∷ Ω'''')} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Δ ++ F ∷ Ω'''') , refl , refl)
  | inj₂ (E , .(Δ ++ F ∷ Ω'''') , refl , refl)
  | refl , refl
  | inj₂ (F , Ω'''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ F ∷ Ω'''') Λ₁ E |
          ++?-inj₁ (F ∷ Ω'''') Δ Λ₁ |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω') (Δ ++ F ∷ Ω'''') Λ₁ E |
          ++?-inj₁ (F ∷ Ω'''') Δ Λ₁ |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Δ ++ F ∷ Ω'''') =
    intrp≗
      (IL⊗R₁~Γ
        (mip (Γ₁ ++ Ω') (E ∷ Δ) (F ∷ Ω'''') f refl)
        g)
mip≗IL⊗R₁ .(Γ₁ ++ I ∷ Δ₁ ++ F ∷ Ω'') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(F ∷ Ω'' ++ E ∷ Δ ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₁ (.(I ∷ Δ₁ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (.(Δ₁ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₁ (F ∷ Ω'') (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (F ∷ Ω'') (Γ₁ ++ I ∷ Δ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ IL⊗R₁)
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  with cases++ Ω Δ (Δ₁ ++ Λ₁) Λ eq3
mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₁ (Ω' , eq4 , eq5)
  with ++? Δ₁ Ω' Λ₁ Λ (sym eq5)
mip≗IL⊗R₁ Γ (E ∷ .(Ω ++ I ∷ Ω')) .(Ω'' ++ Λ₁)
  {.(Γ ++ E ∷ Ω)} {.(Ω' ++ Ω'')} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' (Ω'' ++ Λ₁) I |
          ++?-inj₂ Γ (Ω ++ Ω' ++ Ω'') Λ₁ E |
          ++?-inj₁ Ω'' (Ω ++ Ω') Λ₁ |
          ++?-inj₂ Γ (Ω ++ I ∷ Ω' ++ Ω'') Λ₁ E |
          ++?-inj₁ Ω'' (Ω ++ I ∷ Ω') Λ₁ |
          ++?-inj₂ Γ Ω (I ∷ Ω' ++ Ω'') E |
          cases++-inj₁ Ω Ω' Ω'' I =
    intrp≗ refl
mip≗IL⊗R₁ Γ (E ∷ .(Ω ++ I ∷ Δ₁ ++ F ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω)} {Δ₁} {.(F ∷ Ω'' ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω (Δ₁ ++ F ∷ Ω'') Λ I |
          ++?-inj₂ Γ (Ω ++ Δ₁) (F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ (Ω ++ Δ₁) Ω'' Λ F |
          ++?-inj₂ Γ (Ω ++ I ∷ Δ₁) (F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ (Ω ++ I ∷ Δ₁) Ω'' Λ F |
          ++?-inj₂ Γ Ω (I ∷ Δ₁) E |
          cases++-inj₁ Ω Δ₁ [] I =
    intrp≗ (h~ IL⊗R₁)
mip≗IL⊗R₁ Γ (E ∷ Δ) .(Ω' ++ I ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Δ ++ Ω')} {Δ₁} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ (Δ₁ ++ Λ₁) I |
          ++?-inj₂ Γ (Δ ++ Ω' ++ Δ₁) Λ₁ E |
          ++?-inj₁ (Ω' ++ Δ₁) Δ Λ₁ |
          ++?-inj₂ Γ (Δ ++ Ω' ++ I ∷ Δ₁) Λ₁ E |
          ++?-inj₁ (Ω' ++ I ∷ Δ₁) Δ Λ₁ |
          ++?-inj₂ Γ (Δ ++ Ω') (I ∷ Δ₁) E |
          cases++-inj₂ Ω' Δ Δ₁ I =
    intrp≗
      (IL⊗R₁~Λ
        (mip Γ (E ∷ Δ) (Ω' ++ Δ₁) f refl)
        g)
