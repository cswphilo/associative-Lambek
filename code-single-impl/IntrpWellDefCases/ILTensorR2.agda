{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILTensorR2 where

open import IntrpWellDefCases.Base
open import IntrpWellDefCases.ILIL using (mipIL~Γ)

cut⊗R⊗L⊗RIR : ∀ Γ Λ {A B D : Fma}
  {f : Γ ++ D ∷ [] ⊢ A} {g : Λ ⊢ B}
  → ⊗R f g ≗
      cut Γ (⊗R ax IR)
        (⊗L {Γ} {Λ} (⊗R f (IL {[]} {Λ} g))) refl
cut⊗R⊗L⊗RIR Γ Λ {D = D} {f = f}
  rewrite cases++-inj₂ [] Γ Λ (D ⊗ I) |
          cases++-inj₂ [] (Γ ++ D ∷ []) Λ I |
          cases++-inj₁ Γ [] Λ D =
    ⊗R (~ cutaxA-left Γ f refl) refl

mip≗IL⊗R₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A' B' : Fma}
  {f : Γ₁ ⊢ A'} {g : Δ₁ ++ Λ₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ I ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (IL {Γ₁ ++ Δ₁} {Λ₁} (⊗R f g)) eq)
      (mip Γ Δ Λ (⊗R f (IL {Δ₁} {Λ₁} g)) eq)
mip≗IL⊗R₂ Γ [] Λ eq = mip[]≗ Γ Λ eq IL⊗R₂
mip≗IL⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  with ++? Γ (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) (I ∷ Λ₁) eq
mip≗IL⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗IL⊗R₂ .(Γ₁ ++ Δ₁) (.(I) ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Δ ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ Δ₁ Γ₁ (I ∷ Δ ++ Λ) =
    intrp≗
      (~-trans
        (IL~Δ (mip⊗R₂~ Γ₁ Δ₁ Δ Λ))
        (⊗R~₂ (~-sym (mipIL~Δ Δ₁ [] Δ Λ)) refl))
mip≗IL⊗R₂ .(Γ₁ ++ Δ₁ ++ I ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (Δ₁ ++ I ∷ Ω') Γ₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Ω') Δ₁ (E ∷ Δ ++ Λ) =
    intrp≗
      (~-trans
        (IL~Γ {Γ₀ = Γ₁ ++ Δ₁} {Γ₁ = Ω'}
          (mip⊗R₂~ Γ₁ (Δ₁ ++ Ω') (E ∷ Δ) Λ))
        (IL⊗R₂~Γ
          (mip (Δ₁ ++ Ω') (E ∷ Δ) Λ g refl)
          f))
mip≗IL⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
mip≗IL⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  with cases++ Γ Γ₁ Ω Δ₁ eq1
mip≗IL⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₁ (Ω' , eq4 , eq5)
  with cases++ Ω Δ Λ₁ Λ eq3
mip≗IL⊗R₂ Γ (E ∷ .(Ω' ++ I ∷ [])) Λ
  {.(Γ ++ E ∷ Ω')} {[]} {Λ} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Ω' [] Λ I |
          ++?-inj₂ Γ Ω' Λ E |
          ++?-inj₁ [] Ω' Λ |
          ++?-inj₂ Γ Ω' (I ∷ Λ) E |
          ++?-inj₂ Ω' [] Λ I =
    intrp≗
      (↝∷
        (⊗R ax IR ,
         cut⊗R⊗L⊗RIR Γ Λ ,
         (~ IL⊗R₁) ∘ IL⊗R₂)
        refl)
mip≗IL⊗R₂ Γ (E ∷ .(Ω' ++ I ∷ F ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω')} {[]} {.(F ∷ Ω'' ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω' , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (F ∷ Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω' (F ∷ Ω'') Λ I |
          ++?-inj₂ Γ Ω' (F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' Ω'' Λ F |
          ++?-inj₂ Γ Ω' (I ∷ F ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' (F ∷ Ω'') Λ I |
          ++?-inj₁ [] [] (I ∷ F ∷ Ω'' ++ Λ) =
    intrp≗
      (IL⊗R₂~Δ
        (mip Γ (E ∷ Ω') [] f refl)
        (mip [] (F ∷ Ω'') Λ g refl))
mip≗IL⊗R₂ Γ (E ∷ .((Ω' ++ F ∷ Δ₁) ++ I ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω')} {F ∷ Δ₁} {.(Ω'' ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ F ∷ Δ₁) , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Ω' ++ F ∷ Δ₁) Ω'' Λ I |
          ++?-inj₂ Γ Ω' (F ∷ Δ₁ ++ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' (Δ₁ ++ Ω'') Λ F |
          ++?-inj₂ Γ Ω' (F ∷ Δ₁ ++ I ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' (Δ₁ ++ I ∷ Ω'') Λ F |
          ++?-inj₂ [] Δ₁ (I ∷ Ω'' ++ Λ) F |
          cases++-inj₁ Δ₁ Ω'' Λ I =
    intrp≗
      (IL⊗R₂~Δ
        (mip Γ (E ∷ Ω') [] f refl)
        (mip [] (F ∷ Δ₁ ++ Ω'') Λ g refl))
... | inj₂ (Ω'' , eq6 , eq7)
  with ++? Δ Ω' Ω'' Δ₁ (trans (sym eq5) eq7)
mip≗IL⊗R₂ Γ (E ∷ Ω') .(Ω'' ++ I ∷ Λ₁)
  {.(Γ ++ E ∷ Ω')} {Ω''} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ Ω'') , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ Ω'' Ω' Λ₁ I |
          ++?-inj₂ Γ Ω' (Ω'' ++ Λ₁) E |
          ++?-inj₁ [] Ω' (Ω'' ++ Λ₁) |
          ++?-inj₂ Γ Ω' (Ω'' ++ I ∷ Λ₁) E |
          ++?-inj₁ [] Ω' (Ω'' ++ I ∷ Λ₁) =
    intrp≗ (g~ IL⊗R₂)
mip≗IL⊗R₂ Γ (E ∷ .(Ω' ++ F ∷ Ω'''')) .(Ω'' ++ I ∷ Λ₁)
  {.(Γ ++ E ∷ Ω')} {.(F ∷ Ω'''' ++ Ω'')} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Ω' ++ F ∷ Ω'''' ++ Ω'') , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (F ∷ Ω'''' , refl , refl)
  rewrite cases++-inj₂ Ω'' (Ω' ++ F ∷ Ω'''') Λ₁ I |
          ++?-inj₂ Γ Ω' (F ∷ Ω'''' ++ Ω'' ++ Λ₁) E |
          ++?-inj₂ Ω' Ω'''' (Ω'' ++ Λ₁) F |
          ++?-inj₂ Γ Ω' (F ∷ Ω'''' ++ Ω'' ++ I ∷ Λ₁) E |
          ++?-inj₂ Ω' Ω'''' (Ω'' ++ I ∷ Λ₁) F |
          cases++-inj₂ Ω'' Ω'''' Λ₁ I =
    intrp≗ (g~ (IL⊗L-comm₂ ∘ ⊗L IL⊗R₂))
mip≗IL⊗R₂ Γ (E ∷ Δ) .(F ∷ Ω''' ++ Δ₁ ++ I ∷ Λ₁)
  {.(Γ ++ E ∷ Δ ++ F ∷ Ω''')} {Δ₁} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ F ∷ Ω''' ++ Δ₁) , refl , refl)
  | refl , refl
  | inj₁ (.(Δ ++ F ∷ Ω''') , refl , refl)
  | inj₂ (.(F ∷ Ω''' ++ Δ₁) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₂ (F ∷ Ω''' ++ Δ₁) Δ Λ₁ I |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''') (Δ₁ ++ Λ₁) E |
          ++?-inj₁ (F ∷ Ω''') Δ (Δ₁ ++ Λ₁) |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''') (Δ₁ ++ I ∷ Λ₁) E |
          ++?-inj₁ (F ∷ Ω''') Δ (Δ₁ ++ I ∷ Λ₁) =
    intrp≗ (g~ IL⊗R₂)
mip≗IL⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A'} {B'} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₂ (Ω' , eq4 , eq5)
  with cases++ Ω Δ Λ₁ Λ eq3
mip≗IL⊗R₂ .(Γ₁ ++ Ω') (E ∷ .(Ω ++ I ∷ Ω'')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {.(Ω'' ++ Λ)} {A'} {B'} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω Ω'' Λ I |
          ++?-inj₁ Ω' Γ₁ (E ∷ Ω ++ Ω'' ++ Λ) |
          ++?-inj₁ Ω' Γ₁ (E ∷ Ω ++ I ∷ Ω'' ++ Λ) |
          ++?-inj₂ Ω' Ω (I ∷ Ω'' ++ Λ) E |
          cases++-inj₁ Ω Ω'' Λ I =
    intrp≗ refl
mip≗IL⊗R₂ .(Γ₁ ++ Ω') (E ∷ Δ) .(Ω'' ++ I ∷ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ Ω'')} {Λ₁} {A'} {B'} {f} {g} refl
  | inj₂ (E , .(Δ ++ Ω'') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₂ Ω'' Δ Λ₁ I |
          ++?-inj₁ Ω' Γ₁ (E ∷ Δ ++ Ω'' ++ Λ₁) |
          ++?-inj₁ Ω' Γ₁ (E ∷ Δ ++ Ω'' ++ I ∷ Λ₁) |
          ++?-inj₂ Ω' (Δ ++ Ω'') (I ∷ Λ₁) E |
          cases++-inj₂ Ω'' Δ Λ₁ I =
    intrp≗
      (IL⊗R₂~Λ
        (mip Ω' (E ∷ Δ) (Ω'' ++ Λ₁) g refl)
        f)
