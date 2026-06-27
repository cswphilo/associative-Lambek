{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILTensorLComm1 where

open import IntrpWellDefCases.Base
open import IntrpWellDefCases.ILIL using (mipIL~Γ)


mip≗IL⊗L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B C : Fma}
  {f : Γ₁ ++ Δ₁ ++ A ∷ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Δ₁ ++ A ⊗ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁ ++ A ⊗ B ∷ Λ₁} (⊗L {Γ₁ ++ Δ₁} f)) eq)
      (mip Γ Δ Λ (⊗L {Γ₁ ++ I ∷ Δ₁} (IL {Γ₁} {Δ₁ ++ A ∷ B ∷ Λ₁} f)) eq)
mip≗IL⊗L-comm₁ Γ [] Λ eq = mip[]≗ Γ Λ eq IL⊗L-comm₁
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (I ∷ Δ₁ ++ A ⊗ B ∷ Λ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₁ (eq3 , eq4 , eq5)
  with cases++ Δ₁ Δ Λ₁ Λ eq5
mip≗IL⊗L-comm₁ Γ (I ∷ .(Δ₁ ++ A ⊗ B ∷ Ω')) Λ
  {Γ} {Δ₁} {.(Ω' ++ Λ)} {A} {B} {C} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ Δ₁ (A ⊗ B ∷ Ω' ++ Λ) I |
          cases++-inj₁ Δ₁ Ω' Λ (A ⊗ B) |
          ++?-inj₁ [] Γ (I ∷ Δ₁ ++ A ∷ B ∷ Ω' ++ Λ) =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = []} {Δ₁ = Δ₁ ++ A ⊗ B ∷ Ω'}
          (mip⊗L~Δ Γ Δ₁ Ω' Λ))
        (h~ IL⊗L-comm₁))
mip≗IL⊗L-comm₁ Γ (I ∷ Δ) .(Ω' ++ A ⊗ B ∷ Λ₁)
  {Γ} {.(Δ ++ Ω')} {Λ₁} {A} {B} {C} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ω') (A ⊗ B ∷ Λ₁) I |
          cases++-inj₂ Ω' Δ Λ₁ (A ⊗ B) |
          ++?-inj₁ [] Γ (I ∷ Δ ++ Ω' ++ A ∷ B ∷ Λ₁) =
    intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⊗L~Λ Γ Δ Ω' Λ₁))
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  with cases++ Δ₁ Ω' Λ₁ (E ∷ Δ ++ Λ) (sym eq3)
mip≗IL⊗L-comm₁ .(Γ₁ ++ I ∷ Δ₁ ++ A ⊗ B ∷ Ω'') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω'' ++ E ∷ Δ ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Δ₁ ++ A ⊗ B ∷ Ω'') , refl , refl)
  | inj₂ (.(Δ₁ ++ A ⊗ B ∷ Ω'') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (A ⊗ B ∷ Ω'') (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⊗ B ∷ Ω'') (Γ₁ ++ I ∷ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Δ₁ ++ A ∷ B ∷ Ω'') Γ₁ (E ∷ Δ ++ Λ) =
    intrp≗ (g~ IL⊗L-comm₁)
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  | inj₂ (Ω'' , eq5 , eq6)
  with cases∷ Ω'' eq5
mip≗IL⊗L-comm₁ .(Γ₁ ++ I ∷ Ω') (.(A ⊗ B) ∷ Δ) Λ
  {Γ₁} {Ω'} {.(Δ ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Ω') (A ⊗ B ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ I ∷ Ω') (A ⊗ B ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Ω') Γ₁ (A ∷ B ∷ Δ ++ Λ) =
    intrp≗ refl
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₁ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eq3 , eq4)
  | inj₂ (Ω'' , eq5 , eq6)
  | inj₂ (Ω''' , eq7 , eq8)
  with cases++ Ω''' Δ Λ₁ Λ eq7
mip≗IL⊗L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ .(Ω''' ++ A ⊗ B ∷ Ω'''')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {.(Ω'''' ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(E ∷ Ω''') , refl , refl)
  | inj₂ (Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') Ω''' (A ⊗ B ∷ Ω'''' ++ Λ) E |
          cases++-inj₁ Ω''' Ω'''' Λ (A ⊗ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω') Ω''' (A ⊗ B ∷ Ω'''' ++ Λ) E |
          cases++-inj₁ Ω''' Ω'''' Λ (A ⊗ B) |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Ω''' ++ A ∷ B ∷ Ω'''' ++ Λ) =
    intrp≗ refl
mip≗IL⊗L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) .(Ω'''' ++ A ⊗ B ∷ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ Ω'''')} {Λ₁} {A} {B} {C} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(E ∷ Δ ++ Ω'''') , refl , refl)
  | inj₂ (.(Δ ++ Ω'''') , refl , refl)
  | inj₂ (Ω'''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ Ω'''') (A ⊗ B ∷ Λ₁) E |
          cases++-inj₂ Ω'''' Δ Λ₁ (A ⊗ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω') (Δ ++ Ω'''') (A ⊗ B ∷ Λ₁) E |
          cases++-inj₂ Ω'''' Δ Λ₁ (A ⊗ B) =
    intrp≗
      (~-trans
        (g~ (IL⊗L-comm₁ {Γ = Γ₁} {Δ = Ω' ++ _ ∷ Ω''''} {Λ = Λ₁}))
        (~-sym
          (⊗L~Λ {Λ₀ = Ω''''}
            (mipIL~Γ Γ₁ Ω' (E ∷ Δ) (Ω'''' ++ A ∷ B ∷ Λ₁)))))
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  with cases++ Ω Δ (Δ₁ ++ A ⊗ B ∷ Λ₁) Λ eq3
mip≗IL⊗L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Ω')) Λ
  {.(Γ ++ E ∷ Ω)} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , refl , eq2)
  | refl , eq3
  | inj₁ (Ω' , refl , eq4)
  with cases++ Δ₁ Ω' Λ₁ Λ (sym eq4)
mip≗IL⊗L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Δ₁ ++ A ⊗ B ∷ Ω'')) Λ
  {.(Γ ++ E ∷ Ω)} {Δ₁} {.(Ω'' ++ Λ)} {A} {B} {C} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (.(Δ₁ ++ A ⊗ B ∷ Ω'') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω (Δ₁ ++ A ⊗ B ∷ Ω'') Λ I |
          ++?-inj₂ Γ (Ω ++ I ∷ Δ₁) (A ⊗ B ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Γ (Ω ++ Δ₁) (A ⊗ B ∷ Ω'' ++ Λ) E |
          cases++-inj₁ (Ω ++ I ∷ Δ₁) Ω'' Λ (A ⊗ B) |
          cases++-inj₁ (Ω ++ Δ₁) Ω'' Λ (A ⊗ B) |
          ++?-inj₂ Γ Ω (I ∷ Δ₁ ++ A ∷ B ∷ Ω'' ++ Λ) E |
          cases++-inj₁ Ω (Δ₁ ++ A ∷ B ∷ Ω'') Λ I =
    intrp≗ (h~ IL⊗L-comm₁)
mip≗IL⊗L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Ω')) .(Ω'' ++ A ⊗ B ∷ Λ₁)
  {.(Γ ++ E ∷ Ω)} {.(Ω' ++ Ω'')} {Λ₁} {A} {B} {C} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' (Ω'' ++ A ⊗ B ∷ Λ₁) I |
          ++?-inj₂ Γ (Ω ++ I ∷ Ω' ++ Ω'') (A ⊗ B ∷ Λ₁) E |
          ++?-inj₂ Γ (Ω ++ Ω' ++ Ω'') (A ⊗ B ∷ Λ₁) E |
          cases++-inj₂ Ω'' (Ω ++ I ∷ Ω') Λ₁ (A ⊗ B) |
          cases++-inj₂ Ω'' (Ω ++ Ω') Λ₁ (A ⊗ B) |
          ++?-inj₂ Γ Ω (I ∷ Ω' ++ Ω'' ++ A ∷ B ∷ Λ₁) E |
          cases++-inj₁ Ω Ω' (Ω'' ++ A ∷ B ∷ Λ₁) I = intrp≗ refl
mip≗IL⊗L-comm₁ Γ (E ∷ Δ) .(Ω' ++ I ∷ Δ₁ ++ A ⊗ B ∷ Λ₁)
  {.(Γ ++ E ∷ Δ ++ Ω')} {Δ₁} {Λ₁} {A} {B} {C} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ (Δ₁ ++ A ⊗ B ∷ Λ₁) I |
          ++?-inj₂ Γ (Δ ++ Ω' ++ I ∷ Δ₁) (A ⊗ B ∷ Λ₁) E |
          cases++-inj₂ (Ω' ++ I ∷ Δ₁) Δ Λ₁ (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω' ++ Δ₁) (A ⊗ B ∷ Λ₁) E |
          cases++-inj₂ (Ω' ++ Δ₁) Δ Λ₁ (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω') (I ∷ Δ₁ ++ A ∷ B ∷ Λ₁) E |
          cases++-inj₂ Ω' Δ (Δ₁ ++ A ∷ B ∷ Λ₁) I =
    intrp≗ (g~ (IL⊗L-comm₁ {Γ = Γ ++ _ ∷ Ω'} {Δ = Δ₁} {Λ = Λ₁}))
