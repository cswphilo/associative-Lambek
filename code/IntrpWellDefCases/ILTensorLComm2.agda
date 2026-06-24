{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILTensorLComm2 where

open import IntrpWellDefCases.Base

mip≗IL⊗L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {A B C : Fma}
  {f : Γ₁ ++ A ∷ B ∷ Δ₁ ++ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ++ I ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ A ⊗ B ∷ Δ₁} {Λ₁} (⊗L f)) eq)
      (mip Γ Δ Λ (⊗L (IL {Γ₁ ++ A ∷ B ∷ Δ₁} {Λ₁} f)) eq)
mip≗IL⊗L-comm₂ Γ [] Λ eq = mip[]≗ Γ Λ eq IL⊗L-comm₂
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  with ++? Γ (Γ₁ ++ A ⊗ B ∷ Δ₁) (E ∷ Δ ++ Λ) (I ∷ Λ₁) eq
... | inj₁ (Ω , eq1 , eq2)
  with cases∷ Ω eq1
mip≗IL⊗L-comm₂ .(Γ₁ ++ A ⊗ B ∷ Δ₁) (I ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Δ ++ Λ)} {A} {B} {C} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ (A ⊗ B ∷ Δ₁) Γ₁ (I ∷ Δ ++ Λ) =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⊗L~Γ Γ₁ Δ₁ Δ Λ))
        (~-sym
          (⊗L~Γ
            (mipIL~Δ (Γ₁ ++ A ∷ B ∷ Δ₁) [] Δ Λ))))
mip≗IL⊗L-comm₂ .(Γ₁ ++ A ⊗ B ∷ Δ₁ ++ I ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A ⊗ B ∷ Δ₁ ++ Ω') Γ₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⊗ B ∷ Δ₁ ++ I ∷ Ω') Γ₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Ω') (Γ₁ ++ A ∷ B ∷ Δ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ (IL⊗L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Ω' ++ _ ∷ Λ}))
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  with cases++ Ω Δ Λ₁ Λ eq3
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₁ (Ω' , eq4 , eq5)
  with cases++ Γ Γ₁ Ω (A ⊗ B ∷ Δ₁) eq1
mip≗IL⊗L-comm₂ Γ (E ∷ .(Ω'' ++ A ⊗ B ∷ Δ₁ ++ I ∷ Ω')) Λ
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {.(Ω' ++ Λ)} {A} {B} {C} refl
  | inj₂ (E , .(Ω'' ++ A ⊗ B ∷ Δ₁) , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Ω'' ++ A ⊗ B ∷ Δ₁) Ω' Λ I |
          ++?-inj₂ Γ Ω'' (A ⊗ B ∷ Δ₁ ++ Ω' ++ Λ) E |
          cases++-inj₁ Ω'' (Δ₁ ++ Ω') Λ (A ⊗ B) |
          ++?-inj₂ Γ Ω'' (A ⊗ B ∷ Δ₁ ++ I ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω'' (Δ₁ ++ I ∷ Ω') Λ (A ⊗ B) |
          ++?-inj₂ Γ (Ω'' ++ A ∷ B ∷ Δ₁) (I ∷ Ω' ++ Λ) E |
          cases++-inj₁ (Ω'' ++ A ∷ B ∷ Δ₁) Ω' Λ I =
    intrp≗ (h~ (IL⊗L-comm₂ {Γ = E ∷ Ω''} {Δ = Δ₁} {Λ = Ω'}))
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₁ (Ω' , eq4 , eq5)
  | inj₂ (Ω'' , eq6 , eq7)
  with cases∷ Ω'' eq6
mip≗IL⊗L-comm₂ Γ (.(A ⊗ B) ∷ .(Δ₁ ++ I ∷ Ω')) Λ
  {Γ} {Δ₁} {.(Ω' ++ Λ)} {A} {B} {C} refl
  | inj₂ (.(A ⊗ B) , Δ₁ , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₁ Δ₁ Ω' Λ I |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ₁ ++ Ω' ++ Λ) |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ₁ ++ I ∷ Ω' ++ Λ) |
          ++?-inj₂ Γ (B ∷ Δ₁) (I ∷ Ω' ++ Λ) A |
          cases++-inj₁ (B ∷ Δ₁) Ω' Λ I =
    intrp≗ (h~ (IL⊗L-comm₂ {Γ = []} {Δ = Δ₁} {Λ = Ω'}))
mip≗IL⊗L-comm₂ .(Γ₁ ++ A ⊗ B ∷ Ω''') (E ∷ .(Ω ++ I ∷ Ω')) Λ
  {Γ₁} {.(Ω''' ++ E ∷ Ω)} {.(Ω' ++ Λ)} {A} {B} {C} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  | inj₂ (.(A ⊗ B ∷ Ω''') , refl , refl)
  | inj₂ (Ω''' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ I |
          ++?-inj₁ (A ⊗ B ∷ Ω''') Γ₁ (E ∷ Ω ++ Ω' ++ Λ) |
          ++?-inj₁ (A ⊗ B ∷ Ω''') Γ₁ (E ∷ Ω ++ I ∷ Ω' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ A ∷ B ∷ Ω''') Ω (I ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω Ω' Λ I =
    intrp≗ refl
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₂ (Ω' , eq4 , eq5)
  with cases++ Γ Γ₁ Ω (A ⊗ B ∷ Δ₁) eq1
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₂ (Ω' , eq4 , eq5)
  | inj₁ (Ω'' , eq6 , eq7)
  with cases++ Ω'' Δ Δ₁ Ω' (trans (sym eq5) eq7)
mip≗IL⊗L-comm₂ Γ (E ∷ .(Ω'' ++ A ⊗ B ∷ Ω''')) .(Ω' ++ I ∷ Λ₁)
  {.(Γ ++ E ∷ Ω'')} {.(Ω''' ++ Ω')} {Λ₁} {A} {B} {C} {f} refl
  | inj₂ (E , .(Ω'' ++ A ⊗ B ∷ Ω''' ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₂ Ω' (Ω'' ++ A ⊗ B ∷ Ω''') Λ₁ I |
          ++?-inj₂ Γ Ω'' (A ⊗ B ∷ Ω''' ++ Ω' ++ Λ₁) E |
          cases++-inj₁ Ω'' Ω''' (Ω' ++ Λ₁) (A ⊗ B) |
          ++?-inj₂ Γ Ω'' (A ⊗ B ∷ Ω''' ++ Ω' ++ I ∷ Λ₁) E |
          cases++-inj₁ Ω'' Ω''' (Ω' ++ I ∷ Λ₁) (A ⊗ B) =
    intrp≗
      (~-sym
        (⊗L~Δ {Δ₀ = E ∷ Ω''} {Δ₁ = Ω'''}
          (mipIL~Λ Γ (E ∷ Ω'' ++ A ∷ B ∷ Ω''') Ω' Λ₁ {f = f})))
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) .(Ω''' ++ A ⊗ B ∷ Δ₁ ++ I ∷ Λ₁)
  {.(Γ ++ E ∷ Δ ++ Ω''')} {Δ₁} {Λ₁} {A} {B} {C} refl
  | inj₂ (E , .(Δ ++ Ω''' ++ A ⊗ B ∷ Δ₁) , refl , refl)
  | refl , refl
  | inj₂ (.(Ω''' ++ A ⊗ B ∷ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ Ω''') , refl , refl)
  | inj₂ (Ω''' , refl , refl)
  rewrite cases++-inj₂ (Ω''' ++ A ⊗ B ∷ Δ₁) Δ Λ₁ I |
          ++?-inj₂ Γ (Δ ++ Ω''') (A ⊗ B ∷ Δ₁ ++ Λ₁) E |
          cases++-inj₂ Ω''' Δ (Δ₁ ++ Λ₁) (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω''') (A ⊗ B ∷ Δ₁ ++ I ∷ Λ₁) E |
          cases++-inj₂ Ω''' Δ (Δ₁ ++ I ∷ Λ₁) (A ⊗ B) |
          ++?-inj₂ Γ (Δ ++ Ω''' ++ A ∷ B ∷ Δ₁) (I ∷ Λ₁) E |
          cases++-inj₂ (Ω''' ++ A ∷ B ∷ Δ₁) Δ Λ₁ I =
    intrp≗ (g~ (IL⊗L-comm₂ {Γ = Γ ++ _ ∷ Ω'''} {Δ = Δ₁} {Λ = Λ₁}))
mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₂ (Ω' , eq4 , eq5)
  | inj₂ (Ω'' , eq6 , eq7)
  with cases∷ Ω'' eq6
mip≗IL⊗L-comm₂ Γ (.(A ⊗ B) ∷ Δ) .(Ω' ++ I ∷ Λ₁)
  {Γ} {.(Δ ++ Ω')} {Λ₁} {A} {B} {C} refl
  | inj₂ (.(A ⊗ B) , .(Δ ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Λ₁ I |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ ++ Ω' ++ Λ₁) |
          ++?-inj₁ [] Γ (A ⊗ B ∷ Δ ++ Ω' ++ I ∷ Λ₁) |
          ++?-inj₂ Γ (B ∷ Δ ++ Ω') (I ∷ Λ₁) A |
          cases++-inj₂ Ω' (B ∷ Δ) Λ₁ I =
    intrp≗ refl
mip≗IL⊗L-comm₂ .(Γ₁ ++ A ⊗ B ∷ Ω''') (E ∷ Δ) .(Ω' ++ I ∷ Λ₁)
  {Γ₁} {.(Ω''' ++ E ∷ Δ ++ Ω')} {Λ₁} {A} {B} {C} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | refl , refl
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(A ⊗ B ∷ Ω''') , refl , refl)
  | inj₂ (Ω''' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Λ₁ I |
          ++?-inj₁ (A ⊗ B ∷ Ω''') Γ₁ (E ∷ Δ ++ Ω' ++ Λ₁) |
          ++?-inj₁ (A ⊗ B ∷ Ω''') Γ₁ (E ∷ Δ ++ Ω' ++ I ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ A ∷ B ∷ Ω''') (Δ ++ Ω') (I ∷ Λ₁) E |
          cases++-inj₂ Ω' Δ Λ₁ I =
    intrp≗ (g~ (IL⊗L-comm₂ {Γ = Γ₁} {Δ = Ω''' ++ _ ∷ Ω'} {Λ = Λ₁}))
