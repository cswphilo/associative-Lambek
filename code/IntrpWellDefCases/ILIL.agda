{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILIL where

open import IntrpWellDefCases.Base

mip≗ILIL : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {C : Fma}
  {f : Γ₁ ++ Δ₁ ++ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Δ₁ ++ I ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ I ∷ Δ₁} {Λ₁} (IL {Γ₁} {Δ₁ ++ Λ₁} f)) eq)
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁ ++ I ∷ Λ₁} (IL {Γ₁ ++ Δ₁} {Λ₁} f)) eq)
mip≗ILIL Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} eq with cases++ (Γ₁ ++ I ∷ Δ₁) Γ Λ₁ (Δ ++ Λ) (sym eq)
mip≗ILIL Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} refl | inj₁ (Ω , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₁ ++ I ∷ Ω) (Δ ++ Λ) I |
          cases++-inj₁ (Γ₁ ++ Δ₁) Ω (Δ ++ Λ) I |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω) (Δ ++ Λ) I = intrp≗ (g~ ILIL)
... | inj₂ (Ω , eq1 , eq2) with cases++ Ω Δ Λ₁ Λ eq1
mip≗ILIL Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} eq | inj₂ (Ω , refl , eq2) | inj₁ (Ω' , refl , refl) with cases++ Γ₁ Γ Δ₁ Ω (sym eq2)
mip≗ILIL Γ .(Ω ++ I ∷ Ω') Λ {Γ₁} {Δ₁} {.(Ω' ++ Λ)} refl | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ I |
          cases++-inj₁ Γ₁ Ω'' (Ω ++ Ω' ++ Λ) I |
          cases++-inj₁ Γ₁ Ω'' (Ω ++ I ∷ Ω' ++ Λ) I |
          cases++-inj₂ Ω (Γ₁ ++ Ω'') (Ω' ++ Λ) I |
          cases++-inj₁ Ω Ω' Λ I = intrp≗ refl
mip≗ILIL Γ .(Ω ++ I ∷ Ω') Λ {Γ₁} {Δ₁} {.(Ω' ++ Λ)} refl | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Ω'' ++ I ∷ Δ₁) Ω' Λ I |
          cases++-inj₂ Ω'' Γ (Δ₁ ++ Ω' ++ Λ) I |
          cases++-inj₁ Ω'' (Δ₁ ++ Ω') Λ I |
          cases++-inj₂ Ω'' Γ (Δ₁ ++ I ∷ Ω' ++ Λ) I |
          cases++-inj₁ Ω'' (Δ₁ ++ I ∷ Ω') Λ I |
          cases++-inj₂ (Ω'' ++ Δ₁) Γ (Ω' ++ Λ) I |
          cases++-inj₁ (Ω'' ++ Δ₁) Ω' Λ I = intrp≗ (h~ ILIL)
mip≗ILIL Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} eq | inj₂ (Ω , refl , eq2) | inj₂ (Ω' , refl , refl) with cases++ Γ₁ Γ Δ₁ (Δ ++ Ω') (sym eq2)
mip≗ILIL Γ Δ .(Ω' ++ I ∷ Λ₁) {Γ₁} {Δ₁} {Λ₁} refl | inj₂ (.(Δ ++ Ω') , refl , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Λ₁ I |
          cases++-inj₁ Γ₁ Ω'' (Δ ++ Ω' ++ Λ₁) I |
          cases++-inj₁ Γ₁ Ω'' (Δ ++ Ω' ++ I ∷ Λ₁) I |
          cases++-inj₂ (Δ ++ Ω') (Γ₁ ++ Ω'') Λ₁ I |
          cases++-inj₂ Ω' Δ Λ₁ I = intrp≗ (g~ (ILIL {Γ₁}{Ω'' ++ _ ∷ Ω'}{Λ₁}))
... | inj₂ (Ω'' , eq3 , refl) with cases++ Ω'' Δ Δ₁ Ω' eq3
mip≗ILIL Γ Δ .(Ω' ++ I ∷ Λ₁) {.(Γ ++ Ω'')} {Δ₁} {Λ₁} refl | inj₂ (.(Δ ++ Ω') , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₂ Ω' (Ω'' ++ I ∷ Ω''') Λ₁ I |
          cases++-inj₂ Ω'' Γ (Ω''' ++ Ω' ++ Λ₁) I |
          cases++-inj₁ Ω'' Ω''' (Ω' ++ Λ₁) I |
          cases++-inj₂ Ω'' Γ (Ω''' ++ Ω' ++ I ∷ Λ₁) I |
          cases++-inj₁ Ω'' Ω''' (Ω' ++ I ∷ Λ₁) I |
          cases++-inj₂ (Ω'' ++ Ω''' ++ Ω') Γ Λ₁ I |
          cases++-inj₂ Ω' (Ω'' ++ Ω''') Λ₁ I = intrp≗ refl
mip≗ILIL Γ Δ .(Ω' ++ I ∷ Λ₁) {.(Γ ++ Ω'')} {Δ₁} {Λ₁} refl | inj₂ (.(Δ ++ Ω') , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₂ (Ω''' , refl , refl)
  rewrite cases++-inj₂ (Ω''' ++ I ∷ Δ₁) Δ Λ₁ I |
          cases++-inj₂ (Δ ++ Ω''') Γ (Δ₁ ++ Λ₁) I |
          cases++-inj₂ Ω''' Δ (Δ₁ ++ Λ₁) I |
          cases++-inj₂ (Δ ++ Ω''') Γ (Δ₁ ++ I ∷ Λ₁) I |
          cases++-inj₂ Ω''' Δ (Δ₁ ++ I ∷ Λ₁) I |
          cases++-inj₂ (Δ ++ Ω''' ++ Δ₁) Γ Λ₁ I |
          cases++-inj₂ (Ω''' ++ Δ₁) Δ Λ₁ I = intrp≗ (g~ (ILIL {Γ ++ _ ∷ Ω'''}{Δ₁}{Λ₁}))

