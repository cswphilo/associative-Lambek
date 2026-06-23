{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILIL where

open import Data.Sum
open import IntrpWellDefCases.Base

-- mip commutes with an IL whose I lands in the first (Γ) interpolation block:
-- interpolating IL {Γ₀} f is the same (up to ~) as IL~Γ'-transporting the
-- interpolation of f.  The buried difference is exactly one ILIL permutation.
mipIL~Γ : ∀ Γ₀ Γ₁ Δ Λ {C} {f : Γ₀ ++ Γ₁ ++ Δ ++ Λ ⊢ C}
  → mip (Γ₀ ++ I ∷ Γ₁) Δ Λ (IL {Γ₀} {Γ₁ ++ Δ ++ Λ} f) refl
      ~ IL~Γ' {Γ₀} {Γ₁} {Δ} {Λ} (mip (Γ₀ ++ Γ₁) Δ Λ f refl)
mipIL~Γ Γ₀ Γ₁ [] Λ = g~ ILIL
mipIL~Γ Γ₀ Γ₁ (A ∷ Δ) Λ 
  rewrite ++?-inj₁ (I ∷ Γ₁) Γ₀ (A ∷ Δ ++ Λ) = refl

mip≗ILIL : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ : Cxt} {C : Fma}
  {f : Γ₁ ++ Δ₁ ++ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Δ₁ ++ I ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ I ∷ Δ₁} {Λ₁} (IL {Γ₁} {Δ₁ ++ Λ₁} f)) eq)
      (mip Γ Δ Λ (IL {Γ₁} {Δ₁ ++ I ∷ Λ₁} (IL {Γ₁ ++ Δ₁} {Λ₁} f)) eq)
mip≗ILIL Γ [] Λ {Γ₁} {Δ₁} {Λ₁} eq 
  with ++? Γ Γ₁ Λ (I ∷ Δ₁ ++ I ∷ Λ₁) eq
mip≗ILIL Γ [] Λ {Γ₁} {Δ₁} {Λ₁} refl | inj₁ ([] , refl , refl) = intrp≗ (g~ (IL ILIL))
... | inj₁ (E ∷ Ω , eq1 , refl)
  with cases++ Δ₁ Ω Λ₁ Λ (sym (inj∷ eq1 .proj₂))
mip≗ILIL ._ [] Λ {Γ₁} {Δ₁} {Λ₁} refl | inj₁ (E ∷ Ω , refl , refl) | inj₁ (Ω' , refl , refl) = intrp≗ (g~ (IL {Γ₁ ++ I ∷ Δ₁ ++ I ∷ Ω'} ILIL))
mip≗ILIL ._ [] Λ {Γ₁} {Δ₁} {Λ₁} refl | inj₁ (E ∷ Ω , refl , refl) | inj₂ (Ω' , refl , refl) = intrp≗ (g~ (IL {_ ++ I ∷ _} (ILIL {Γ₁} {Ω ++ Ω'})))
mip≗ILIL Γ [] Λ {Γ₁} {Δ₁} {Λ₁} refl | inj₂ (E , Ω , refl , refl) = intrp≗ (g~ (IL (ILIL {_ ++ _ ∷ _})))
mip≗ILIL Γ (A ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} eq 
  with ++? Γ Γ₁ (A ∷ Δ ++ Λ) (I ∷ Δ₁ ++ I ∷ Λ₁) eq
... | inj₁ ([] , eq1 , refl)
  with inj∷ eq1
... | refl , eq2
  with cases++ Δ₁ Δ Λ₁ Λ (sym eq2)
mip≗ILIL Γ (I ∷ .(I ∷ Ω')) Λ {.(Γ)} {[]} {.(Ω' ++ Λ)} refl
  | inj₁ ([] , refl , refl) | refl , refl | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ [] (I ∷ Ω' ++ Λ) I |
          cases++-inj₁ [] Ω' Λ I |
          ++?-inj₁ [] Γ (I ∷ Ω' ++ Λ) =
    intrp≗ (h~ ILIL)
mip≗ILIL Γ (I ∷ .((B ∷ Θ) ++ I ∷ Ω')) Λ {.(Γ)} {B ∷ Θ} {.(Ω' ++ Λ)} refl
  | inj₁ ([] , refl , refl) | refl , refl | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (B ∷ Θ) (I ∷ Ω' ++ Λ) I |
          cases++-inj₁ (B ∷ Θ) Ω' Λ I |
          ++?-inj₁ [] Γ (I ∷ B ∷ Θ ++ Ω' ++ Λ) |
          ++?-inj₂ Γ Θ (I ∷ Ω' ++ Λ) B |
          cases++-inj₁ Θ Ω' Λ I =
    intrp≗ (h~ ILIL)
mip≗ILIL Γ (I ∷ []) .(Ω' ++ I ∷ Λ₁) {.(Γ)} {Ω'} {Λ₁} refl
  | inj₁ ([] , refl , refl) | refl , refl | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ Ω' (I ∷ Λ₁) I |
          cases++-inj₂ Ω' [] Λ₁ I |
          ++?-inj₁ [] Γ (I ∷ Ω' ++ Λ₁) =
    intrp≗ (g~ ILIL)
mip≗ILIL Γ (I ∷ B ∷ Θ) .(Ω' ++ I ∷ Λ₁) {.(Γ)} {.(B ∷ Θ ++ Ω')} {Λ₁} refl
  | inj₁ ([] , refl , refl) | refl , refl | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (B ∷ Θ ++ Ω') (I ∷ Λ₁) I |
          cases++-inj₂ Ω' (B ∷ Θ) Λ₁ I |
          ++?-inj₁ [] Γ (I ∷ B ∷ Θ ++ Ω' ++ Λ₁) |
          ++?-inj₂ Γ (Θ ++ Ω') (I ∷ Λ₁) B |
          cases++-inj₂ Ω' Θ Λ₁ I =
    intrp≗ refl
mip≗ILIL Γ (A ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} eq
  | inj₁ (E ∷ Ω , eq1 , refl)
  with inj∷ eq1
... | refl , eq2
  with cases++ Δ₁ Ω Λ₁ (A ∷ Δ ++ Λ) (sym eq2)
mip≗ILIL .(Γ₁ ++ (I ∷ (Δ₁ ++ (I ∷ Ω')))) (A ∷ Δ) Λ {Γ₁} {Δ₁} {.(Ω' ++ A ∷ Δ ++ Λ)} refl
  | inj₁ (Ω₀ , refl , refl) | refl , refl | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₁ (I ∷ Ω') (Γ₁ ++ I ∷ Δ₁) (A ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Δ₁ ++ Ω') Γ₁ (A ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Ω') (Γ₁ ++ Δ₁) (A ∷ Δ ++ Λ) =
    intrp≗ (g~ ILIL)
... | inj₂ (Ω' , eq3 , refl)
  with cases++ Ω' (A ∷ Δ) Λ₁ Λ eq3
... | inj₁ (Ω'' , eq4 , refl)
  with cases∷ Ω' eq4
mip≗ILIL .(Γ₁ ++ I ∷ Ω) (A ∷ Δ) Λ {Γ₁} {.(Ω ++ Ω')} {.(Ω'' ++ Λ)} refl | inj₁ (.I ∷ Ω , refl , refl) | refl , eq2 | inj₂ (Ω' , eq3 , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ I ∷ Ω) (I ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Ω) (I ∷ Δ ++ Λ) = intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mipIL~Γ Γ₁ Ω Δ Λ))
mip≗ILIL .(Γ₁ ++ I ∷ Ω) (A ∷ Δ) Λ {Γ₁} {.(Ω ++ Ω')} {.(Ω'' ++ Λ)} refl | inj₁ (.I ∷ Ω , refl , refl) | refl , eq2 | inj₂ (Ω' , eq3 , refl) | inj₁ (Ω'' , eq4 , refl) | inj₂ (Ω''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ I ∷ Ω) Ω''' (I ∷ Ω'' ++ Λ) A |
          ++?-inj₂ (Γ₁ ++ Ω) Ω''' (I ∷ Ω'' ++ Λ) A |
          cases++-inj₁ Ω''' Ω'' Λ I |
          ++?-inj₁ (I ∷ Ω) Γ₁ (A ∷ Ω''' ++ Ω'' ++ Λ) =
           intrp≗ refl

mip≗ILIL .(Γ₁ ++ I ∷ Ω) (A ∷ Δ) .(Ω'' ++ I ∷ Λ₁) {Γ₁} {.(Ω ++ A ∷ Δ ++ Ω'')} {Λ₁} refl
  | inj₁ (I ∷ Ω , refl , refl) | refl , refl | inj₂ (Ω₀ , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ I ∷ Ω) (Δ ++ Ω'') (I ∷ Λ₁) A |
          cases++-inj₂ Ω'' Δ Λ₁ I |
          ++?-inj₁ (I ∷ Ω) Γ₁ (A ∷ Δ ++ Ω'' ++ Λ₁) |
          ++?-inj₂ (Γ₁ ++ Ω) (Δ ++ Ω'') (I ∷ Λ₁) A |
          cases++-inj₂ Ω'' Δ Λ₁ I =
    intrp≗ (g~ (ILIL {Γ = Γ₁} {Δ = Ω ++ _ ∷ Ω''} {Λ = Λ₁}))
mip≗ILIL Γ (A ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} eq
  | inj₂ (E , Ω , refl , eq2) 
  with ++? Ω Δ (I ∷ Δ₁ ++ I ∷ Λ₁) Λ (inj∷ eq2 .proj₂)
mip≗ILIL Γ (A ∷ Δ) .(Ω' ++ I ∷ Δ₁ ++ I ∷ Λ₁) {.(Γ ++ A ∷ Δ ++ Ω')} {Δ₁} {Λ₁} refl
  | inj₂ (A , Ω₀ , refl , refl) | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ω' ++ I ∷ Δ₁) (I ∷ Λ₁) A |
          cases++-inj₂ (Ω' ++ I ∷ Δ₁) Δ Λ₁ I |
          cases++-inj₂ Ω' Δ (Δ₁ ++ I ∷ Λ₁) I |
          ++?-inj₂ Γ (Δ ++ Ω') (I ∷ Δ₁ ++ Λ₁) A |
          cases++-inj₂ Ω' Δ (Δ₁ ++ Λ₁) I |
          ++?-inj₂ Γ (Δ ++ Ω' ++ Δ₁) (I ∷ Λ₁) A |
          cases++-inj₂ (Ω' ++ Δ₁) Δ Λ₁ I =
    intrp≗ (g~ (ILIL {Γ = Γ ++ _ ∷ Ω'} {Δ = Δ₁} {Λ = Λ₁}))
... | inj₂ (E' , Ω' , refl , eq4) 
  with cases++ Δ₁ Ω' Λ₁ Λ (sym (inj∷ eq4 .proj₂))
mip≗ILIL Γ (A ∷ .(Ω ++ I ∷ Δ₁ ++ I ∷ Ω'')) Λ {.(Γ ++ A ∷ Ω)} {Δ₁} {.(Ω'' ++ Λ)} refl
  | inj₂ (A , Ω , refl , refl) | inj₂ (I , Ω₀ , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω ++ I ∷ Δ₁) (I ∷ Ω'' ++ Λ) A |
          cases++-inj₁ (Ω ++ I ∷ Δ₁) Ω'' Λ I |
          cases++-inj₁ Ω (Δ₁ ++ I ∷ Ω'') Λ I |
          ++?-inj₂ Γ Ω (I ∷ Δ₁ ++ Ω'' ++ Λ) A |
          cases++-inj₁ Ω (Δ₁ ++ Ω'') Λ I |
          ++?-inj₂ Γ (Ω ++ Δ₁) (I ∷ Ω'' ++ Λ) A |
          cases++-inj₁ (Ω ++ Δ₁) Ω'' Λ I =
    intrp≗ (h~ (ILIL {Γ = A ∷ Ω} {Δ = Δ₁} {Λ = Ω''}))
mip≗ILIL Γ (A ∷ .(Ω ++ E' ∷ Ω')) Λ {.(Γ ++ E ∷ Ω)} {Δ₁} {Λ₁} refl | inj₂ (E , Ω , refl , refl) | inj₂ (E' , Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) 
  rewrite cases++-inj₁ Ω Ω' (Ω'' ++ I ∷ Λ₁) I |
          ++?-inj₂ Γ (Ω ++ Ω' ++ Ω'') (I ∷ Λ₁) A |
          cases++-inj₂ Ω'' (Ω ++ Ω') Λ₁ I |
          ++?-inj₂ Γ (Ω ++ I ∷ Ω' ++ Ω'') (I ∷ Λ₁) A |
          cases++-inj₂ Ω'' (Ω ++ I ∷ Ω') Λ₁ I |
          ++?-inj₂ Γ Ω (I ∷ Ω' ++ Ω'' ++ Λ₁) A |
          cases++-inj₁ Ω Ω' (Ω'' ++ Λ₁) I = intrp≗ refl
