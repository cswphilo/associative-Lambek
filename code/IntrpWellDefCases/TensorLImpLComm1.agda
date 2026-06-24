{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLImpLComm1 where

open import IntrpWellDefCases.Base


mip≗⊗L⇒L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ B ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L (⇒L {Γ₁ ++ A' ∷ B' ∷ Λ₁} f g)) eq)
      (mip Γ Δ Λ (⇒L {Γ₁ ++ A' ⊗ B' ∷ Λ₁} f (⊗L g)) eq)
mip≗⊗L⇒L-comm₁ Γ [] Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  with cases++ Γ₁ Γ (Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) Λ (sym eq)
... | inj₁ (Ω , refl , eq2)
  with cases++ (Λ₁ ++ Δ₁) Ω Ω₁ Λ (sym eq2)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω) [] Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (Ω , refl , eq2) | inj₁ (Ξ , refl , refl) = intrp≗ (g~ (IL {Γ₁ ++ A' ⊗ B' ∷ Ω} ⊗L⇒L-comm₁))
... | inj₂ (Ξ , refl , eqb)
  with ++? Ω Λ₁ Ξ Δ₁ eqb
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω) [] .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (Ω , refl , eq2) | inj₂ (Ξ , refl , eqb) | inj₁ (Ψ , refl , refl) = intrp≗ (g~ (IL {Γ₁ ++ A' ⊗ B' ∷ Ω} ⊗L⇒L-comm₁))
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω) [] .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (Ω , refl , eq2) | inj₂ (Ξ , refl , eqb) | inj₂ (F , Ψ , refl , refl) = intrp≗ (g~ (IL {Γ₁ ++ A' ⊗ B' ∷ Ω} ⊗L⇒L-comm₁))
mip≗⊗L⇒L-comm₁ Γ [] Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₂ (Ω , refl , refl) = intrp≗ (g~ (IL (⊗L⇒L-comm₁ {Γ ++ Ω})))
mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (A' ⊗ B' ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) eq
... | inj₁ (Ω , eq1 , refl)
  with cases∷ Ω eq1
... | inj₂ (Ω₀ , eq3 , refl)
  with cases++ (Λ₁ ++ Δ₁) Ω₀ Ω₁ (E ∷ Δ ++ Λ) (sym eq3)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ξ) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {.(Ξ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ξ) , refl , refl) | inj₂ (.(Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ξ) , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₁ (A ⇒ B ∷ Ξ) (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ξ) (Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ξ) Γ₁ (E ∷ Δ ++ Λ) = intrp≗ (g~ ⊗L⇒L-comm₁)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl) | inj₂ (Ξ , eqa , eqb)
  with cases∷ Ξ eqa
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) (.(A ⇒ B) ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ Δ₁) , refl , refl) | inj₂ (.(Λ₁ ++ Δ₁) , refl , refl) | inj₂ (.[] , refl , refl) | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ (A' ⊗ B' ∷ Λ₁) Γ₁ (B ∷ Δ ++ Λ) = intrp≗ (g~ ⊗L⇒L-comm₁)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl) | inj₂ (.(E ∷ Ξ) , eqa , eqb) | inj₂ (Ξ , eq4 , refl)
  with ++? Ω₀ Λ₁ (E ∷ Ξ) Δ₁ eqb
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl) | inj₂ (.(E ∷ Ξ) , eqa , eqb) | inj₂ (Ξ , eq4 , refl) | inj₁ (Ψ , refl , refl)
  with ++? Δ Ξ Λ (A ⇒ B ∷ Ω₁) (sym eq4)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Ψ) (E ∷ Ξ) .(A ⇒ B ∷ Ω₁) {Γ₁} {.(Ψ ++ E ∷ Ξ)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ Ψ) , refl , refl) | inj₂ (.(Λ₁ ++ Ψ) , refl , refl) | inj₂ (.(E ∷ Ξ) , refl , refl) | inj₂ (Ξ , refl , refl) | inj₁ (Ψ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ Ψ) Ξ (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ A' ∷ B' ∷ Λ₁) Ξ E |
          cases++-inj₂ [] Ξ Ω₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Ψ) Ξ (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Ξ E |
          cases++-inj₂ [] Ξ Ω₁ (A ⇒ B) = intrp≗ (g~ ⊗L⇒L-comm₁)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Ψ) (E ∷ .(Ξ ++ A ⇒ B ∷ Ω'')) Λ {Γ₁} {.(Ψ ++ E ∷ Ξ)} {Λ₁} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ Ψ) , refl , refl) | inj₂ (.(Λ₁ ++ Ψ) , refl , refl) | inj₂ (.(E ∷ Ξ) , refl , refl) | inj₂ (Ξ , refl , refl) | inj₁ (Ψ , refl , refl) | inj₁ (.(A ⇒ B) ∷ Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ Ψ) Ξ (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ Ψ (Γ₁ ++ A' ∷ B' ∷ Λ₁) Ξ E |
          cases++-inj₁ Ξ Ω'' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Ψ) Ξ (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ Ψ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Ξ E |
          cases++-inj₁ Ξ Ω'' Λ (A ⇒ B) |
          ++?-inj₁ (A' ⊗ B' ∷ Λ₁) Γ₁ (B ∷ Ω'' ++ Λ) = intrp≗ (g~ ⊗L⇒L-comm₁)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Ψ) (E ∷ Δ) Λ {Γ₁} {.(Ψ ++ E ∷ Ξ)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ Ψ) , refl , refl) | inj₂ (.(Λ₁ ++ Ψ) , refl , refl) | inj₂ (.(E ∷ Ξ) , refl , refl) | inj₂ (Ξ , refl , refl) | inj₁ (Ψ , refl , refl) | inj₂ (G , Ω' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ Ψ) (Δ ++ G ∷ Ω') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Δ ++ G ∷ Ω') E |
          cases++-inj₂ (G ∷ Ω') Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ Ψ) (Δ ++ G ∷ Ω') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Δ ++ G ∷ Ω') E |
          cases++-inj₂ (G ∷ Ω') Δ Ω₁ (A ⇒ B) = intrp≗ (g~ ⊗L⇒L-comm₁)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl) | inj₂ (.(E ∷ Ξ) , eqa , eqb) | inj₂ (Ξ , eq4 , refl) | inj₂ (G , Ψ , refl , refl)
  with ++? Δ Ψ Λ (Δ₁ ++ A ⇒ B ∷ Ω₁) (sym eq4)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Ψ)} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl) | inj₂ (.(E ∷ Ψ ++ Δ₁) , eqa , eqb) | inj₂ (.(Ψ ++ Δ₁) , eq4 , refl) | inj₂ (E , Ψ , refl , refl) | inj₁ (Ω'' , eq5 , refl)
  with ++? Δ₁ Ω'' (A ⇒ B ∷ Ω₁) Λ (sym eq5)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ .(Ψ ++ Ω'')) Λ {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Ψ)} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Ω₀) , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (.(E ∷ Ψ ++ Δ₁) , refl , refl) | inj₂ (.(Ψ ++ Δ₁) , refl , refl) | inj₂ (E , Ψ , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ Ω₀) (Ψ ++ Ω'' ++ Ω''') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Ω₀) Ψ (Ω'' ++ Ω''') E |
          cases++-inj₂ Ω''' (Ψ ++ Ω'') Ω₁ (A ⇒ B) |
          ++?-inj₁ Ω'' Ψ Ω''' |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ Ω₀) (Ψ ++ Ω'' ++ Ω''') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Ω₀) Ψ (Ω'' ++ Ω''') E |
          cases++-inj₂ Ω''' (Ψ ++ Ω'') Ω₁ (A ⇒ B) |
          ++?-inj₁ Ω'' Ψ Ω''' |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₀) Γ₁ (E ∷ Ψ ++ B ∷ Ω₁)
            = intrp≗ (g~ ((~ ⊗L⊗L) ∘
                ⊗L {Γ = Γ₁ ++ A' ⊗ B' ∷ Ω₀} ⊗L⇒L-comm₁))
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ .(Ψ ++ Δ₁ ++ A ⇒ B ∷ Ω''')) Λ {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Ψ)} {.(Ω''' ++ Λ)} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Ω₀) , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (.(E ∷ Ψ ++ Δ₁) , refl , refl) | inj₂ (.(Ψ ++ Δ₁) , refl , refl) | inj₂ (E , Ψ , refl , refl) | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω''') , refl , refl) | inj₂ (.(A ⇒ B) , Ω''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ Ω₀) (Ψ ++ Δ₁) (A ⇒ B ∷ Ω''' ++ Λ) E |
          cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Ω₀) Ψ Δ₁ E |
          cases++-inj₁ (Ψ ++ Δ₁) Ω''' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ Ω₀) (Ψ ++ Δ₁) (A ⇒ B ∷ Ω''' ++ Λ) E |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Ω₀) Ψ Δ₁ E |
          cases++-inj₁ (Ψ ++ Δ₁) Ω''' Λ (A ⇒ B) |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₀) Γ₁ (E ∷ Ψ ++ B ∷ Ω''' ++ Λ) = intrp≗ refl
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) .(F ∷ Ω'' ++ Δ₁ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Δ ++ F ∷ Ω'')} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.(A' ⊗ B' ∷ Ω₀) , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (.(E ∷ Δ ++ F ∷ Ω'' ++ Δ₁) , refl , refl) | inj₂ (.(Δ ++ F ∷ Ω'' ++ Δ₁) , refl , refl) | inj₂ (E , .(Δ ++ F ∷ Ω'') , refl , refl) | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ Ω₀) (Δ ++ F ∷ Ω'' ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Ω₀) (Δ ++ F ∷ Ω'') Δ₁ E |
          cases++-inj₂ (F ∷ Ω'' ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω'' Δ₁ F |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ Ω₀) (Δ ++ F ∷ Ω'' ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Ω₀) (Δ ++ F ∷ Ω'') Δ₁ E |
          cases++-inj₂ (F ∷ Ω'' ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω'' Δ₁ F |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₀) Γ₁ (E ∷ Δ ++ F ∷ Ω'' ++ B ∷ Ω₁) = intrp≗ (g~ ⊗L⇒L-comm₁)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₁ (.[] , eq1 , refl) | inj₁ (refl , refl , eq3)
  with cases++ (Λ₁ ++ Δ₁) Δ Ω₁ Λ eq3
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ξ ++ Λ) A' | cases++-inj₁ Γ₁ (B' ∷ Λ₁) Δ₁ A' | cases++-inj₁ (Λ₁ ++ Δ₁) Ξ Λ (A ⇒ B)
          | ++?-inj₂ Γ₁ (Λ₁ ++ Δ₁) (A ⇒ B ∷ Ξ ++ Λ) (A' ⊗ B') | cases++-inj₁ Γ₁ Λ₁ Δ₁ (A' ⊗ B') | cases++-inj₁ (Λ₁ ++ Δ₁) Ξ Λ (A ⇒ B)
          | ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ξ ++ Λ) = intrp≗ (h~ (⊗L⇒L-comm₁ {[]}))
... | inj₂ (Ξ , refl , eqb)
  with ++? Δ Λ₁ Ξ Δ₁ eqb
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (Ξ , refl , refl) | inj₁ (Ψ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (B' ∷ Λ₁ ++ Ψ ++ Ξ) (A ⇒ B ∷ Ω₁) A' |
          cases++-inj₁ Γ₁ (B' ∷ Λ₁) (Ψ ++ Ξ) A' |
          cases++-inj₂ Ξ (Λ₁ ++ Ψ) Ω₁ (A ⇒ B) |
          ++?-inj₁ Ψ Λ₁ Ξ |
          ++?-inj₂ Γ₁ (Λ₁ ++ Ψ ++ Ξ) (A ⇒ B ∷ Ω₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ Λ₁ (Ψ ++ Ξ) (A' ⊗ B') |
          cases++-inj₂ Ξ (Λ₁ ++ Ψ) Ω₁ (A ⇒ B) |
          ++?-inj₁ Ψ Λ₁ Ξ |
          ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) = intrp≗ (h~ ⊗L⊗R₁)
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (Ξ , refl , refl) | inj₂ (G , Ψ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (B' ∷ Δ ++ G ∷ Ψ ++ Δ₁) (A ⇒ B ∷ Ω₁) A' |
          cases++-inj₁ Γ₁ (B' ∷ Δ ++ G ∷ Ψ) Δ₁ A' |
          cases++-inj₂ (G ∷ Ψ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Ψ Δ₁ G |
          ++?-inj₂ Γ₁ (Δ ++ G ∷ Ψ ++ Δ₁) (A ⇒ B ∷ Ω₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Δ ++ G ∷ Ψ) Δ₁ (A' ⊗ B') |
          cases++-inj₂ (G ∷ Ψ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Ψ Δ₁ G |
          ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Δ ++ G ∷ Ψ ++ B ∷ Ω₁) = intrp≗ refl
mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₂ (F , Ω , refl , eq2)
  with cases++ Ω Δ (Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) Λ (inj∷ eq2 .proj₂)
... | inj₁ (Ξ , eqa , eqb)
  with ++? Ξ Λ₁ Λ (Δ₁ ++ A ⇒ B ∷ Ω₁) eqb
... | inj₁ (Ψ , eqc , refl)
  with ++? Δ₁ Ψ (A ⇒ B ∷ Ω₁) Λ (sym eqc)
mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₂ (F , Ω , refl , refl) | inj₁ (Ξ , refl , refl) | inj₁ (Ψ , eqc , refl) | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω ++ A' ∷ B' ∷ Λ₁ ++ Ψ ++ Ω') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Ω ++ A' ∷ B' ∷ Λ₁) (Ψ ++ Ω') E |
          cases++-inj₂ Ω' (Ω ++ A' ∷ B' ∷ Λ₁ ++ Ψ) Ω₁ (A ⇒ B) |
          ++?-inj₁ Ψ (Ω ++ A' ∷ B' ∷ Λ₁) Ω' |
          ++?-inj₂ Γ (Ω ++ A' ⊗ B' ∷ Λ₁ ++ Ψ ++ Ω') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Ω ++ A' ⊗ B' ∷ Λ₁) (Ψ ++ Ω') E |
          cases++-inj₂ Ω' (Ω ++ A' ⊗ B' ∷ Λ₁ ++ Ψ) Ω₁ (A ⇒ B) |
          ++?-inj₁ Ψ (Ω ++ A' ⊗ B' ∷ Λ₁) Ω' |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Λ₁ (B ∷ Ω₁) (A' ⊗ B') = intrp≗ (h~ ⊗L⊗R₁)
mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₂ (F , Ω , refl , refl) | inj₁ (Ξ , refl , refl) | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω') , refl , refl) | inj₂ (.(A ⇒ B) , Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω ++ A' ∷ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω' ++ Λ) E |
          cases++-inj₁ Γ (Ω ++ A' ∷ B' ∷ Λ₁) Δ₁ E |
          cases++-inj₁ (Ω ++ A' ∷ B' ∷ Λ₁ ++ Δ₁) Ω' Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ω ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω' ++ Λ) E |
          cases++-inj₁ Γ (Ω ++ A' ⊗ B' ∷ Λ₁) Δ₁ E |
          cases++-inj₁ (Ω ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) Ω' Λ (A ⇒ B) |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω (Λ₁ ++ B ∷ Ω') Λ (A' ⊗ B') = intrp≗ (h~ ⊗L⇒L-comm₁)
mip≗⊗L⇒L-comm₁ Γ (E ∷ .(Ω ++ A' ⊗ B' ∷ Ξ)) .(G ∷ Ψ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) {.(Γ ++ E ∷ Ω)} {Δ₁} {.(Ξ ++ G ∷ Ψ)} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (E , Ω , refl , refl) | inj₁ (Ξ , refl , refl) | inj₂ (G , Ψ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω ++ A' ∷ B' ∷ Ξ ++ G ∷ Ψ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Ω ++ A' ∷ B' ∷ Ξ ++ G ∷ Ψ) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ Δ₁) (Ω ++ A' ∷ B' ∷ Ξ) Ω₁ (A ⇒ B) |
          ++?-inj₂ (Ω ++ A' ∷ B' ∷ Ξ) Ψ Δ₁ G |
          ++?-inj₂ Γ (Ω ++ A' ⊗ B' ∷ Ξ ++ G ∷ Ψ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Ω ++ A' ⊗ B' ∷ Ξ ++ G ∷ Ψ) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ Δ₁) (Ω ++ A' ⊗ B' ∷ Ξ) Ω₁ (A ⇒ B) |
          ++?-inj₂ (Ω ++ A' ⊗ B' ∷ Ξ) Ψ Δ₁ G |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Ξ ++ G ∷ Ψ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Ξ (G ∷ Ψ ++ B ∷ Ω₁) (A' ⊗ B') = intrp≗ refl
mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) .(A' ⊗ B' ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) {.(Γ ++ E ∷ Δ ++ [])} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ []) , refl , refl) | inj₂ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ A' ∷ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ A' ∷ B' ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (A' ∷ B' ∷ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ (B' ∷ Λ₁) Δ₁ A' |
          ++?-inj₂ Γ (Δ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ A' ⊗ B' ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (A' ⊗ B' ∷ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Λ₁ Δ₁ (A' ⊗ B') |
          ++?-inj₂ Γ Δ (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₂ [] Δ (Λ₁ ++ B ∷ Ω₁) (A' ⊗ B')
            = intrp≗
                (~-trans
                  (g~ (⊗L⇒L-comm₁ {Γ = Γ ++ _ ∷ []} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁}))
                  (⇒L~Λ {Γ = Γ} {Λ₀ = A' ⊗ B' ∷ Λ₁} refl refl))
mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) .(G ∷ Ψ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) {.(Γ ++ E ∷ Δ ++ G ∷ Ψ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ G ∷ Ψ) , refl , refl) | inj₂ (G ∷ Ψ , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ G ∷ Ψ ++ A' ∷ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ψ ++ A' ∷ B' ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ A' ∷ B' ∷ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ (Ψ ++ A' ∷ B' ∷ Λ₁) Δ₁ G |
          ++?-inj₂ Γ (Δ ++ G ∷ Ψ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ψ ++ A' ⊗ B' ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ A' ⊗ B' ∷ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ (Ψ ++ A' ⊗ B' ∷ Λ₁) Δ₁ G |
          ++?-inj₂ Γ (Δ ++ G ∷ Ψ) (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₂ (G ∷ Ψ) Δ (Λ₁ ++ B ∷ Ω₁) (A' ⊗ B') =
            intrp≗ (g~ (⊗L⇒L-comm₁ {Γ = Γ ++ _ ∷ G ∷ Ψ} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁}))
