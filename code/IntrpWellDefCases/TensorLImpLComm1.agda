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
... | inj₂ (Ω₀ , eq3 , refl) = {! eq3  !}
... | inj₁ (refl , refl , eq3)
  with cases++ (Λ₁ ++ Δ₁) Δ Ω₁ Λ eq3
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (B' ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ξ ++ Λ) A' | cases++-inj₁ Γ₁ (B' ∷ Λ₁) Δ₁ A' | cases++-inj₁ (Λ₁ ++ Δ₁) Ξ Λ (A ⇒ B)
          | ++?-inj₂ Γ₁ (Λ₁ ++ Δ₁) (A ⇒ B ∷ Ξ ++ Λ) (A' ⊗ B') | cases++-inj₁ Γ₁ Λ₁ Δ₁ (A' ⊗ B') | cases++-inj₁ (Λ₁ ++ Δ₁) Ξ Λ (A ⇒ B)
          | ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ξ ++ Λ) = intrp≗ (h~ (⊗L⇒L-comm₁ {[]}))
... | inj₂ (Ξ , refl , eqb)
  with ++? Δ Λ₁ Ξ Δ₁ eqb
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (Ξ , refl , refl) | inj₁ (Ψ , refl , refl) = {!   !}
mip≗⊗L⇒L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (Ξ , refl , refl) | inj₂ (G , Ψ , refl , refl) = {!   !}
mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq | inj₂ (F , Ω , refl , eq2)
  with cases++ Ω Δ (Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) Λ (inj∷ eq2 .proj₂)
... | inj₁ (Ξ , eqa , eqb) = {!   !}
... | inj₂ (Ξ , eqa , eqb) = {!   !}
