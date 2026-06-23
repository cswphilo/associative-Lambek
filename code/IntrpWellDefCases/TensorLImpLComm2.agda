{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLImpLComm2 where

open import IntrpWellDefCases.Base
open import IntrpWellDefCases.ILImpLAssoc using (mip⇒L~⇒; mip⇒L~Δ; mip⇒L~ΔΓ)
open import IntrpWellDefCases.TensorLImpLAssoc using (mip⊗L~Δ; mip⊗L~Λ)

mip≗⊗L⇒L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L f (⊗L {Γ₁ ++ B ∷ Λ₁} g)) eq)
mip≗⊗L⇒L-comm₂ Γ [] Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  with cases++ (Γ₁ ++ Δ₁) Γ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) Λ (sym eq)
... | inj₁ (Ω , refl , eq2)
  with cases++ Λ₁ Ω Ω₁ Λ (sym eq2)
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) [] Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Ω , refl , eq2) | inj₁ (Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ = Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ} {Δ = Λ}
      (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ξ ++ Λ})))
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) [] .(Ξ ++ A' ⊗ B' ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Ω , refl , eq2) | inj₂ (Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ = Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω} {Δ = Ξ ++ A' ⊗ B' ∷ Ω₁}
      (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Ω ++ Ξ} {Ω = Ω₁})))
mip≗⊗L⇒L-comm₂ Γ [] Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (Ω , refl , eqΓ)
  with ++? Γ Γ₁ Ω Δ₁ eqΓ
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Ξ) [] .(Ω ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁) {Γ₁} {.(Ξ ++ Ω)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ = Γ₁ ++ Ξ} {Δ = Ω ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁}
      (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Ξ ++ Ω} {Λ = Λ₁} {Ω = Ω₁})))
mip≗⊗L⇒L-comm₂ Γ [] .(F ∷ Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁) {.(Γ ++ F ∷ Ξ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (.(F ∷ Ξ ++ Δ₁) , refl , refl) | inj₂ (F , Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ = Γ} {Δ = F ∷ Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁}
      (⊗L⇒L-comm₂ {Γ = Γ ++ F ∷ Ξ} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁})))
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  with cases++ (Γ₁ ++ Δ₁) Γ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) (E ∷ Δ ++ Λ) (sym eq)
... | inj₁ (Ω , refl , eq2)
  with cases++ Λ₁ Ω Ω₁ (E ∷ Δ ++ Λ) (sym eq2)
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ) (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ξ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Λ₁ ++ A' ⊗ B' ∷ Ξ) , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Ξ) (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁ ++ A' ∷ B' ∷ Ξ) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A' ⊗ B' ∷ Ξ) (Γ₁ ++ B ∷ Λ₁) (E ∷ Δ ++ Λ)
            = intrp≗ (g~ ⊗L⇒L-comm₂)
... | inj₂ (Ξ , eqΔ , refl)
  with cases++ Ξ (E ∷ Δ) Ω₁ Λ eqΔ
... | inj₁ (Ω , eqMid , refl)
  with cases∷ Ξ eqMid
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ω) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ω ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Λ₁ , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ω ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₁) (A' ∷ B' ∷ Ω ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₁) (A' ⊗ B' ∷ Ω ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ B ∷ Λ₁) (A' ⊗ B' ∷ Ω ++ Λ)
            = intrp≗ refl
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) (E ∷ .(Ω₀ ++ A' ⊗ B' ∷ Ω')) Λ
  {Γ₁} {Δ₁} {.(Ω ++ E ∷ Ω₀)} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Ω , refl , refl) | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) Ω₀ (A' ⊗ B' ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω₀ Ω' Λ (A' ⊗ B') |
          ++?-inj₁ (A ⇒ B ∷ Ω) (Γ₁ ++ Δ₁) (E ∷ Ω₀ ++ A' ∷ B' ∷ Ω' ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ω) (Γ₁ ++ Δ₁) (E ∷ Ω₀ ++ A' ⊗ B' ∷ Ω' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ B ∷ Ω) Ω₀ (A' ⊗ B' ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω₀ Ω' Λ (A' ⊗ B')
            = intrp≗ refl
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) (E ∷ Δ) .(Ω' ++ A' ⊗ B' ∷ Ω₁)
  {Γ₁} {Δ₁} {.(Ω ++ E ∷ Δ ++ Ω')} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Ω , refl , refl) | inj₂ (.(E ∷ Δ ++ Ω') , refl , refl) | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) (Δ ++ Ω') (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ω' Δ Ω₁ (A' ⊗ B') |
          ++?-inj₁ (A ⇒ B ∷ Ω) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Ω' ++ A' ∷ B' ∷ Ω₁) |
          ++?-inj₁ (A ⇒ B ∷ Ω) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Ω' ++ A' ⊗ B' ∷ Ω₁) |
          ++?-inj₂ (Γ₁ ++ B ∷ Ω) (Δ ++ Ω') (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ω' Δ Ω₁ (A' ⊗ B')
            = intrp≗ (g~ (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Ω ++ _ ∷ Ω'} {Ω = Ω₁}))
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (Ω , eqΔ , eqΓ)
  with cases++ Ω (E ∷ Δ) (Λ₁ ++ A' ⊗ B' ∷ Ω₁) Λ eqΔ | ++? Γ Γ₁ Ω Δ₁ eqΓ
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (Ω , eqΔ , eqΓ) | inj₁ (Ω' , eqMid , eqΛ) | inj₁ (Ξ , refl , refl)
  with cases∷ Ω eqMid | cases++ Λ₁ Ω' Ω₁ Λ (sym eqΛ)
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Ξ) (A ⇒ B ∷ .(Λ₁ ++ A' ⊗ B' ∷ Ξ')) Λ
  {Γ₁} {Ξ} {Λ₁} {.(Ξ' ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₂ ([] , refl , refl) | inj₁ (.(Λ₁ ++ A' ⊗ B' ∷ Ξ') , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₁ (refl , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ξ) Λ₁ (A' ⊗ B' ∷ Ξ' ++ Λ) (A ⇒ B) |
          cases++-inj₁ Λ₁ Ξ' Λ (A' ⊗ B') |
          ++?-inj₁ [] (Γ₁ ++ Ξ) (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ' ++ Λ)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = A ⇒ B ∷ Λ₁} {Δ₁ = Ξ'}
                    (mip⇒L~⇒ Γ₁ Ξ [] (Λ₁ ++ A' ∷ B' ∷ Ξ') Λ))
                  (~-trans
                    (h~ (⊗L⇒R ∘ ⇒R ⊗L⇒L-comm₂))
                    (~-sym (⇒L~⇒ refl (mip⊗L~Δ Γ₁ (B ∷ Λ₁) Ξ' Λ)))))
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Ξ) (A ⇒ B ∷ Δ) .(Ξ' ++ A' ⊗ B' ∷ Ω₁)
  {Γ₁} {Ξ} {.(Δ ++ Ξ')} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ ([] , refl , refl) | inj₁ (Δ , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₁ (refl , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ξ) (Δ ++ Ξ') (A' ⊗ B' ∷ Ω₁) (A ⇒ B) |
          cases++-inj₂ Ξ' Δ Ω₁ (A' ⊗ B') |
          ++?-inj₁ [] (Γ₁ ++ Ξ) (A ⇒ B ∷ Δ ++ Ξ' ++ A' ⊗ B' ∷ Ω₁)
            = intrp≗
                (~-trans
                  (⊗L~Λ {Λ₀ = Ξ'} (mip⇒L~⇒ Γ₁ Ξ [] Δ (Ξ' ++ A' ∷ B' ∷ Ω₁)))
                  (~-trans
                    (g~ (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Ξ} {Λ = Ξ'} {Ω = Ω₁}))
                    (~-sym (⇒L~⇒ refl (mip⊗L~Λ Γ₁ (B ∷ Δ) Ξ' Ω₁)))))
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Ξ) (E ∷ .(Ω₀ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ')) Λ
  {Γ₁} {.(Ξ ++ E ∷ Ω₀)} {Λ₁} {.(Ξ' ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (.(Λ₁ ++ A' ⊗ B' ∷ Ξ') , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ξ) (Ω₀ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ξ' ++ Λ) E |
          cases++-inj₁ (Ω₀ ++ A ⇒ B ∷ Λ₁) Ξ' Λ (A' ⊗ B') |
          ++?-inj₂ (Γ₁ ++ Ξ) Ω₀ (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ' ++ Λ) E |
          cases++-inj₂ Ξ Γ₁ Ω₀ E |
          cases++-inj₁ Ω₀ (Λ₁ ++ A' ⊗ B' ∷ Ξ') Λ (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = E ∷ Ω₀ ++ A ⇒ B ∷ Λ₁} {Δ₁ = Ξ'}
                    (mip⇒L~⇒ Γ₁ Ξ (E ∷ Ω₀) (Λ₁ ++ A' ∷ B' ∷ Ξ') Λ))
                  (~-trans
                    (h~ (⊗L⇒R ∘ ⇒R ⊗L⇒L-comm₂))
                    (~-sym (⇒L~⇒ refl (mip⊗L~Δ Γ₁ (B ∷ Λ₁) Ξ' Λ)))))
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Ξ) (E ∷ .(Ω₀ ++ A ⇒ B ∷ Ω')) .(Ξ' ++ A' ⊗ B' ∷ Ω₁)
  {Γ₁} {.(Ξ ++ E ∷ Ω₀)} {.(Ω' ++ Ξ')} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ξ) (Ω₀ ++ A ⇒ B ∷ Ω' ++ Ξ') (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ξ' (Ω₀ ++ A ⇒ B ∷ Ω') Ω₁ (A' ⊗ B') |
          ++?-inj₂ (Γ₁ ++ Ξ) Ω₀ (A ⇒ B ∷ Ω' ++ Ξ' ++ A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ξ Γ₁ Ω₀ E |
          cases++-inj₁ Ω₀ Ω' (Ξ' ++ A' ⊗ B' ∷ Ω₁) (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Λ {Λ₀ = Ξ'}
                    (mip⇒L~⇒ Γ₁ Ξ (E ∷ Ω₀) Ω' (Ξ' ++ A' ∷ B' ∷ Ω₁)))
                  (~-trans
                    (g~ (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Ξ} {Λ = Ξ'} {Ω = Ω₁}))
                    (~-sym (⇒L~⇒ refl (mip⊗L~Λ Γ₁ (B ∷ Ω') Ξ' Ω₁)))))
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (Ω , eqΔ , eqΓ) | inj₁ (Ω' , eqMid , eqΛ) | inj₂ (F , Ξ , refl , refl)
  with cases++ Λ₁ Ω' Ω₁ Λ (sym eqΛ)
mip≗⊗L⇒L-comm₂ Γ .((F ∷ Ξ ++ Δ₁) ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ') Λ
  {.(Γ ++ F ∷ Ξ)} {Δ₁} {Λ₁} {.(Ξ' ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {g} refl
  | inj₂ (.(F ∷ Ξ ++ Δ₁) , refl , refl)
  | inj₁ (.(Λ₁ ++ A' ⊗ B' ∷ Ξ') , refl , refl)
  | inj₂ (F , Ξ , refl , refl)
  | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ξ' ++ Λ) F |
          cases++-inj₁ (Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Ξ' Λ (A' ⊗ B') |
          ++?-inj₂ Γ (Ξ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ A' ∷ B' ∷ Ξ' ++ Λ) F |
          cases++-inj₁ Γ Ξ Δ₁ F |
          cases++-inj₁ (Ξ ++ Δ₁) (Λ₁ ++ A' ∷ B' ∷ Ξ') Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ξ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ξ' ++ Λ) F |
          cases++-inj₁ Γ Ξ Δ₁ F |
          cases++-inj₁ (Ξ ++ Δ₁) (Λ₁ ++ A' ⊗ B' ∷ Ξ') Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ξ ++ B ∷ Λ₁) (A' ⊗ B' ∷ Ξ' ++ Λ) F |
          cases++-inj₁ (Ξ ++ B ∷ Λ₁) Ξ' Λ (A' ⊗ B')
            = intrp≗ (h~ ⊗L⇒L-comm₂)
mip≗⊗L⇒L-comm₂ Γ .((F ∷ Ξ ++ Δ₁) ++ A ⇒ B ∷ Ω') .(Ξ' ++ A' ⊗ B' ∷ Ω₁)
  {.(Γ ++ F ∷ Ξ)} {Δ₁} {.(Ω' ++ Ξ')} {Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g} refl
  | inj₂ (.(F ∷ Ξ ++ Δ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (F , Ξ , refl , refl)
  | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ Δ₁ ++ A ⇒ B ∷ Ω' ++ Ξ') (A' ⊗ B' ∷ Ω₁) F |
          cases++-inj₂ Ξ' (Ξ ++ Δ₁ ++ A ⇒ B ∷ Ω') Ω₁ (A' ⊗ B') |
          ++?-inj₂ Γ (Ξ ++ Δ₁) (A ⇒ B ∷ Ω' ++ Ξ' ++ A' ∷ B' ∷ Ω₁) F |
          cases++-inj₁ Γ Ξ Δ₁ F |
          cases++-inj₁ (Ξ ++ Δ₁) Ω' (Ξ' ++ A' ∷ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₂ Γ (Ξ ++ Δ₁) (A ⇒ B ∷ Ω' ++ Ξ' ++ A' ⊗ B' ∷ Ω₁) F |
          cases++-inj₁ Γ Ξ Δ₁ F |
          cases++-inj₁ (Ξ ++ Δ₁) Ω' (Ξ' ++ A' ⊗ B' ∷ Ω₁) (A ⇒ B)
            = intrp≗ (~-sym (⇒L~ΓΛ (mip⊗L~Λ Γ (F ∷ Ξ ++ B ∷ Ω') Ξ' Ω₁ {f = g}) refl))
mip≗⊗L⇒L-comm₂ .(Γ₁ ++ Ξ) (E ∷ Δ) .(Ω' ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {Γ₁} {.(Ξ ++ E ∷ Δ ++ Ω')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (.(E ∷ Δ ++ Ω') , refl , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ξ) (Δ ++ Ω' ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (Ω' ++ A ⇒ B ∷ Λ₁) Δ Ω₁ (A' ⊗ B') |
          ++?-inj₂ (Γ₁ ++ Ξ) (Δ ++ Ω') (A ⇒ B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) E |
          cases++-inj₂ Ξ Γ₁ (Δ ++ Ω') E |
          cases++-inj₂ Ω' Δ (Λ₁ ++ A' ∷ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Ξ) (Δ ++ Ω') (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ξ Γ₁ (Δ ++ Ω') E |
          cases++-inj₂ Ω' Δ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) (A ⇒ B)
            = intrp≗ (g~ ⊗L⇒L-comm₂)
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (Ω , eqΔ , eqΓ) | inj₂ (Ω' , refl , refl) | inj₂ (F , Ξ , refl , eq5)
  with inj∷ eq5
... | refl , eq3
  with ++? Ξ Δ Δ₁ Ω' eq3
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) .(Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {.(Γ ++ E ∷ Δ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g} refl
  | inj₂ (.(E ∷ Δ ++ Δ₁) , refl , refl)
  | inj₂ (Δ₁ , refl , refl)
  | inj₂ (E , Δ , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (Δ₁ ++ A ⇒ B ∷ Λ₁) Δ Ω₁ (A' ⊗ B') |
          ++?-inj₂ Γ (Δ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) E |
          cases++-inj₁ Γ Δ Δ₁ E |
          cases++-inj₂ Δ₁ Δ (Λ₁ ++ A' ∷ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₁ [] Δ Δ₁ |
          ++?-inj₂ Γ (Δ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₁ Γ Δ Δ₁ E |
          cases++-inj₂ Δ₁ Δ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₁ [] Δ Δ₁
            = intrp≗
                (~-trans
                  (g~ (⊗L⊗L
                    {Γ = Γ} {Δ = Δ₁ ++ A ⇒ B ∷ Λ₁} {Λ = Ω₁}
                    {A = MIP.D (mip Γ (E ∷ Δ) (B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) g refl)} {B = I} {A' = A'} {B' = B'} ∘
                    ⊗L {Γ = Γ} {A = MIP.D (mip Γ (E ∷ Δ) (B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) g refl)} {B = I}
                      (⊗L⇒L-comm₂ {Γ = Γ ++ _ ∷ []} {Δ = I ∷ Δ₁} {Λ = Λ₁} {Ω = Ω₁})))
                  (⇒L~⊗ refl (~-sym (mip⊗L~Λ Γ (E ∷ Δ) (B ∷ Λ₁) Ω₁))))
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) .(F' ∷ Ω'' ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {.(Γ ++ E ∷ Δ ++ F' ∷ Ω'')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g} refl
  | inj₂ (.(E ∷ Δ ++ F' ∷ Ω'' ++ Δ₁) , refl , refl)
  | inj₂ (.(F' ∷ Ω'' ++ Δ₁) , refl , refl)
  | inj₂ (E , .(Δ ++ F' ∷ Ω'') , refl , refl)
  | refl , refl
  | inj₁ (F' ∷ Ω'' , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ F' ∷ Ω'' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (F' ∷ Ω'' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Δ Ω₁ (A' ⊗ B') |
          ++?-inj₂ Γ (Δ ++ F' ∷ Ω'' ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ F' ∷ Ω'') Δ₁ E |
          cases++-inj₂ (F' ∷ Ω'' ++ Δ₁) Δ (Λ₁ ++ A' ∷ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₂ Δ Ω'' Δ₁ F' |
          ++?-inj₂ Γ (Δ ++ F' ∷ Ω'' ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ F' ∷ Ω'') Δ₁ E |
          cases++-inj₂ (F' ∷ Ω'' ++ Δ₁) Δ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₂ Δ Ω'' Δ₁ F'
            = intrp≗
                (~-trans
                  (g~ (⊗L⇒L-comm₂ {Γ = Γ ++ _ ∷ F' ∷ Ω''} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁}))
                  (⇒L~Λ {Γ = Γ} {Λ₀ = F' ∷ Ω''}
                    (~-sym (mip⊗L~Λ Γ (E ∷ Δ) (F' ∷ Ω'' ++ B ∷ Λ₁) Ω₁))
                    refl))
mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) .(Ω' ++ A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {.(Γ ++ E ∷ Ξ)} {.(F' ∷ Ω'' ++ Ω')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g} refl
  | inj₂ (.(E ∷ Δ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (E , Ξ , refl , refl)
  | refl , refl
  | inj₂ (F' , Ω'' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ F' ∷ Ω'' ++ Ω' ++ A ⇒ B ∷ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (Ω' ++ A ⇒ B ∷ Λ₁) (Ξ ++ F' ∷ Ω'') Ω₁ (A' ⊗ B') |
          ++?-inj₂ Γ (Ξ ++ F' ∷ Ω'' ++ Ω') (A ⇒ B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) E |
          cases++-inj₁ Γ Ξ (F' ∷ Ω'' ++ Ω') E |
          cases++-inj₂ Ω' (Ξ ++ F' ∷ Ω'') (Λ₁ ++ A' ∷ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₁ (F' ∷ Ω'') Ξ Ω' |
          ++?-inj₂ Γ (Ξ ++ F' ∷ Ω'' ++ Ω') (A ⇒ B ∷ Λ₁ ++ A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₁ Γ Ξ (F' ∷ Ω'' ++ Ω') E |
          cases++-inj₂ Ω' (Ξ ++ F' ∷ Ω'') (Λ₁ ++ A' ⊗ B' ∷ Ω₁) (A ⇒ B) |
          ++?-inj₁ (F' ∷ Ω'') Ξ Ω'
            = intrp≗
                (~-trans
                  (g~ (⊗L⊗L
                    {Γ = Γ} {Δ = Ω' ++ A ⇒ B ∷ Λ₁} {Λ = Ω₁}
                    {A = MIP.D (mip Γ (E ∷ Ξ) (B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) g refl)}
                    {B = MIP.D (mip [] (F' ∷ Ω'') Ω' f refl)}
                    {A' = A'} {B' = B'} ∘
                    ⊗L {Γ = Γ}
                      {A = MIP.D (mip Γ (E ∷ Ξ) (B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁) g refl)}
                      {B = MIP.D (mip [] (F' ∷ Ω'') Ω' f refl)}
                      (⊗L⇒L-comm₂ {Γ = Γ ++ _ ∷ []} {Δ = _ ∷ Ω'} {Λ = Λ₁} {Ω = Ω₁})))
                  (⇒L~⊗ refl (~-sym (mip⊗L~Λ Γ (E ∷ Ξ) (B ∷ Λ₁) Ω₁))))
