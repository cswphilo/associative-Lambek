{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLImpLAssoc where

open import IntrpWellDefCases.Base
open import IntrpWellDefCases.ILImpLAssoc using (mip⇒L~⇒; mip⇒L~Δ; mip⇒L~ΔΓ)

mip⊗L~Λ : ∀ Γ Δ Λ₀ Λ₁ {A' B' C}
  {f : Γ ++ Δ ++ Λ₀ ++ A' ∷ B' ∷ Λ₁ ⊢ C}
  → mip Γ Δ (Λ₀ ++ A' ⊗ B' ∷ Λ₁) (⊗L {Γ ++ Δ ++ Λ₀} f) refl
      ~ ⊗L~Λ' {Γ} {Δ} {Λ₀} {Λ₁} (mip Γ Δ (Λ₀ ++ A' ∷ B' ∷ Λ₁) f refl)
mip⊗L~Λ Γ [] Λ₀ Λ₁ = g~ IL⊗L-comm₁
mip⊗L~Λ Γ (E ∷ Δ) Λ₀ Λ₁ {A'} {B'}
  rewrite ++?-inj₂ Γ (Δ ++ Λ₀) (A' ⊗ B' ∷ Λ₁) E |
          cases++-inj₂ Λ₀ Δ Λ₁ (A' ⊗ B') = refl

mip⊗L~Δ : ∀ Γ Δ₀ Δ₁ Λ {A' B' C}
  {f : Γ ++ Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Λ ⊢ C}
  → mip Γ (Δ₀ ++ A' ⊗ B' ∷ Δ₁) Λ (⊗L {Γ ++ Δ₀} f) refl
      ~ ⊗L~Δ' {Γ} {Δ₀} {Δ₁} {Λ} (mip Γ (Δ₀ ++ A' ∷ B' ∷ Δ₁) Λ f refl)
mip⊗L~Δ Γ [] Δ₁ Λ {A'} {B'}
  rewrite ++?-inj₁ [] Γ (A' ⊗ B' ∷ Δ₁ ++ Λ) = refl
mip⊗L~Δ Γ (E ∷ Δ₀) Δ₁ Λ {A'} {B'}
  rewrite ++?-inj₂ Γ Δ₀ (A' ⊗ B' ∷ Δ₁ ++ Λ) E |
          cases++-inj₁ Δ₀ Δ₁ Λ (A' ⊗ B') = refl

mip≗⊗L⇒L-assoc : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ++ A' ∷ B' ∷ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁ ++ Δ₀} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L (⊗L f) g) eq)
mip≗⊗L⇒L-assoc Γ [] Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} eq
  with cases++ (Γ₁ ++ Δ₀) Γ (Δ₁ ++ A ⇒ B ∷ Λ₁) Λ (sym eq)
... | inj₁ (Ω , refl , eq2)
  with cases++ Δ₁ Ω Λ₁ Λ (sym eq2)
mip≗⊗L⇒L-assoc .(Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Ω') [] Λ {Γ₁} {Δ₀} {Δ₁} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} refl
  | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) =
    intrp≗ (g~ (IL {Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Ω'} {Λ}
      (⊗L⇒L-assoc {Γ₁} {Δ₀} {Δ₁} {Ω' ++ Λ})))
mip≗⊗L⇒L-assoc .(Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Ω) [] .(Ω' ++ A ⇒ B ∷ Λ₁) {Γ₁} {Δ₀} {.(Ω ++ Ω')} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) =
    intrp≗ (g~ (IL {Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Ω} {Ω' ++ A ⇒ B ∷ Λ₁}
      (⊗L⇒L-assoc {Γ₁} {Δ₀} {Ω ++ Ω'} {Λ₁})))
mip≗⊗L⇒L-assoc Γ [] Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (Ω , refl , eqΓ)
  with ++? Γ Γ₁ Ω Δ₀ eqΓ
mip≗⊗L⇒L-assoc .(Γ₁ ++ Ξ) [] .(Ω ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(Ξ ++ Ω)} {Δ₁} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ₁ ++ Ξ} {Ω ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁}
      (⊗L⇒L-assoc {Γ₁} {Ξ ++ Ω} {Δ₁} {Λ₁})))
mip≗⊗L⇒L-assoc Γ [] .(F ∷ Ξ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ F ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ (.(F ∷ Ξ ++ Δ₀) , refl , refl) | inj₂ (F , Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ} {F ∷ Ξ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁}
      (⊗L⇒L-assoc {Γ ++ F ∷ Ξ} {Δ₀} {Δ₁} {Λ₁})))
mip≗⊗L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} eq
  with cases++ (Γ₁ ++ Δ₀) Γ (Δ₁ ++ A ⇒ B ∷ Λ₁) (E ∷ Δ ++ Λ) (sym eq)
... | inj₁ (Ω , refl , eq2)
  with cases++ Δ₁ Ω Λ₁ (E ∷ Δ ++ Λ) (sym eq2)
mip≗⊗L⇒L-assoc .(Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Ω) (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₁ (Ω , refl , refl) | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Ω') (Γ₁ ++ Δ₀) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ω') (Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ω') (Γ₁ ++ Δ₀ ++ A' ∷ B' ∷ Δ₁) (E ∷ Δ ++ Λ)
            = intrp≗ (g~ ⊗L⇒L-assoc)
... | inj₂ (Ω' , eq1 , refl)
  with cases++ Ω' (E ∷ Δ) Λ₁ Λ eq1
... | inj₁ (Ω'' , eqMid , refl)
  with cases∷ Ω' eqMid
mip≗⊗L⇒L-assoc .(Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Ω) (A ⇒ B ∷ Ω'') Λ {Γ₁} {Δ₀} {Ω} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} refl
  | inj₁ (Ω , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Ω) (Γ₁ ++ Δ₀) (A ⇒ B ∷ Ω'' ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ A' ∷ B' ∷ Ω) (A ⇒ B ∷ Ω'' ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Ω) (A ⇒ B ∷ Ω'' ++ Λ)
            = intrp≗
                (~-trans
                  (g~ ⊗L⇒L-assoc)
                  (~-sym (⇒L~⇒ (mip⊗L~Δ [] Δ₀ Ω []) refl)))
mip≗⊗L⇒L-assoc .(Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Ω) (E ∷ .(Ω₀ ++ A ⇒ B ∷ Ω'')) Λ {Γ₁} {Δ₀} {.(Ω ++ E ∷ Ω₀)} {.(Ω'' ++ Λ)} {A} {B} {A'} {B'} refl
  | inj₁ (Ω , refl , refl) | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (Ω₀ , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Ω) (Γ₁ ++ Δ₀) (E ∷ Ω₀ ++ A ⇒ B ∷ Ω'' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A' ∷ B' ∷ Ω) Ω₀ (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ (Δ₀ ++ A' ∷ B' ∷ Ω) Γ₁ Ω₀ E |
          cases++-inj₁ Ω₀ Ω'' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A' ⊗ B' ∷ Ω) Ω₀ (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ (Δ₀ ++ A' ⊗ B' ∷ Ω) Γ₁ Ω₀ E |
          cases++-inj₁ Ω₀ Ω'' Λ (A ⇒ B)
            = intrp≗
                (~-trans
                  (g~ ⊗L⇒L-assoc)
                  (~-sym (⇒L~⇒ (mip⊗L~Δ [] Δ₀ Ω (E ∷ Ω₀)) refl)))
mip≗⊗L⇒L-assoc .(Γ₁ ++ D' ∷ Δ₀ ++ A' ⊗ B' ∷ Ω) (E ∷ Δ) Λ {Γ₁} {D' ∷ Δ₀} {.(Ω ++ Ω')} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} refl
  | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Ω) (Γ₁ ++ D' ∷ Δ₀) (E ∷ Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ D' ∷ Δ₀ ++ A' ⊗ B' ∷ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          ++?-inj₂ (Γ₁ ++ D' ∷ Δ₀ ++ A' ∷ B' ∷ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (D' ∷ Δ₀ ++ A' ⊗ B' ∷ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ (D' ∷ Δ₀ ++ A' ∷ B' ∷ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ (A' ⊗ B' ∷ Ω) (D' ∷ Δ₀) (E ∷ Δ ++ Ω'')
            = intrp≗ (g~ (⊗L⇒L-assoc {Γ₁} {D' ∷ Δ₀} {Ω ++ _ ∷ Ω''}))
mip≗⊗L⇒L-assoc ._ (E ∷ Δ) Λ {Γ₁} {[]} {_} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} refl
  | inj₁ ([] , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ []) Γ₁ (E ∷ Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ []) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ∷ B' ∷ []) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ []) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ⊗ B' ∷ []) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ (A' ⊗ B' ∷ []) [] (E ∷ Δ ++ Ω'')
            = intrp≗ (g~ ⊗L⇒L-assoc)
mip≗⊗L⇒L-assoc .(Γ₁ ++ A' ⊗ B' ∷ D' ∷ Ω) (E ∷ Δ) Λ {Γ₁} {[]} {.(D' ∷ Ω ++ Ω')} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₁ (D' ∷ Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ D' ∷ Ω) Γ₁ (E ∷ Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ A' ∷ B' ∷ D' ∷ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ∷ B' ∷ D' ∷ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ A' ⊗ B' ∷ D' ∷ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ⊗ B' ∷ D' ∷ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ (A' ⊗ B' ∷ D' ∷ Ω) [] (E ∷ Δ ++ Ω'')
            = intrp≗ (g~ ⊗L⇒L-assoc)
mip≗⊗L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (Ω₁ , eq1 , eq2)
  with cases++ Ω₁ (E ∷ Δ) (Δ₁ ++ A ⇒ B ∷ Λ₁) Λ eq1 | ++? Γ Γ₁ Ω₁ Δ₀ eq2
mip≗⊗L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (Ω₁ , eqTop , eqΓ) | inj₁ (Ω , eqΔ , eq4) | inj₁ (Ξ , refl , refl)
  with cases∷ Ω₁ eqΔ | cases++ Δ₁ Ω Λ₁ Λ (sym eq4)
mip≗⊗L⇒L-assoc .(Γ₁ ++ Ξ) (A' ⊗ B' ∷ .(Δ₁ ++ A ⇒ B ∷ Ξ')) Λ {Γ₁} {Ξ} {Δ₁} {.(Ξ' ++ Λ)} {A} {B} {A'} {B'} refl
  | inj₂ ([] , refl , refl) | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ξ') , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₁ (refl , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Ξ) (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Ξ' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ Ξ) Δ₁ (A ⇒ B ∷ Ξ' ++ Λ) (A' ⊗ B') |
          cases++-inj₂ Ξ Γ₁ Δ₁ (A' ⊗ B') |
          cases++-inj₁ Δ₁ Ξ' Λ (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = []} {Δ₁ = Δ₁ ++ A ⇒ B ∷ Ξ'}
                    (mip⇒L~⇒ Γ₁ Ξ (A' ∷ B' ∷ Δ₁) Ξ' Λ))
                  (~-trans
                    (h~ (⊗L⇒R ∘ ⇒R ⊗L⇒L-assoc))
                    (~-sym (⇒L~⇒ (mip⊗L~Λ [] Ξ [] Δ₁) refl))))
mip≗⊗L⇒L-assoc .(Γ₁ ++ Ξ) (E ∷ .(Ω₀ ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Ξ')) Λ {Γ₁} {.(Ξ ++ E ∷ Ω₀)} {Δ₁} {.(Ξ' ++ Λ)} {A} {B} {A'} {B'} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ξ') , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ξ) Ω₀ (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Ξ' ++ Λ) E |
          cases++-inj₁ Ω₀ (Δ₁ ++ A ⇒ B ∷ Ξ') Λ (A' ⊗ B') |
          ++?-inj₂ (Γ₁ ++ Ξ) (Ω₀ ++ A' ⊗ B' ∷ Δ₁) (A ⇒ B ∷ Ξ' ++ Λ) E |
          cases++-inj₂ Ξ Γ₁ (Ω₀ ++ A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₁ (Ω₀ ++ A' ⊗ B' ∷ Δ₁) Ξ' Λ (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = E ∷ Ω₀} {Δ₁ = Δ₁ ++ A ⇒ B ∷ Ξ'}
                    (mip⇒L~⇒ Γ₁ Ξ (E ∷ Ω₀ ++ A' ∷ B' ∷ Δ₁) Ξ' Λ))
                  (~-trans
                    (h~ (⊗L⇒R ∘ ⇒R ⊗L⇒L-assoc))
                    (~-sym (⇒L~⇒ (mip⊗L~Λ [] Ξ (E ∷ Ω₀) Δ₁) refl))))
mip≗⊗L⇒L-assoc Γ (A' ⊗ B' ∷ Ω) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {[]} {.(Ω ++ Ξ')} {Λ₁} {A} {B} {A'} {B'} {f = f} refl
  | inj₂ ([] , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ Γ₁ (Ω ++ Ξ') (A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          cases++-inj₂ [] Γ₁ (Ω ++ Ξ') (A' ⊗ B') |
          cases++-inj₂ Ξ' Ω Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = []} {Δ₁ = Ω} (mip⇒L~Δ Γ₁ (A' ∷ B' ∷ Ω) Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mip⊗L~Δ [] [] Ω Ξ' {f = f}) refl)))
mip≗⊗L⇒L-assoc Γ (E ∷ .(Ω₀ ++ A' ⊗ B' ∷ Ω)) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(E ∷ Ω₀)} {.(Ω ++ Ξ')} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ ([] , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ₁ Ω₀ (A' ⊗ B' ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Ω₀ Ω (Ξ' ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ Γ₁ (Ω₀ ++ A' ⊗ B' ∷ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ [] Γ₁ (Ω₀ ++ A' ⊗ B' ∷ Ω ++ Ξ') E |
          cases++-inj₂ Ξ' (Ω₀ ++ A' ⊗ B' ∷ Ω) Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = E ∷ Ω₀} {Δ₁ = Ω}
                    (mip⇒L~Δ Γ₁ (E ∷ Ω₀ ++ A' ∷ B' ∷ Ω) Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mip⊗L~Δ [] (E ∷ Ω₀) Ω Ξ') refl)))
mip≗⊗L⇒L-assoc .(Γ₁ ++ D' ∷ Ξ) (A' ⊗ B' ∷ Ω) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {D' ∷ Ξ} {.(Ω ++ Ξ')} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ ([] , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ (D' ∷ Ξ , refl , refl)
  | inj₁ (refl , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ D' ∷ Ξ) (A' ⊗ B' ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ D' ∷ Ξ) (Ω ++ Ξ') (A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          cases++-inj₂ (D' ∷ Ξ) Γ₁ (Ω ++ Ξ') (A' ⊗ B') |
          cases++-inj₂ Ξ' Ω Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = []} {Δ₁ = Ω}
                    (mip⇒L~ΔΓ Γ₁ (D' ∷ Ξ) (A' ∷ B' ∷ Ω) Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mip⊗L~Δ (D' ∷ Ξ) [] Ω Ξ') refl)))
mip≗⊗L⇒L-assoc .(Γ₁ ++ D' ∷ Ξ) (E ∷ .(Ω₀ ++ A' ⊗ B' ∷ Ω)) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(D' ∷ Ξ ++ E ∷ Ω₀)} {.(Ω ++ Ξ')} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ (D' ∷ Ξ , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ D' ∷ Ξ) Ω₀ (A' ⊗ B' ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Ω₀ Ω (Ξ' ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ (Γ₁ ++ D' ∷ Ξ) (Ω₀ ++ A' ⊗ B' ∷ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (D' ∷ Ξ) Γ₁ (Ω₀ ++ A' ⊗ B' ∷ Ω ++ Ξ') E |
          cases++-inj₂ Ξ' (Ω₀ ++ A' ⊗ B' ∷ Ω) Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (⊗L~Δ {Δ₀ = E ∷ Ω₀} {Δ₁ = Ω}
                    (mip⇒L~ΔΓ Γ₁ (D' ∷ Ξ) (E ∷ Ω₀ ++ A' ∷ B' ∷ Ω) Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mip⊗L~Δ (D' ∷ Ξ) (E ∷ Ω₀) Ω Ξ') refl)))
mip≗⊗L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (Ω₁ , eq1 , eq2) | inj₁ (Ω , refl , eq4) | inj₂ (C' , Ξ , refl , refl)
  with cases++ Δ₁ Ω Λ₁ Λ (sym eq4)
mip≗⊗L⇒L-assoc Γ .((C' ∷ Ξ ++ Δ₀) ++ A' ⊗ B' ∷ Ω) Λ {.(Γ ++ C' ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (.(C' ∷ Ξ ++ Δ₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ Δ₀) (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Ξ' ++ Λ) C' |
          cases++-inj₁ (Ξ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Ξ') Λ (A' ⊗ B') |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ A' ∷ B' ∷ Δ₁) (A ⇒ B ∷ Ξ' ++ Λ) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ A' ∷ B' ∷ Δ₁) C' |
          cases++-inj₁ (Ξ ++ Δ₀ ++ A' ∷ B' ∷ Δ₁) Ξ' Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁) (A ⇒ B ∷ Ξ' ++ Λ) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ A' ⊗ B' ∷ Δ₁) C' |
          cases++-inj₁ (Ξ ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁) Ξ' Λ (A ⇒ B)
            = intrp≗ (h~ ⊗L⇒L-assoc)
mip≗⊗L⇒L-assoc Γ .((C' ∷ Ξ ++ Δ₀) ++ A' ⊗ B' ∷ Ω) Λ {.(Γ ++ C' ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (.(C' ∷ Ξ ++ Δ₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ Δ₀) (A' ⊗ B' ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) C' |
          cases++-inj₁ (Ξ ++ Δ₀) Ω (Ξ' ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ A' ∷ B' ∷ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ A' ∷ B' ∷ Ω ++ Ξ') C' |
          cases++-inj₂ Ξ' (Ξ ++ Δ₀ ++ A' ∷ B' ∷ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A' ∷ B' ∷ Ω) Ξ Ξ' |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ A' ⊗ B' ∷ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ A' ⊗ B' ∷ Ω ++ Ξ') C' |
          cases++-inj₂ Ξ' (Ξ ++ Δ₀ ++ A' ⊗ B' ∷ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A' ⊗ B' ∷ Ω) Ξ Ξ'
            = intrp≗
                (~-trans
                  (h~ ⊗L⊗R₂)
                  (~-sym (⇒L~⊗ (mip⊗L~Δ [] Δ₀ Ω Ξ') refl)))
mip≗⊗L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ω) (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ Γ (Δ ++ Ω ++ A' ∷ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ [] Γ (Δ ++ Ω ++ A' ∷ B' ∷ Δ₁) E |
          cases++-inj₂ (Ω ++ A' ∷ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ (Δ ++ Ω ++ A' ⊗ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ [] Γ (Δ ++ Ω ++ A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₂ (Ω ++ A' ⊗ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ [] (Δ ++ Ω) (A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₂ Ω Δ Δ₁ (A' ⊗ B')
            = intrp≗ (g~ ⊗L⇒L-assoc)
mip≗⊗L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f = f} refl
  | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω , refl , refl) | inj₁ (D' ∷ Ξ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ D' ∷ Ξ) (Δ ++ Ω) (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ (Γ₁ ++ D' ∷ Ξ) (Δ ++ Ω ++ A' ∷ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (D' ∷ Ξ) Γ₁ (Δ ++ Ω ++ A' ∷ B' ∷ Δ₁) E |
          cases++-inj₂ (Ω ++ A' ∷ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ D' ∷ Ξ) (Δ ++ Ω ++ A' ⊗ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (D' ∷ Ξ) Γ₁ (Δ ++ Ω ++ A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₂ (Ω ++ A' ⊗ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (D' ∷ Ξ) (Δ ++ Ω) (A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₂ Ω Δ Δ₁ (A' ⊗ B')
            = intrp≗ (g~ (⊗L⇒L-assoc {_}{D' ∷ Ξ ++ _ ∷ Ω}))
mip≗⊗L⇒L-assoc Γ (x ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (Ω₁ , eq1 , eq2) | inj₂ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , eq5)
  with inj∷ eq5
... | refl , eq3
  with ++? Ξ Δ Δ₀ Ω eq3
mip≗⊗L⇒L-assoc Γ (x ∷ Δ) .(Ω ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ω) (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) x |
          cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ Γ (Δ ++ Ω ++ A' ∷ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ Δ (Ω ++ A' ∷ B' ∷ Δ₁) x |
          cases++-inj₂ (Ω ++ A' ∷ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Δ (Ω ++ A' ∷ B' ∷ Δ₁) |
          ++?-inj₂ Γ (Δ ++ Ω ++ A' ⊗ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ Δ (Ω ++ A' ⊗ B' ∷ Δ₁) x |
          cases++-inj₂ (Ω ++ A' ⊗ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Δ (Ω ++ A' ⊗ B' ∷ Δ₁)
            = intrp≗
                (g~ (⊗L⊗L ∘
                  ⊗L (⊗L⇒L-assoc {Γ ++ _ ∷ []} {I ∷ Ω} {Δ₁} ∘ ⇒L (~ IL⊗L-comm₁) refl)))
mip≗⊗L⇒L-assoc Γ (x ∷ Δ) .(Ω ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₁ (D' ∷ Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ D' ∷ Ξ' ++ Δ₀) (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) x |
          cases++-inj₂ (D' ∷ Ξ' ++ Δ₀) Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ Γ (Δ ++ D' ∷ Ξ' ++ Δ₀ ++ A' ∷ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ (Δ ++ D' ∷ Ξ') (Δ₀ ++ A' ∷ B' ∷ Δ₁) x |
          cases++-inj₂ (D' ∷ Ξ' ++ Δ₀ ++ A' ∷ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Ξ' (Δ₀ ++ A' ∷ B' ∷ Δ₁) D' |
          ++?-inj₂ Γ (Δ ++ D' ∷ Ξ' ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ (Δ ++ D' ∷ Ξ') (Δ₀ ++ A' ⊗ B' ∷ Δ₁) x |
          cases++-inj₂ (D' ∷ Ξ' ++ Δ₀ ++ A' ⊗ B' ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Ξ' (Δ₀ ++ A' ⊗ B' ∷ Δ₁) D'
            = intrp≗ (g~ ⊗L⇒L-assoc)
mip≗⊗L⇒L-assoc Γ (x ∷ Δ) .(Ω ++ A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} refl
  | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₂ (C'' , Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ C'' ∷ Ξ' ++ Ω) (A' ⊗ B' ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) x |
          cases++-inj₂ Ω (Ξ ++ C'' ∷ Ξ') (Δ₁ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B') |
          ++?-inj₂ Γ (Ξ ++ C'' ∷ Ξ' ++ Ω ++ A' ∷ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ Ξ (C'' ∷ Ξ' ++ Ω ++ A' ∷ B' ∷ Δ₁) x |
          cases++-inj₂ (Ω ++ A' ∷ B' ∷ Δ₁) (Ξ ++ C'' ∷ Ξ') Λ₁ (A ⇒ B) |
          ++?-inj₁ (C'' ∷ Ξ') Ξ (Ω ++ A' ∷ B' ∷ Δ₁) |
          ++?-inj₂ Γ (Ξ ++ C'' ∷ Ξ' ++ Ω ++ A' ⊗ B' ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ Ξ (C'' ∷ Ξ' ++ Ω ++ A' ⊗ B' ∷ Δ₁) x |
          cases++-inj₂ (Ω ++ A' ⊗ B' ∷ Δ₁) (Ξ ++ C'' ∷ Ξ') Λ₁ (A ⇒ B) |
          ++?-inj₁ (C'' ∷ Ξ') Ξ (Ω ++ A' ⊗ B' ∷ Δ₁) |
          ++?-inj₂ [] (Ξ' ++ Ω) (A' ⊗ B' ∷ Δ₁) C'' |
          cases++-inj₂ Ω Ξ' Δ₁ (A' ⊗ B')
            = intrp≗ (g~ (⊗L⊗L ∘ ⊗L ⊗L⇒L-assoc))
