{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLLeftImpLComm1 where

open import IntrpWellDefCases.Base

mip≗⊗L⇐L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ B ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁} {Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁} {A'} {B'} (⇐L {Γ₁ ++ A' ∷ B' ∷ Λ₁} {Δ₁} {Ω₁} f g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁ ++ A' ⊗ B' ∷ Λ₁} {Δ₁} {Ω₁} f (⊗L {Γ₁} {Λ₁ ++ B ∷ Ω₁} {A'} {B'} g)) eq)
mip≗⊗L⇐L-comm₁ Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⇐L-comm₁
mip≗⊗L⇐L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁) eq
... | inj₁ (Ω , eq1 , refl)
  with cases∷ Ω eq1
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.[] , eq1 , refl) | inj₁ (refl , refl , eq3)
  with cases++ Λ₁ Δ (Δ₁ ++ Ω₁) Λ eq3
... | inj₁ (Ξ , refl , eqb)
  with ++? Ξ Δ₁ Λ Ω₁ eqb
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ .(Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ψ)) Λ {Γ₁} {Δ₁} {Λ₁} {.(Ψ ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (.(Δ₁ ++ Ψ) , refl , refl) | inj₁ (Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ (A' ∷ B' ∷ Λ₁) Γ₁ (Δ₁ ++ Ψ) (B ⇐ A) |
          ++?-inj₁ Ψ Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ (A' ⊗ B' ∷ Λ₁) Γ₁ (Δ₁ ++ Ψ) (B ⇐ A) |
          ++?-inj₁ Ψ Δ₁ Λ |
          ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ψ ++ Λ) =
    intrp≗ (h~ (⊗L⇐L-comm₁ {[]}))
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ .(Λ₁ ++ B ⇐ A ∷ Ξ)) .(F ∷ Ψ ++ Ω₁) {Γ₁} {.(Ξ ++ F ∷ Ψ)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ξ , refl , refl) | inj₂ (F , Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) Ξ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (A' ∷ B' ∷ Λ₁) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₂ Ξ Ψ Ω₁ F |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Ξ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (A' ⊗ B' ∷ Λ₁) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₂ Ξ Ψ Ω₁ F |
          ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) =
    intrp≗ (h~ (⊗L⇐R ∘ ⇐R (⊗L⇐L-comm₁ {[]})))
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ []) (.(A' ⊗ B') ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , eq3) | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₂ Ξ (Γ₁ ++ A' ∷ B' ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ Ξ (Γ₁ ++ A' ⊗ B' ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₁ [] Γ₁ (A' ⊗ B' ∷ Δ ++ Ξ ++ B ∷ Ω₁) =
    intrp≗ refl
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl)
  with cases++ Ω₀ Λ₁ (Δ ++ Λ) (B ⇐ A ∷ Δ₁ ++ Ω₁) eq3
... | inj₁ (Ξ , refl , eqb)
  with ++? Ξ Δ (B ⇐ A ∷ Δ₁ ++ Ω₁) Λ eqb
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) .(Ψ ++ B ⇐ A ∷ Δ₁ ++ Ω₁) {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Δ ++ Ψ)} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , refl , refl) | inj₂ (Ω₀ , refl , refl)
  | inj₁ (.(Δ ++ Ψ) , refl , refl) | inj₁ (Ψ , refl , refl)
  rewrite cases++-inj₂ Ψ (Γ₁ ++ A' ∷ B' ∷ Ω₀ ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ Ψ (Γ₁ ++ A' ⊗ B' ∷ Ω₀ ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₀) Γ₁ (E ∷ Δ ++ Ψ ++ B ∷ Ω₁) =
    let n = mip (Γ₁ ++ A' ∷ B' ∷ Ω₀) (E ∷ Δ) (Ψ ++ B ∷ Ω₁) g refl
    in intrp≗ (g~ (⊗L⇐L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Ω₀ ++ n .MIP.D ∷ Ψ} {Ω = Ω₁}))
... | inj₂ (F , Ψ , refl , eqc)
  with inj∷ eqc
... | refl , eqd
  with ++? Δ₁ Ψ Ω₁ Λ (sym eqd)
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ .(Ξ ++ B ⇐ A ∷ Ψ)) .Ω₁ {Γ₁} {.(Ψ ++ [])} {.(Ω₀ ++ E ∷ Ξ)} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , refl , refl) | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ξ , refl , refl) | inj₂ (.(B ⇐ A) , Ψ , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Ω₀ ++ E ∷ Ξ) Ψ Ω₁ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) (Γ₁ ++ A' ∷ B' ∷ Ω₀) Ψ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Ω₀ ++ E ∷ Ξ) Ψ Ω₁ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) (Γ₁ ++ A' ⊗ B' ∷ Ω₀) Ψ (B ⇐ A) |
          ++?-inj₁ [] Ψ Ω₁ |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₀) Γ₁ (E ∷ Ξ ++ B ∷ Ω₁) = intrp≗ refl
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ .(Ξ ++ B ⇐ A ∷ Ψ)) .(G ∷ Ω₂ ++ Ω₁) {Γ₁} {.(Ψ ++ G ∷ Ω₂)} {.(Ω₀ ++ E ∷ Ξ)} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , refl , refl) | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ξ , refl , refl) | inj₂ (.(B ⇐ A) , Ψ , refl , refl)
  | refl , refl
  | inj₁ (G ∷ Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Ω₀ ++ E ∷ Ξ) Ψ (G ∷ Ω₂ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) (Γ₁ ++ A' ∷ B' ∷ Ω₀) Ψ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Ω₀ ++ E ∷ Ξ) Ψ (G ∷ Ω₂ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) (Γ₁ ++ A' ⊗ B' ∷ Ω₀) Ψ (B ⇐ A) |
          ++?-inj₂ Ψ Ω₂ Ω₁ G |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₀) Γ₁ (E ∷ Ξ ++ B ∷ Ω₁) =
    intrp≗ (g~ (⊗L⇐L-comm₁ {Γ = Γ₁} {Δ = G ∷ Ω₂} {Λ = Ω₀} {Ω = Ω₁}))
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ .(Ξ ++ B ⇐ A ∷ Δ₁ ++ F' ∷ Ω₂)) Λ {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Ξ)} {.(F' ∷ Ω₂ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , refl , refl) | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ξ , refl , refl) | inj₂ (.(B ⇐ A) , .(Δ₁ ++ F' ∷ Ω₂) , refl , refl)
  | refl , refl
  | inj₂ (F' , Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Ω₀ ++ E ∷ Ξ) (Δ₁ ++ F' ∷ Ω₂) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) (Γ₁ ++ A' ∷ B' ∷ Ω₀) (Δ₁ ++ F' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₁ (F' ∷ Ω₂) Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Ω₀ ++ E ∷ Ξ) (Δ₁ ++ F' ∷ Ω₂) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) (Γ₁ ++ A' ⊗ B' ∷ Ω₀) (Δ₁ ++ F' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₁ (F' ∷ Ω₂) Δ₁ Λ |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₀) Γ₁ (E ∷ Ξ ++ B ∷ F' ∷ Ω₂ ++ Λ) = intrp≗ refl
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl)
  | inj₂ (Ξ , eqa , eqb)
  with cases∷ Ξ eqa
... | inj₁ (refl , refl , eq4)
  with ++? Δ Δ₁ Λ Ω₁ (sym eq4)
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁) (.(B ⇐ A) ∷ .(Δ₁ ++ Ψ)) Λ {Γ₁} {Δ₁} {Λ₁} {.(Ψ ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(A' ⊗ B' ∷ Λ₁) , refl , refl) | inj₂ (Λ₁ , refl , refl)
  | inj₂ (.[] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ Ψ) (B ⇐ A) |
          ++?-inj₁ Ψ Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ Ψ) (B ⇐ A) |
          ++?-inj₁ Ψ Δ₁ Λ |
          ++?-inj₁ (A' ⊗ B' ∷ Λ₁) Γ₁ (B ∷ Ψ ++ Λ) = intrp≗ refl
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁) (.(B ⇐ A) ∷ Δ) .(F ∷ Ψ ++ Ω₁) {Γ₁} {.(Δ ++ F ∷ Ψ)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Λ₁) , refl , refl) | inj₂ (Λ₁ , refl , refl)
  | inj₂ (.[] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) Δ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ A' ∷ B' ∷ Λ₁) Δ (B ⇐ A) |
          ++?-inj₂ Δ Ψ Ω₁ F |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Δ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Δ (B ⇐ A) |
          ++?-inj₂ Δ Ψ Ω₁ F |
          ++?-inj₁ (A' ⊗ B' ∷ Λ₁) Γ₁ (B ∷ Ω₁) =
    intrp≗ (g~ (⊗L⇐L-comm₁ {Γ = Γ₁} {Δ = F ∷ Ψ} {Λ = Λ₁} {Ω = Ω₁}))
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl)
  | inj₂ (.(B ⇐ A ∷ Ξ) , eqa , eqb)
  | inj₂ (Ξ , eq4 , refl)
  with ++? Ξ Δ₁ (E ∷ Δ ++ Λ) Ω₁ eq4
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ψ) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {.(Ψ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ψ) , refl , refl) | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Δ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(Δ₁ ++ Ψ) , refl , refl)
  | inj₁ (Ψ , refl , refl)
  with Ψ
... | [] rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ E ∷ Δ) Λ (B ⇐ A) |
                 cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) Δ₁ (E ∷ Δ) (B ⇐ A) |
                 ++?-inj₁ (E ∷ Δ) Δ₁ Λ |
                 ++?-inj₁ [] Δ₁ (E ∷ Δ) |
                 cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ E ∷ Δ) Λ (B ⇐ A) |
                 cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Δ₁ (E ∷ Δ) (B ⇐ A) |
                 ++?-inj₁ (E ∷ Δ) Δ₁ Λ |
                 ++?-inj₁ [] Δ₁ (E ∷ Δ) |
                 ++?-inj₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ []) Γ₁ (E ∷ Δ ++ Λ) =
    intrp≗
      (g~
        ((~
          (⊗L⊗L {Γ = Γ₁} {Δ = Λ₁ ++ B ⇐ A ∷ Δ₁} {Λ = Λ} {A = A'} {B = B'}
            {A' = I} {B' = mip (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ B ∷ []) (E ∷ Δ) Λ g refl .MIP.D}))
        ∘ ⊗L {Γ = Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Δ₁}
            (⊗L⇐L-comm₁ {Γ = Γ₁} {Δ = Δ₁ ++ I ∷ []} {Λ = Λ₁})))
... | G ∷ Ω₂
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ G ∷ Ω₂ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ G ∷ Ω₂ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ G ∷ Ω₂) (E ∷ Δ) (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ G ∷ Ω₂) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (G ∷ Ω₂ ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ Ω₂ (E ∷ Δ) G |
          ++?-inj₁ (A' ⊗ B' ∷ Λ₁ ++ B ∷ G ∷ Ω₂) Γ₁ (E ∷ Δ ++ Λ) =
    intrp≗ (g~ (⊗L⇐L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁}))
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {.(Ξ ++ F ∷ Ψ)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(A' ⊗ B' ∷ Ω₀) , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl)
  | inj₂ (.(B ⇐ A ∷ Ξ) , eqa , eqb)
  | inj₂ (Ξ , eq4 , refl)
  | inj₂ (F , Ψ , refl , eq5)
  with inj∷ eq5
... | refl , eqd
  with ++? Δ Ψ Λ Ω₁ (sym eqd)
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Ξ) (E ∷ .(Ψ ++ Ω₃)) Λ {Γ₁} {.(Ξ ++ E ∷ Ψ)} {Λ₁} {.(Ω₃ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl) | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ξ) , refl , refl)
  | inj₂ (Ξ , refl , refl)
  | inj₂ (E , Ψ , refl , refl)
  | refl , refl
  | inj₁ (Ω₃ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Ξ ++ E ∷ Ψ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Ξ ++ E ∷ Ψ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Ξ (E ∷ Ψ ++ Ω₃) (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) Ξ (E ∷ Ψ ++ Ω₃) (B ⇐ A) |
          ++?-inj₁ Ω₃ (Ξ ++ E ∷ Ψ) Λ |
          ++?-inj₁ (E ∷ Ψ) Ξ Ω₃ =
    intrp≗
      (~-trans
        (g~
          ((~
            ⊗L⊗L {Γ = Γ₁} {Δ = Λ₁ ++ B ⇐ A ∷ Ξ} {Λ = Λ} {A = A'} {B = B'}
              {A' = mip Ξ (E ∷ Ψ) [] f refl .MIP.D}
              {B' = mip (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ B ∷ []) Ω₃ Λ g refl .MIP.D})
            ∘
            ⊗L {Γ = Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Ξ}
              (⊗L⇐L-comm₁ {Γ = Γ₁}
                {Δ = Ξ ++ mip Ξ (E ∷ Ψ) [] f refl .MIP.D ∷ []}
                {Λ = Λ₁}
                {Ω = mip (Γ₁ ++ A' ∷ B' ∷ Λ₁ ++ B ∷ []) Ω₃ Λ g refl .MIP.D ∷ Λ})))
        (⇐L~⊗ {Γ₀ = Γ₁ ++ A' ⊗ B' ∷ Λ₁} {Γ₁ = Ξ}
          {Δ₀ = E ∷ Ψ} {Δ₁ = Ω₃} {Λ = Λ}
          refl (~-sym (mip⊗L~Γ Γ₁ (Λ₁ ++ B ∷ []) Ω₃ Λ))))
mip≗⊗L⇐L-comm₁ .(Γ₁ ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Ξ) (E ∷ Δ) .(H ∷ Ω₃ ++ Ω₁)
  {Γ₁} {.(Ξ ++ E ∷ Δ ++ H ∷ Ω₃)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl) | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ξ) , refl , refl)
  | inj₂ (Ξ , refl , refl)
  | inj₂ (E , .(Δ ++ H ∷ Ω₃) , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₃ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) (Ξ ++ E ∷ Δ) (H ∷ Ω₃ ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) (Ξ ++ E ∷ Δ) (H ∷ Ω₃ ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ∷ B' ∷ Λ₁) Ξ (E ∷ Δ) (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ A' ⊗ B' ∷ Λ₁) Ξ (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ξ ++ E ∷ Δ) Ω₃ Ω₁ H =
    intrp≗
      (g~
        (⊗L⇐L-comm₁ {Γ = Γ₁}
          {Δ = Ξ ++ mip Ξ (E ∷ Δ) (H ∷ Ω₃) f refl .MIP.D ∷ H ∷ Ω₃}
          {Λ = Λ₁}
          {Ω = Ω₁}))
mip≗⊗L⇐L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₂ (F , Ω , refl , eq2)
  with cases++ Ω Δ (Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁) Λ (inj∷ eq2 .proj₂)
... | inj₁ (Ξ , eqa , eqb)
  with ++? Ξ Λ₁ Λ (B ⇐ A ∷ Δ₁ ++ Ω₁) eqb
... | inj₁ (Ψ , eqc , refl)
  with cases++ [] Ψ (Δ₁ ++ Ω₁) Λ (sym eqc)
... | inj₁ (Ψ₁ , refl , eqd)
  with ++? Δ₁ Ψ₁ Ω₁ Λ (sym eqd)
mip≗⊗L⇐L-comm₁ Γ (E ∷ .(Ω ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Ψ₁)) .(Ω₂ ++ Ω₁)
  {.(Γ ++ E ∷ Ω)} {.(Ψ₁ ++ Ω₂)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (.(Λ₁ ++ B ⇐ A ∷ Ψ₁) , refl , refl)
  | inj₁ (.(B ⇐ A ∷ Ψ₁) , refl , refl)
  | inj₁ (Ψ₁ , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω ++ A' ∷ B' ∷ Λ₁) Ψ₁ (Ω₂ ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω ++ A' ⊗ B' ∷ Λ₁) Ψ₁ (Ω₂ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ A' ∷ B' ∷ Λ₁) Γ Ψ₁ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ A' ⊗ B' ∷ Λ₁) Γ Ψ₁ (B ⇐ A)
  with Ω₂
... | []
  rewrite ++?-inj₁ [] Ψ₁ Ω₁ |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω (Λ₁ ++ B ∷ []) Ω₁ (A' ⊗ B') =
    intrp≗ (h~ (⊗L⇐L-comm₁ {Γ = E ∷ Ω} {Δ = Ψ₁} {Λ = Λ₁} {Ω = []}))
... | H ∷ Ω₃
  rewrite ++?-inj₂ Ψ₁ Ω₃ Ω₁ H |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω (Λ₁ ++ B ∷ []) Ω₁ (A' ⊗ B') =
    intrp≗
      (h~
        (⊗L⇐R ∘
          ⇐R
            (⊗L⇐L-comm₁ {Γ = E ∷ Ω}
              {Δ = Ψ₁ ++ mip Ψ₁ (H ∷ Ω₃) [] f refl .MIP.D ∷ []}
              {Λ = Λ₁} {Ω = []})))
mip≗⊗L⇐L-comm₁ Γ (E ∷ .(Ω ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ H ∷ Ω₂)) Λ
  {.(Γ ++ E ∷ Ω)} {Δ₁} {Λ₁} {.(H ∷ Ω₂ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (.(Λ₁ ++ B ⇐ A ∷ Δ₁ ++ H ∷ Ω₂) , refl , refl)
  | inj₁ (.(B ⇐ A ∷ Δ₁ ++ H ∷ Ω₂) , refl , refl)
  | inj₁ (.(Δ₁ ++ H ∷ Ω₂) , refl , refl)
  | inj₂ (H , Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ H ∷ Ω₂) Λ (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ H ∷ Ω₂) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ A' ∷ B' ∷ Λ₁) Γ (Δ₁ ++ H ∷ Ω₂) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ A' ⊗ B' ∷ Λ₁) Γ (Δ₁ ++ H ∷ Ω₂) (B ⇐ A) |
          ++?-inj₁ (H ∷ Ω₂) Δ₁ Λ |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Λ₁ ++ B ∷ H ∷ Ω₂ ++ Λ) E |
          cases++-inj₁ Ω (Λ₁ ++ B ∷ H ∷ Ω₂) Λ (A' ⊗ B') =
    intrp≗ (h~ (⊗L⇐L-comm₁ {Γ = E ∷ Ω} {Δ = Δ₁} {Λ = Λ₁} {Ω = H ∷ Ω₂}))
mip≗⊗L⇐L-comm₁ Γ (E ∷ .(Ω ++ A' ⊗ B' ∷ Λ₁)) .(B ⇐ A ∷ Δ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Ω)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Λ₁ , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ [] (Γ ++ E ∷ Ω ++ A' ∷ B' ∷ Λ₁) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ ++ E ∷ Ω ++ A' ⊗ B' ∷ Λ₁) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Λ₁ (B ∷ Ω₁) (A' ⊗ B') = intrp≗ refl
mip≗⊗L⇐L-comm₁ Γ (E ∷ .(Ω ++ A' ⊗ B' ∷ Ξ)) .(G ∷ Ψ ++ B ⇐ A ∷ Δ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Ω)} {Δ₁} {.(Ξ ++ G ∷ Ψ)} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₂ (G , Ψ , refl , refl)
  rewrite cases++-inj₂ (G ∷ Ψ) (Γ ++ E ∷ Ω ++ A' ∷ B' ∷ Ξ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (G ∷ Ψ) (Γ ++ E ∷ Ω ++ A' ⊗ B' ∷ Ξ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₂ Γ Ω (A' ⊗ B' ∷ Ξ ++ G ∷ Ψ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Ξ (G ∷ Ψ ++ B ∷ Ω₁) (A' ⊗ B') = intrp≗ refl
mip≗⊗L⇐L-comm₁ Γ (E ∷ Δ) .(Ξ ++ A' ⊗ B' ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Δ ++ Ξ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Δ ++ Ξ) , refl , refl)
  | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₂ (Ξ ++ A' ∷ B' ∷ Λ₁) (Γ ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (Ξ ++ A' ⊗ B' ∷ Λ₁) (Γ ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₂ Γ (Δ ++ Ξ) (A' ⊗ B' ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₂ Ξ Δ (Λ₁ ++ B ∷ Ω₁) (A' ⊗ B') =
    intrp≗
      (g~
        (⊗L⇐L-comm₁
          {Γ = Γ ++ mip Γ (E ∷ Δ) (Ξ ++ A' ∷ B' ∷ Λ₁ ++ B ∷ Ω₁) g refl .MIP.D ∷ Ξ}
          {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁}))
