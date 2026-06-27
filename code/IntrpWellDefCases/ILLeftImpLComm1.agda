{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILLeftImpLComm1 where

open import IntrpWellDefCases.Base

mip≗IL⇐L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ Λ₁ ++ B ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁} {Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁} (⇐L {Γ₁ ++ Λ₁} {Δ₁} {Ω₁} f g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁ ++ I ∷ Λ₁} {Δ₁} {Ω₁} f (IL {Γ₁} {Λ₁ ++ B ∷ Ω₁} g)) eq)
mip≗IL⇐L-comm₁ Γ [] Λ eq = mip[]≗ Γ Λ eq IL⇐L-comm₁
mip≗IL⇐L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (I ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁) eq
... | inj₁ (Ω , eq1 , refl)
  with cases∷ Ω eq1
... | inj₁ (refl , refl , eq3)
  with cases++ Λ₁ Δ (Δ₁ ++ Ω₁) Λ eq3
... | inj₁ (Ξ , refl , eq4)
  with ++? Δ₁ Ξ Ω₁ Λ (sym eq4)
mip≗IL⇐L-comm₁ Γ₁ (I ∷ .([] ++ B ⇐ A ∷ Ξ)) .Ω₁
  {Γ₁} {.Ξ} {[]} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ I ∷ []) Ξ Ω₁ (B ⇐ A) |
          cases++-inj₂ (I ∷ []) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₁ [] Ξ Ω₁ |
          ++?-inj₁ [] Γ₁ (I ∷ [] ++ B ∷ Ω₁) |
          cases++-inj₁ Γ₁ Ξ Ω₁ (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Ξ (B ⇐ A) |
          ++?-inj₁ [] Ξ Ω₁ =
    intrp≗ (h~ IL⇐L-comm₁)
mip≗IL⇐L-comm₁ Γ₁ (I ∷ .((F ∷ Λ₁) ++ B ⇐ A ∷ Ξ)) .Ω₁
  {Γ₁} {.Ξ} {F ∷ Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ I ∷ F ∷ Λ₁) Ξ Ω₁ (B ⇐ A) |
          cases++-inj₂ (I ∷ F ∷ Λ₁) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₁ [] Ξ Ω₁ |
          ++?-inj₁ [] Γ₁ (I ∷ F ∷ Λ₁ ++ B ∷ Ω₁) |
          cases++-inj₁ (Γ₁ ++ F ∷ Λ₁) Ξ Ω₁ (B ⇐ A) |
          cases++-inj₂ (F ∷ Λ₁) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₁ [] Ξ Ω₁ =
    intrp≗ (h~ IL⇐L-comm₁)
mip≗IL⇐L-comm₁ Γ₁ (I ∷ .([] ++ B ⇐ A ∷ Ξ)) .(F ∷ Ψ ++ Ω₁)
  {Γ₁} {.(Ξ ++ F ∷ Ψ)} {[]} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₁ (F ∷ Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ I ∷ []) Ξ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (I ∷ []) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₂ Ξ Ψ Ω₁ F |
          ++?-inj₁ [] Γ₁ (I ∷ [] ++ B ∷ Ω₁) |
          cases++-inj₁ Γ₁ Ξ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Ξ (B ⇐ A) |
          ++?-inj₂ Ξ Ψ Ω₁ F =
    intrp≗ (h~ (IL⇐R ∘ ⇐R IL⇐L-comm₁))
mip≗IL⇐L-comm₁ Γ₁ (I ∷ .((G ∷ Λ₁) ++ B ⇐ A ∷ Ξ)) .(F ∷ Ψ ++ Ω₁)
  {Γ₁} {.(Ξ ++ F ∷ Ψ)} {G ∷ Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₁ (F ∷ Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ I ∷ G ∷ Λ₁) Ξ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (I ∷ G ∷ Λ₁) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₂ Ξ Ψ Ω₁ F |
          ++?-inj₁ [] Γ₁ (I ∷ G ∷ Λ₁ ++ B ∷ Ω₁) |
          cases++-inj₁ (Γ₁ ++ G ∷ Λ₁) Ξ (F ∷ Ψ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (G ∷ Λ₁) Γ₁ Ξ (B ⇐ A) |
          ++?-inj₂ Ξ Ψ Ω₁ F =
    intrp≗ (h~ (IL⇐R ∘ ⇐R IL⇐L-comm₁))
mip≗IL⇐L-comm₁ Γ₁ (I ∷ .([] ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ψ)) Λ
  {Γ₁} {Δ₁} {[]} {.(F ∷ Ψ ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ψ) , refl , refl)
  | inj₂ (F , Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ I ∷ []) (Δ₁ ++ F ∷ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ (I ∷ []) Γ₁ (Δ₁ ++ F ∷ Ψ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ψ) Δ₁ Λ |
          ++?-inj₁ [] Γ₁ (I ∷ [] ++ B ∷ F ∷ Ψ ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Δ₁ ++ F ∷ Ψ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ψ) Δ₁ Λ =
    intrp≗ (h~ IL⇐L-comm₁)
mip≗IL⇐L-comm₁ Γ₁ (I ∷ .((G ∷ Λ₁) ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ψ)) Λ
  {Γ₁} {Δ₁} {G ∷ Λ₁} {.(F ∷ Ψ ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ψ) , refl , refl)
  | inj₂ (F , Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ I ∷ G ∷ Λ₁) (Δ₁ ++ F ∷ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ (I ∷ G ∷ Λ₁) Γ₁ (Δ₁ ++ F ∷ Ψ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ψ) Δ₁ Λ |
          ++?-inj₁ [] Γ₁ (I ∷ G ∷ Λ₁ ++ B ∷ F ∷ Ψ ++ Λ) |
          cases++-inj₁ (Γ₁ ++ G ∷ Λ₁) (Δ₁ ++ F ∷ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ (G ∷ Λ₁) Γ₁ (Δ₁ ++ F ∷ Ψ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ψ) Δ₁ Λ =
    intrp≗ (h~ IL⇐L-comm₁)
mip≗IL⇐L-comm₁ Γ₁ (I ∷ Δ) .(Ξ ++ B ⇐ A ∷ Δ₁ ++ Ω₁)
  {Γ₁} {Δ₁} {.(Δ ++ Ξ)} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₂ Ξ (Γ₁ ++ I ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₁ [] Γ₁ (I ∷ Δ ++ Ξ ++ B ∷ Ω₁) =
    intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⇐L~Λ Γ₁ Δ Ξ Ω₁))
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} eq
  | inj₁ (.(I ∷ Ω') , eq1 , refl)
  | inj₂ (Ω' , eq3 , refl)
  with cases++ Λ₁ Ω' (Δ₁ ++ Ω₁) (E ∷ Δ ++ Λ) (sym eq3)
... | inj₁ (Ξ , refl , eq4)
  with ++? Δ₁ Ξ Ω₁ (E ∷ Δ ++ Λ) (sym eq4)
... | inj₁ (Ψ , eq5 , refl)
  with cases++ [] Ψ (Δ ++ Λ) Ω₁ (sym eq5)
... | inj₁ (Ω'' , refl , eq6)
  with ++? Δ Ω'' Λ Ω₁ (sym eq6)
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) (E ∷ Δ) Λ
  {Γ₁} {.(Ξ ++ E ∷ Ω'')} {Λ₁} {.(Ω''' ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₁ (.(E ∷ Ω'') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Λ₁) (Ξ ++ E ∷ Ω'' ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ Λ₁) Ξ (E ∷ Ω'' ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' (Ξ ++ E ∷ Ω'') Λ |
          ++?-inj₁ (E ∷ Ω'') Ξ Ω''' |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) (Ξ ++ E ∷ Ω'' ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) Ξ (E ∷ Ω'' ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' (Ξ ++ E ∷ Ω'') Λ |
          ++?-inj₁ (E ∷ Ω'') Ξ Ω''' =
    intrp≗
      (~-trans
        (g~ (IL⊗L-comm₁ {Γ = Γ₁} {Δ = Λ₁ ++ B ⇐ A ∷ Ξ} {Λ = Λ} ∘
             ⊗L {Γ = Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Ξ} IL⇐L-comm₁))
        (~-sym
          (⇐L~⊗ {Γ₀ = Γ₁ ++ I ∷ Λ₁} {Γ₁ = Ξ}
            {Δ₀ = E ∷ Ω''} {Δ₁ = Ω'''} {Λ = Λ} {A = A} {B = B}
            refl (mipIL~Γ Γ₁ (Λ₁ ++ B ∷ []) Ω''' Λ {f = g}))))
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) (E ∷ Δ) .(G ∷ Ω''' ++ Ω₁)
  {Γ₁} {.(Ξ ++ E ∷ Δ ++ G ∷ Ω''')} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₁ (.(E ∷ Δ ++ G ∷ Ω''') , refl , refl)
  | inj₁ (.(Δ ++ G ∷ Ω''') , refl , refl)
  | inj₂ (G , Ω''' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Λ₁) (Ξ ++ E ∷ Δ) (G ∷ Ω''' ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ Λ₁) Ξ (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ξ ++ E ∷ Δ) Ω''' Ω₁ G |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) (Ξ ++ E ∷ Δ) (G ∷ Ω''' ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) Ξ (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ξ ++ E ∷ Δ) Ω''' Ω₁ G =
    intrp≗ (g~ (IL⇐L-comm₁ {Γ = Γ₁} {Λ = Λ₁}))
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) (E ∷ Δ) Λ
  {Γ₁} {.Ξ} {Λ₁} {.(E ∷ Δ ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Ξ) , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Λ₁) (Ξ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ Λ₁) Ξ (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) Ξ Λ |
          ++?-inj₁ [] Ξ (E ∷ Δ) |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) (Ξ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) Ξ (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) Ξ Λ |
          ++?-inj₁ [] Ξ (E ∷ Δ) |
          ++?-inj₁ (I ∷ Λ₁ ++ B ∷ []) Γ₁ (E ∷ Δ ++ Λ) =
    intrp≗
      (g~ (IL⊗L-comm₁ {Γ = Γ₁} {Δ = Λ₁ ++ B ⇐ A ∷ Ξ} {Λ = Λ} ∘
           ⊗L {Γ = Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Ξ}
             (IL⇐L-comm₁ {Γ = Γ₁} {Λ = Λ₁})))
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) (E ∷ Δ) Λ
  {Γ₁} {.(Ξ ++ Ψ)} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} eq
  | inj₁ (.(I ∷ Λ₁ ++ B ⇐ A ∷ Ξ) , eq1 , refl)
  | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Ξ) , eq3 , refl)
  | inj₁ (Ξ , refl , eq4)
  | inj₁ (Ψ , eq5 , refl)
  | inj₂ (x ∷ Ω'' , eq6 , eq7)
  with []disj∷ Ψ eq7
... | ()
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ψ) (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(F ∷ Ψ ++ E ∷ Δ ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Λ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ψ) , refl , refl)
  | inj₂ (.(Λ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ψ) , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ψ) , refl , refl)
  | inj₂ (F , Ψ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Λ₁) (Δ₁ ++ F ∷ Ψ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ Λ₁) (Δ₁ ++ F ∷ Ψ) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ψ ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ Ψ (E ∷ Δ) F |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) (Δ₁ ++ F ∷ Ψ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₁ ++ I ∷ Λ₁) (Δ₁ ++ F ∷ Ψ) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ψ ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ Ψ (E ∷ Δ) F |
          ++?-inj₁ (I ∷ Λ₁ ++ B ∷ F ∷ Ψ) Γ₁ (E ∷ Δ ++ Λ) =
    intrp≗ (g~ (IL⇐L-comm₁ {Γ = Γ₁} {Λ = Λ₁}))
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ Ξ)} {Ω₁} {A} {B} {C} {f = f} {g} eq
  | inj₁ (.(I ∷ Ω') , eq1 , refl)
  | inj₂ (Ω' , eq3 , refl)
  | inj₂ (Ξ , eq4 , refl)
  with cases∷ Ξ eq4
... | inj₁ (refl , refl , eΔ)
  with ++? Δ Δ₁ Λ Ω₁ eΔ
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (.(B ⇐ A) ∷ .(Δ₁ ++ Ω'')) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ [])} {.(Ω'' ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Ω') (Δ₁ ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ Ω') (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ I ∷ Ω') (Δ₁ ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ I ∷ Ω') (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ Λ |
          ++?-inj₁ (I ∷ Ω') Γ₁ (B ∷ Ω'' ++ Λ) =
    intrp≗ refl
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (.(B ⇐ A) ∷ Δ) .(F ∷ Ω'' ++ Ω₁)
  {Γ₁} {.(Δ ++ F ∷ Ω'')} {.(Ω' ++ [])} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Ω') Δ (F ∷ Ω'' ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ Ω') Δ (B ⇐ A) |
          ++?-inj₂ Δ Ω'' Ω₁ F |
          cases++-inj₁ (Γ₁ ++ I ∷ Ω') Δ (F ∷ Ω'' ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ I ∷ Ω') Δ (B ⇐ A) |
          ++?-inj₂ Δ Ω'' Ω₁ F |
          ++?-inj₁ (I ∷ Ω') Γ₁ (B ∷ Ω₁) =
    intrp≗ (g~ IL⇐L-comm₁)
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ Ξ)} {Ω₁} {A} {B} {C} {f = f} {g} eq
  | inj₁ (.(I ∷ Ω') , eq1 , refl)
  | inj₂ (Ω' , eq3 , refl)
  | inj₂ (Ξ , eq4 , refl)
  | inj₂ (Ξ' , eq4' , refl)
  with ++? Δ Ξ' Λ (B ⇐ A ∷ Δ₁ ++ Ω₁) (sym eq4')
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) .(B ⇐ A ∷ Δ₁ ++ Ω₁)
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ)} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(E ∷ Δ) , refl , refl)
  | inj₂ (Δ , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ [] (Γ₁ ++ Ω' ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ₁ ++ I ∷ Ω' ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Δ ++ B ∷ Ω₁) =
    intrp≗ (g~ (IL⇐L-comm₁
      {Γ = Γ₁}
      {Λ = Ω' ++ MIP.D (mip (Γ₁ ++ Ω') (E ∷ Δ) (B ∷ Ω₁) g refl) ∷ []}))
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ Δ) .(F ∷ Ψ ++ B ⇐ A ∷ Δ₁ ++ Ω₁)
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Δ ++ F ∷ Ψ)} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(E ∷ Δ ++ F ∷ Ψ) , refl , refl)
  | inj₂ (.(Δ ++ F ∷ Ψ) , refl , refl)
  | inj₂ (F , Ψ , refl , refl)
  rewrite cases++-inj₂ (F ∷ Ψ) (Γ₁ ++ Ω' ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (F ∷ Ψ) (Γ₁ ++ I ∷ Ω' ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Δ ++ F ∷ Ψ ++ B ∷ Ω₁) =
    intrp≗ (g~ (IL⇐L-comm₁
      {Γ = Γ₁}
      {Λ = Ω' ++ MIP.D (mip (Γ₁ ++ Ω') (E ∷ Δ) (F ∷ Ψ ++ B ∷ Ω₁) g refl) ∷ F ∷ Ψ}))
... | inj₁ (G ∷ Ψ' , eq5 , refl)
  with inj∷ eq5
... | refl , eq6
  with ++? Ψ' Δ₁ Λ Ω₁ eq6
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ .(Ξ' ++ B ⇐ A ∷ Ψ')) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Ξ')} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , eq3 , refl)
  | inj₂ (.(E ∷ Ξ') , eq4 , refl)
  | inj₂ (Ξ' , eq4' , refl)
  | inj₁ (.(B ⇐ A) ∷ Ψ' , eq5 , refl)
  | refl , eq6
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Ω' ++ E ∷ Ξ') (Δ₁ ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ') (Γ₁ ++ Ω') (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ I ∷ Ω' ++ E ∷ Ξ') (Δ₁ ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ') (Γ₁ ++ I ∷ Ω') (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ Λ |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Ξ' ++ B ∷ Ω'' ++ Λ) =
    intrp≗ refl
mip≗IL⇐L-comm₁ .(Γ₁ ++ I ∷ Ω') (E ∷ .(Ξ' ++ B ⇐ A ∷ Ψ')) Λ
  {Γ₁} {Δ₁} {.(Ω' ++ E ∷ Ξ')} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₁ (.(I ∷ Ω') , refl , refl)
  | inj₂ (Ω' , eq3 , refl)
  | inj₂ (.(E ∷ Ξ') , eq4 , refl)
  | inj₂ (Ξ' , eq4' , refl)
  | inj₁ (.(B ⇐ A) ∷ Ψ' , eq5 , refl)
  | refl , eq6
  | inj₂ (F , Ω'' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Ω' ++ E ∷ Ξ') Ψ' (F ∷ Ω'' ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ') (Γ₁ ++ Ω') Ψ' (B ⇐ A) |
          ++?-inj₂ Ψ' Ω'' Ω₁ F |
          cases++-inj₁ (Γ₁ ++ I ∷ Ω' ++ E ∷ Ξ') Ψ' (F ∷ Ω'' ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ') (Γ₁ ++ I ∷ Ω') Ψ' (B ⇐ A) |
          ++?-inj₂ Ψ' Ω'' Ω₁ F |
          ++?-inj₁ (I ∷ Ω') Γ₁ (E ∷ Ξ' ++ B ∷ Ω₁) =
          intrp≗ (g~ (IL⇐L-comm₁
            {Γ = Γ₁}
            {Λ = Ω'}))
mip≗IL⇐L-comm₁ Γ (E ∷ Δ) Λ {.(Γ ++ F ∷ Ω)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} eq
  | inj₂ (F , Ω , refl , eq2)
  with cases++ Ω Δ (Λ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₁) Λ (inj∷ eq2 .proj₂)
... | inj₁ (Ξ , eqa , eqb)
  with ++? Ξ Λ₁ Λ (B ⇐ A ∷ Δ₁ ++ Ω₁) eqb
mip≗IL⇐L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Λ₁)) .(B ⇐ A ∷ Δ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Ω)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Λ₁ , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ [] (Γ ++ E ∷ Ω ++ Λ₁) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ ++ E ∷ Ω ++ I ∷ Λ₁) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₂ Γ Ω (I ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Λ₁ (B ∷ Ω₁) I = intrp≗ refl
... | inj₁ (G ∷ Ψ' , eqc , refl)
  with inj∷ eqc
... | refl , eqd
  with ++? Δ₁ Ψ' Ω₁ Λ (sym eqd)
mip≗IL⇐L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Λ₁ ++ B ⇐ A ∷ Ψ')) .(Ω' ++ Ω₁)
  {.(Γ ++ E ∷ Ω)} {.(Ψ' ++ Ω')} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (.(Λ₁ ++ B ⇐ A ∷ Ψ') , refl , refl)
  | inj₁ (B ⇐ A ∷ Ψ' , refl , refl)
  | refl , refl
  | inj₁ (Ω' , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω ++ Λ₁) Ψ' (Ω' ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω ++ I ∷ Λ₁) Ψ' (Ω' ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ Λ₁) Γ Ψ' (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ I ∷ Λ₁) Γ Ψ' (B ⇐ A)
  with Ω'
... | [] rewrite ++?-inj₁ [] Ψ' Ω₁ |
                 ++?-inj₂ Γ Ω (I ∷ Λ₁ ++ B ∷ Ω₁) E |
                 cases++-inj₁ Ω (Λ₁ ++ B ∷ []) Ω₁ I =
                 intrp≗ (h~ (IL⇐L-comm₁ {Γ = E ∷ Ω} {Λ = Λ₁}))
... | H ∷ Ω'' rewrite ++?-inj₂ Ψ' Ω'' Ω₁ H |
                       ++?-inj₂ Γ Ω (I ∷ Λ₁ ++ B ∷ Ω₁) E |
                       cases++-inj₁ Ω (Λ₁ ++ B ∷ []) Ω₁ I =
                       intrp≗ (h~ (IL⇐R ∘ ⇐R (IL⇐L-comm₁ {Γ = E ∷ Ω} {Λ = Λ₁})))
mip≗IL⇐L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Λ₁ ++ ((B ⇐ A) ∷ (Δ₁ ++ (H ∷ Ω'))))) Λ
  {.(Γ ++ E ∷ Ω)} {Δ₁} {Λ₁} {.(H ∷ Ω' ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (.(Λ₁ ++ ((B ⇐ A) ∷ (Δ₁ ++ (H ∷ Ω')))) , refl , refl)
  | inj₁ (.((B ⇐ A) ∷ (Δ₁ ++ (H ∷ Ω'))) , refl , refl)
  | refl , refl
  | inj₂ (H , Ω' , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω ++ Λ₁) (Δ₁ ++ H ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω ++ I ∷ Λ₁) (Δ₁ ++ H ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ Λ₁) Γ (Δ₁ ++ H ∷ Ω') (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω ++ I ∷ Λ₁) Γ (Δ₁ ++ H ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (H ∷ Ω') Δ₁ Λ |
          ++?-inj₂ Γ Ω (I ∷ Λ₁ ++ B ∷ H ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω (Λ₁ ++ B ∷ H ∷ Ω') Λ I =
          intrp≗ (h~ (IL⇐L-comm₁ {Γ = E ∷ Ω} {Λ = Λ₁}))
mip≗IL⇐L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Ξ)) .(G ∷ Ψ ++ (B ⇐ A) ∷ Δ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Ω)} {Δ₁} {.(Ξ ++ G ∷ Ψ)} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₂ (G , Ψ , refl , refl)
  rewrite cases++-inj₂ (G ∷ Ψ) (Γ ++ E ∷ Ω ++ Ξ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (G ∷ Ψ) (Γ ++ E ∷ Ω ++ I ∷ Ξ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₂ Γ Ω (I ∷ Ξ ++ G ∷ Ψ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Ξ (G ∷ Ψ ++ B ∷ Ω₁) I = intrp≗ refl
mip≗IL⇐L-comm₁ Γ (E ∷ Δ) .(Ξ ++ I ∷ Λ₁ ++ (B ⇐ A) ∷ Δ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Δ ++ Ξ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ Ξ) , refl , refl)
  | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₂ (Ξ ++ Λ₁) (Γ ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (Ξ ++ I ∷ Λ₁) (Γ ++ E ∷ Δ) (Δ₁ ++ Ω₁) (B ⇐ A) |
          ++?-inj₂ Γ (Δ ++ Ξ) (I ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₂ Ξ Δ (Λ₁ ++ B ∷ Ω₁) I =
          intrp≗ (g~ (IL⇐L-comm₁
            {Γ = Γ ++ MIP.D (mip Γ (E ∷ Δ) (Ξ ++ Λ₁ ++ B ∷ Ω₁) g refl) ∷ Ξ}
            {Λ = Λ₁}))
