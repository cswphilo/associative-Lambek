{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILImpLComm1 where

open import IntrpWellDefCases.Base
open import IntrpWellDefCases.ImpLImpLAssoc using (mip⇒L~Λ∷)

IL⇒L⊗R-seed : ∀ Γ Δ Λ {A B C : Fma}
  {f : Δ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
  → IL (⇒L f g) ≗
      cut Γ (IL {[]} {[]} (⊗R IR IR))
        (⊗L {Γ} {Δ ++ A ⇒ B ∷ Λ}
          (⇒L {Γ ++ I ∷ []} {I ∷ Δ} {Λ}
            (IL {[]} {Δ} f) (IL {Γ} {B ∷ Λ} g))) refl
IL⇒L⊗R-seed Γ Δ Λ {A} {B}
  rewrite cases++-inj₂ [] Γ (Δ ++ A ⇒ B ∷ Λ) (I ⊗ I) |
          cases++-inj₁ (Γ ++ I ∷ []) Δ (A ⇒ B ∷ Λ) I |
          cases++-inj₂ [] (Γ ++ I ∷ []) Δ I |
          cases++-inj₁ Γ Δ (A ⇒ B ∷ Λ) I |
          cases++-inj₁ Γ [] Δ I |
          cases++-inj₂ [] Γ (B ∷ Λ) I = refl

cut⊗RIR⊗L⇒L : ∀ Γ Δ Λ {A B C D : Fma}
  {f : D ∷ Δ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
  → ⇒L {Γ} {D ∷ Δ} {Λ} f g ≗
      cut Γ (⊗R IR ax)
        (⊗L {Γ} {Δ ++ A ⇒ B ∷ Λ}
          (⇒L {Γ ++ I ∷ []} {D ∷ Δ} {Λ}
            f (IL {Γ} {B ∷ Λ} g))) refl
cut⊗RIR⊗L⇒L Γ Δ Λ {A} {B} {C} {D} {f = f} {g}
  rewrite cases++-inj₂ [] Γ (Δ ++ A ⇒ B ∷ Λ) (I ⊗ D) |
          cases++-inj₁ (Γ ++ I ∷ []) Δ (A ⇒ B ∷ Λ) D |
          cases++-inj₂ [] (Γ ++ I ∷ []) Δ D |
          cases++-inj₁ Γ (D ∷ Δ) (A ⇒ B ∷ Λ) I |
          cases++-inj₁ Γ [] (D ∷ Δ) I |
          cases++-inj₂ [] Γ (B ∷ Λ) I =
    ⇒L (~ cutaxA-left [] f refl) refl

mip⇒L~⊗midΓ : ∀ Γ Γ₀ Δ₀ Δ₁ Λ
  {A B C : Fma}
  {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ ++ Γ₀ ++ B ∷ Λ ⊢ C}
  → mip Γ (Γ₀ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Λ)
      (⇒L {Γ ++ Γ₀} {Δ₀ ++ Δ₁} {Λ} f g) refl
      ~ ⇒L~⊗' (mip [] Δ₀ Δ₁ f refl) (mip Γ Γ₀ (B ∷ Λ) g refl)
mip⇒L~⊗midΓ Γ [] [] [] Λ {A} {B} {f = f} {g} =
  ↝∷ (IL {[]} {[]} (⊗R IR IR) , IL⇒L⊗R-seed Γ [] Λ , refl) refl
mip⇒L~⊗midΓ Γ [] [] (E ∷ Δ₁) Λ {f = f} {g} =
  ↝∷ (IL {[]} {[]} (⊗R IR IR) , IL⇒L⊗R-seed Γ (E ∷ Δ₁) Λ , refl) refl
mip⇒L~⊗midΓ Γ [] (D ∷ Δ₀) Δ₁ Λ {A} {B} {f = f} {g}
  rewrite ++?-inj₂ Γ (Δ₀ ++ Δ₁) (A ⇒ B ∷ Λ) D |
          cases++-inj₂ [] Γ (Δ₀ ++ Δ₁) D |
          cases++-inj₂ Δ₁ Δ₀ Λ (A ⇒ B) =
    ↝∷ (⊗R IR ax , cut⊗RIR⊗L⇒L Γ Δ₁ Λ , refl) refl
mip⇒L~⊗midΓ Γ (H ∷ Γ₀) Δ₀ Δ₁ Λ {A} {B} {f = f} {g}
  rewrite ++?-inj₂ Γ (Γ₀ ++ Δ₀ ++ Δ₁) (A ⇒ B ∷ Λ) H |
          cases++-inj₁ Γ Γ₀ (Δ₀ ++ Δ₁) H |
          cases++-inj₂ Δ₁ (Γ₀ ++ Δ₀) Λ (A ⇒ B) |
          ++?-inj₁ Δ₀ Γ₀ Δ₁ = refl

mip≗IL⇒L-comm₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ Λ₁ ++ B ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ I ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁} {Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁} (⇒L {Γ₁ ++ Λ₁} f g)) eq)
      (mip Γ Δ Λ (⇒L {Γ₁ ++ I ∷ Λ₁} f (IL {Γ₁} {Λ₁ ++ B ∷ Ω₁} g)) eq)
mip≗IL⇒L-comm₁ Γ [] Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} eq = mip[]≗ Γ Λ eq IL⇒L-comm₁

mip≗IL⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} eq
  with ++? Γ Γ₁ (E ∷ Δ ++ Λ) (I ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) eq
... | inj₁ (Ω , eq1 , refl)
  with cases∷ Ω eq1
... | inj₁ (refl , refl , eq3)
  with cases++ (Λ₁ ++ Δ₁) Δ Ω₁ Λ eq3
mip≗IL⇒L-comm₁ Γ₁ (I ∷ .([] ++ [] ++ A ⇒ B ∷ Ξ)) Λ {Γ₁} {[]} {[]} {.(Ξ ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₂ Γ₁ ([] ++ []) (A ⇒ B ∷ Ξ ++ Λ) I |
          cases++-inj₁ Γ₁ [] [] I |
          cases++-inj₁ ([] ++ []) Ξ Λ (A ⇒ B) |
          ++?-inj₁ [] Γ₁ (I ∷ [] ++ B ∷ Ξ ++ Λ) |
          ++?-inj₁ [] Γ₁ (A ⇒ B ∷ Ξ ++ Λ) =
    let G = mip Γ₁ (B ∷ Ξ) Λ g refl
        t : (I ⇒ MIP.D G) ∷ [] ⊢ MIP.D G
        t = ⇒L {[]} {[]} {[]} IR ax
    in intrp≗
      (↝∷ (t ,
        (~ (cut⇒L≗ Γ₁ IR ax (MIP.g G) refl
            ∘ ⇒L refl (cutaxA-left Γ₁ (MIP.g G) refl))) ,
        IL⇒L-comm₁ {Γ = []} {Δ = []} {Λ = []} {Ω = Ξ}) refl)
mip≗IL⇒L-comm₁ Γ₁ (I ∷ .([] ++ (D ∷ Δ₀) ++ A ⇒ B ∷ Ξ)) Λ {Γ₁} {D ∷ Δ₀} {[]} {.(Ξ ++ Λ)} {A} {B} {C} {f = f} {g} refl
  | inj₁ ([] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₂ Γ₁ ([] ++ (D ∷ Δ₀)) (A ⇒ B ∷ Ξ ++ Λ) I |
          cases++-inj₁ Γ₁ [] (D ∷ Δ₀) I |
          cases++-inj₁ ([] ++ (D ∷ Δ₀)) Ξ Λ (A ⇒ B) |
          ++?-inj₁ [] Γ₁ (I ∷ [] ++ B ∷ Ξ ++ Λ) |
          ++?-inj₂ Γ₁ Δ₀ (A ⇒ B ∷ Ξ ++ Λ) D |
          cases++-inj₂ [] Γ₁ Δ₀ D |
          cases++-inj₁ Δ₀ Ξ Λ (A ⇒ B) =
    let G = mip Γ₁ (B ∷ Ξ) Λ g refl
        t : (I ⇒ MIP.D G) ∷ [] ⊢ MIP.D G
        t = ⇒L {[]} {[]} {[]} IR ax
    in intrp≗
      (↝∷ (t ,
        (~ (cut⇒L≗ Γ₁ IR ax (MIP.g G) refl
            ∘ ⇒L refl (cutaxA-left Γ₁ (MIP.g G) refl))) ,
        IL⇒L-comm₁ {Γ = []} {Δ = D ∷ Δ₀} {Λ = []} {Ω = Ξ}) refl)
mip≗IL⇒L-comm₁ Γ₁ (I ∷ .((F ∷ Ψ) ++ Δ₁ ++ A ⇒ B ∷ Ξ)) Λ {Γ₁} {Δ₁} {F ∷ Ψ} {.(Ξ ++ Λ)} {A} {B} {C} refl
  | inj₁ ([] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₂ Γ₁ ((F ∷ Ψ) ++ Δ₁) (A ⇒ B ∷ Ξ ++ Λ) I |
          cases++-inj₁ Γ₁ (F ∷ Ψ) Δ₁ I |
          cases++-inj₁ ((F ∷ Ψ) ++ Δ₁) Ξ Λ (A ⇒ B) |
          ++?-inj₁ [] Γ₁ (I ∷ (F ∷ Ψ) ++ B ∷ Ξ ++ Λ) |
          ++?-inj₂ Γ₁ (Ψ ++ Δ₁) (A ⇒ B ∷ Ξ ++ Λ) F |
          cases++-inj₁ Γ₁ Ψ Δ₁ F |
          cases++-inj₁ (Ψ ++ Δ₁) Ξ Λ (A ⇒ B) =
    intrp≗ (h~ (IL⇒L-comm₁ {Γ = []} {Δ = Δ₁} {Λ = F ∷ Ψ} {Ω = Ξ}))
... | inj₂ (Ξ , refl , eqb)
  with ++? Δ Λ₁ Ξ Δ₁ eqb
mip≗IL⇒L-comm₁ Γ₁ (I ∷ .(Λ₁ ++ Ψ)) .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {.(Ψ ++ Ξ)} {Λ₁} {Ω₁} {A} {B} {C} refl
  | inj₁ ([] , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (Ξ , refl , refl) | inj₁ (Ψ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (Λ₁ ++ Ψ ++ Ξ) (A ⇒ B ∷ Ω₁) I |
          cases++-inj₁ Γ₁ Λ₁ (Ψ ++ Ξ) I |
          cases++-inj₂ Ξ (Λ₁ ++ Ψ) Ω₁ (A ⇒ B) |
          ++?-inj₁ Ψ Λ₁ Ξ |
          ++?-inj₁ [] Γ₁ (I ∷ Λ₁ ++ B ∷ Ω₁) =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = []} {Δ₁ = Λ₁ ++ Ψ}
          (mip⇒L~⊗midΓ Γ₁ Λ₁ Ψ Ξ Ω₁))
        (h~ (IL⊗R₁ {Γ = []} {Δ = Λ₁} {Λ = Ψ})))
mip≗IL⇒L-comm₁ Γ₁ (I ∷ Δ) .(Ξ ++ A ⇒ B ∷ Ω₁) {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} refl
  | inj₁ ([] , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (Ξ , refl , refl) | inj₂ (G , Ψ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (Δ ++ G ∷ Ψ ++ Δ₁) (A ⇒ B ∷ Ω₁) I |
          cases++-inj₁ Γ₁ (Δ ++ G ∷ Ψ) Δ₁ I |
          cases++-inj₂ (G ∷ Ψ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Ψ Δ₁ G |
          ++?-inj₁ [] Γ₁ (I ∷ Δ ++ G ∷ Ψ ++ B ∷ Ω₁) =
    intrp≗
      (IL~Δ {Δ₀ = []} {Δ₁ = Δ}
        (mip⇒L~Λ∷ Γ₁ Δ G Ψ Ω₁))
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} eq
  | inj₁ (I ∷ Ω₀ , eq1 , refl) | inj₂ (Ω₀ , eq3 , refl)
  with cases++ (Λ₁ ++ Δ₁) Ω₀ Ω₁ (E ∷ Δ ++ Λ) (sym eq3)
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ξ) (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ξ ++ E ∷ Δ ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ξ) , refl , refl)
  | inj₂ (.(Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ξ) , refl , refl)
  | inj₁ (Ξ , refl , refl)
  rewrite ++?-inj₁ (A ⇒ B ∷ Ξ) (Γ₁ ++ Λ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ξ) (Γ₁ ++ I ∷ Λ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Λ₁ ++ B ∷ Ξ) Γ₁ (E ∷ Δ ++ Λ) =
    intrp≗ (g~ IL⇒L-comm₁)
... | inj₂ (Ξ , eqa , eqb)
  with cases∷ Ξ eqa
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ Δ₁) (.(A ⇒ B) ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Δ ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Λ₁ ++ Δ₁) , refl , refl)
  | inj₂ (.(Λ₁ ++ Δ₁) , refl , refl)
  | inj₂ (.[] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Λ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ I ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Λ₁) Γ₁ (B ∷ Δ ++ Λ) =
    intrp≗ (g~ IL⇒L-comm₁)
... | inj₂ (Ξ' , eq4 , refl)
  with ++? Ω₀ Λ₁ (E ∷ Ξ') Δ₁ eqb
... | inj₁ (Ψ , refl , refl)
  with ++? Δ Ξ' Λ (A ⇒ B ∷ Ω₁) (sym eq4)
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ Ψ) (E ∷ Ξ') .(A ⇒ B ∷ Ω₁)
  {Γ₁} {.(Ψ ++ E ∷ Ξ')} {Λ₁} {Ω₁} {A} {B} {C} refl
  | inj₁ (.(I ∷ Λ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(Λ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(E ∷ Ξ') , refl , refl)
  | inj₂ (Ξ' , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Λ₁ ++ Ψ) Ξ' (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ Λ₁) Ξ' E |
          cases++-inj₂ [] Ξ' Ω₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ Λ₁ ++ Ψ) Ξ' (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ I ∷ Λ₁) Ξ' E |
          cases++-inj₂ [] Ξ' Ω₁ (A ⇒ B) =
    intrp≗ (g~ IL⇒L-comm₁)
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ Ψ) (E ∷ .(Ξ' ++ A ⇒ B ∷ Ω')) Λ
  {Γ₁} {.(Ψ ++ E ∷ Ξ')} {Λ₁} {.(Ω' ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Λ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(Λ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(E ∷ Ξ') , refl , refl)
  | inj₂ (Ξ' , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₁ ((.(A ⇒ B)) ∷ Ω' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Λ₁ ++ Ψ) Ξ' (A ⇒ B ∷ Ω' ++ Λ) E |
          cases++-inj₂ Ψ (Γ₁ ++ Λ₁) Ξ' E |
          cases++-inj₁ Ξ' Ω' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ Λ₁ ++ Ψ) Ξ' (A ⇒ B ∷ Ω' ++ Λ) E |
          cases++-inj₂ Ψ (Γ₁ ++ I ∷ Λ₁) Ξ' E |
          cases++-inj₁ Ξ' Ω' Λ (A ⇒ B) |
          ++?-inj₁ (I ∷ Λ₁) Γ₁ (B ∷ Ω' ++ Λ) =
    intrp≗ (g~ IL⇒L-comm₁)
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Λ₁ ++ Ψ) (E ∷ Δ) .(G ∷ Ω' ++ A ⇒ B ∷ Ω₁)
  {Γ₁} {.(Ψ ++ E ∷ Δ ++ G ∷ Ω')} {Λ₁} {Ω₁} {A} {B} {C} refl
  | inj₁ (.(I ∷ Λ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(Λ₁ ++ Ψ) , refl , refl)
  | inj₂ (.(E ∷ Δ ++ G ∷ Ω') , refl , refl)
  | inj₂ (.(Δ ++ G ∷ Ω') , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₂ (G , Ω' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Λ₁ ++ Ψ) (Δ ++ G ∷ Ω') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ Λ₁) (Δ ++ G ∷ Ω') E |
          cases++-inj₂ (G ∷ Ω') Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ Λ₁ ++ Ψ) (Δ ++ G ∷ Ω') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₂ Ψ (Γ₁ ++ I ∷ Λ₁) (Δ ++ G ∷ Ω') E |
          cases++-inj₂ (G ∷ Ω') Δ Ω₁ (A ⇒ B) =
    intrp≗ (g~ IL⇒L-comm₁)
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} eq
  | inj₁ (I ∷ Ω₀ , eq1 , refl)
  | inj₂ (Ω₀ , eq3 , refl)
  | inj₂ (.(E ∷ Ξ') , eqa , eqb)
  | inj₂ (Ξ' , eq4 , refl)
  | inj₂ (G , Ψ , refl , refl)
  with ++? Δ Ψ Λ (Δ₁ ++ A ⇒ B ∷ Ω₁) (sym eq4)
... | inj₁ (Ω'' , eq5 , refl)
  with ++? Δ₁ Ω'' (A ⇒ B ∷ Ω₁) Λ (sym eq5)
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Ω₀) (E ∷ .(Ψ ++ Ω'')) .(Ω''' ++ A ⇒ B ∷ Ω₁)
  {Γ₁} {.(Ω'' ++ Ω''')} {.(Ω₀ ++ E ∷ Ψ)} {Ω₁} {A} {B} {C} refl
  | inj₁ (.(I ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (.(E ∷ Ψ ++ Ω'' ++ Ω''') , refl , refl)
  | inj₂ (.(Ψ ++ Ω'' ++ Ω''') , refl , refl)
  | inj₂ (E , Ψ , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω₀) (Ψ ++ Ω'' ++ Ω''') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ Ω₀) Ψ (Ω'' ++ Ω''') E |
          cases++-inj₂ Ω''' (Ψ ++ Ω'') Ω₁ (A ⇒ B) |
          ++?-inj₁ Ω'' Ψ Ω''' |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω₀) (Ψ ++ Ω'' ++ Ω''') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ I ∷ Ω₀) Ψ (Ω'' ++ Ω''') E |
          cases++-inj₂ Ω''' (Ψ ++ Ω'') Ω₁ (A ⇒ B) |
          ++?-inj₁ Ω'' Ψ Ω''' |
          ++?-inj₁ (I ∷ Ω₀) Γ₁ (E ∷ Ψ ++ B ∷ Ω₁) =
    intrp≗ (g~ (IL⊗L-comm₁ ∘ ⊗L {Γ = Γ₁ ++ I ∷ Ω₀} IL⇒L-comm₁))
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Ω₀) (E ∷ .(Ψ ++ Δ₁ ++ A ⇒ B ∷ Ω''')) Λ
  {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Ψ)} {.(Ω''' ++ Λ)} {A} {B} {C} refl
  | inj₁ (.(I ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (.(E ∷ Ψ ++ Δ₁) , refl , refl)
  | inj₂ (.(Ψ ++ Δ₁) , refl , refl)
  | inj₂ (E , Ψ , refl , refl)
  | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω''') , refl , refl)
  | inj₂ (.(A ⇒ B) , Ω''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω₀) (Ψ ++ Δ₁) (A ⇒ B ∷ Ω''' ++ Λ) E |
          cases++-inj₁ (Γ₁ ++ Ω₀) Ψ Δ₁ E |
          cases++-inj₁ (Ψ ++ Δ₁) Ω''' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω₀) (Ψ ++ Δ₁) (A ⇒ B ∷ Ω''' ++ Λ) E |
          cases++-inj₁ (Γ₁ ++ I ∷ Ω₀) Ψ Δ₁ E |
          cases++-inj₁ (Ψ ++ Δ₁) Ω''' Λ (A ⇒ B) |
          ++?-inj₁ (I ∷ Ω₀) Γ₁ (E ∷ Ψ ++ B ∷ Ω''' ++ Λ) =
    intrp≗ refl
mip≗IL⇒L-comm₁ .(Γ₁ ++ I ∷ Ω₀) (E ∷ Δ) .(F ∷ Ω'' ++ Δ₁ ++ A ⇒ B ∷ Ω₁)
  {Γ₁} {Δ₁} {.(Ω₀ ++ E ∷ Δ ++ F ∷ Ω'')} {Ω₁} {A} {B} {C} refl
  | inj₁ (.(I ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (.(E ∷ Δ ++ F ∷ Ω'' ++ Δ₁) , refl , refl)
  | inj₂ (.(Δ ++ F ∷ Ω'' ++ Δ₁) , refl , refl)
  | inj₂ (E , .(Δ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω₀) (Δ ++ F ∷ Ω'' ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ Ω₀) (Δ ++ F ∷ Ω'') Δ₁ E |
          cases++-inj₂ (F ∷ Ω'' ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω'' Δ₁ F |
          ++?-inj₂ (Γ₁ ++ I ∷ Ω₀) (Δ ++ F ∷ Ω'' ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ (Γ₁ ++ I ∷ Ω₀) (Δ ++ F ∷ Ω'') Δ₁ E |
          cases++-inj₂ (F ∷ Ω'' ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω'' Δ₁ F |
          ++?-inj₁ (I ∷ Ω₀) Γ₁ (E ∷ Δ ++ F ∷ Ω'' ++ B ∷ Ω₁) =
    intrp≗ (g~ IL⇒L-comm₁)
mip≗IL⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} eq
  | inj₂ (F , Ω , refl , eq2)
  with cases++ Ω Δ (Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁) Λ (inj∷ eq2 .proj₂)
... | inj₁ (Ξ , eqa , eqb)
  with ++? Ξ Λ₁ Λ (Δ₁ ++ A ⇒ B ∷ Ω₁) eqb
... | inj₁ (Ψ , eqc , refl)
  with ++? Δ₁ Ψ (A ⇒ B ∷ Ω₁) Λ (sym eqc)
mip≗IL⇒L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Λ₁ ++ Ψ)) .(Ω' ++ A ⇒ B ∷ Ω₁)
  {.(Γ ++ E ∷ Ω)} {.(Ψ ++ Ω')} {Λ₁} {Ω₁} {A} {B} {C} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (.(Λ₁ ++ Ψ) , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω ++ I ∷ Λ₁ ++ Ψ ++ Ω') (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Ω ++ I ∷ Λ₁) (Ψ ++ Ω') E |
          cases++-inj₂ Ω' (Ω ++ I ∷ Λ₁ ++ Ψ) Ω₁ (A ⇒ B) |
          ++?-inj₁ Ψ (Ω ++ I ∷ Λ₁) Ω' |
          ++?-inj₂ Γ Ω (I ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Λ₁ (B ∷ Ω₁) I =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = E ∷ Ω} {Δ₁ = Λ₁ ++ Ψ}
          (mip⇒L~⊗midΓ Γ (E ∷ Ω ++ Λ₁) Ψ Ω' Ω₁))
        (h~ (IL⊗R₁ {Γ = E ∷ Ω} {Δ = Λ₁} {Λ = Ψ})))
mip≗IL⇒L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω')) Λ
  {.(Γ ++ E ∷ Ω)} {Δ₁} {Λ₁} {.(Ω' ++ Λ)} {A} {B} {C} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (.(Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω') , refl , refl)
  | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω') , refl , refl)
  | inj₂ (.(A ⇒ B) , Ω' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω ++ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω' ++ Λ) E |
          cases++-inj₁ Γ (Ω ++ Λ₁) Δ₁ E |
          cases++-inj₁ (Ω ++ Λ₁ ++ Δ₁) Ω' Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ω ++ I ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω' ++ Λ) E |
          cases++-inj₁ Γ (Ω ++ I ∷ Λ₁) Δ₁ E |
          cases++-inj₁ (Ω ++ I ∷ Λ₁ ++ Δ₁) Ω' Λ (A ⇒ B) |
          ++?-inj₂ Γ Ω (I ∷ Λ₁ ++ B ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω (Λ₁ ++ B ∷ Ω') Λ I =
    intrp≗ (h~ IL⇒L-comm₁)
mip≗IL⇒L-comm₁ Γ (E ∷ .(Ω ++ I ∷ Ξ)) .(G ∷ Ψ ++ Δ₁ ++ A ⇒ B ∷ Ω₁)
  {.(Γ ++ E ∷ Ω)} {Δ₁} {.(Ξ ++ G ∷ Ψ)} {Ω₁} {A} {B} {C} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Ξ , refl , refl)
  | inj₂ (G , Ψ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω ++ Ξ ++ G ∷ Ψ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Ω ++ Ξ ++ G ∷ Ψ) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ Δ₁) (Ω ++ Ξ) Ω₁ (A ⇒ B) |
          ++?-inj₂ (Ω ++ Ξ) Ψ Δ₁ G |
          ++?-inj₂ Γ (Ω ++ I ∷ Ξ ++ G ∷ Ψ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Ω ++ I ∷ Ξ ++ G ∷ Ψ) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ Δ₁) (Ω ++ I ∷ Ξ) Ω₁ (A ⇒ B) |
          ++?-inj₂ (Ω ++ I ∷ Ξ) Ψ Δ₁ G |
          ++?-inj₂ Γ Ω (I ∷ Ξ ++ G ∷ Ψ ++ B ∷ Ω₁) E |
          cases++-inj₁ Ω Ξ (G ∷ Ψ ++ B ∷ Ω₁) I =
    intrp≗ refl
mip≗IL⇒L-comm₁ Γ (E ∷ Δ) .(I ∷ [] ++ Δ₁ ++ A ⇒ B ∷ Ω₁)
  {.(Γ ++ E ∷ Δ ++ [])} {Δ₁} {[]} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ []) , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ [] ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ []) Δ₁ E |
          cases++-inj₂ ([] ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₁ [] Δ Δ₁ |
          ++?-inj₂ Γ (Δ ++ I ∷ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ I ∷ []) Δ₁ E |
          cases++-inj₂ (I ∷ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ [] Δ₁ I |
          ++?-inj₂ Γ Δ (I ∷ B ∷ Ω₁) E |
          cases++-inj₂ [] Δ (B ∷ Ω₁) I =
    let H = mip Γ (E ∷ Δ) (B ∷ Ω₁) g refl
        body = ⇒L {Γ ++ MIP.D H ∷ []} {I ∷ Δ₁} {Ω₁}
                 (IL {[]} {Δ₁} f) (MIP.g H)
        eqbody =
          (((~ (≡to≗
               (cut⇒L-cases++-assoc [] (Γ ++ MIP.D H ∷ [])
                 {Λ₀ = Δ₁} {Λ₁ = Ω₁}
                 {f = IR} {g = IL {[]} {Δ₁} f} {h = MIP.g H})))
            ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D H ∷ []) IR body refl) refl))
            ∘ ≡to≗
                (cut⊗R⊗Lcases++ Γ (Δ₁ ++ A ⇒ B ∷ Ω₁)
                  {f = ax} {g = IR} {h = body}))
    in intrp≗
         (↜∷
           (⊗R ax IR ,
            ((~ (IL⇒L-comm₁ {Γ = Γ ++ MIP.D H ∷ []} {Δ = Δ₁} {Λ = []} {Ω = Ω₁}))
             ∘ (IL {Γ ++ MIP.D H ∷ []} {Δ₁ ++ A ⇒ B ∷ Ω₁} eqbody
                ∘ ≡to≗
                    (cutIL-cases++₂ Γ [] (Δ₁ ++ A ⇒ B ∷ Ω₁)
                      {f = ⊗R ax IR} {g = ⊗L {Γ} body}))) ,
            refl)
           refl)
mip≗IL⇒L-comm₁ Γ (E ∷ Δ) .(I ∷ F ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁)
  {.(Γ ++ E ∷ Δ ++ [])} {Δ₁} {F ∷ Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ []) , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ F ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ F ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (F ∷ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ Λ₁ Δ₁ F |
          ++?-inj₂ Γ (Δ ++ I ∷ F ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ I ∷ F ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (I ∷ F ∷ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ (F ∷ Λ₁) Δ₁ I |
          ++?-inj₂ Γ Δ (I ∷ F ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₂ [] Δ (F ∷ Λ₁ ++ B ∷ Ω₁) I =
    let H = mip Γ (E ∷ Δ) (F ∷ Λ₁ ++ B ∷ Ω₁) g refl
    in intrp≗
         (g~ (IL⇒L-comm₁ {Γ = Γ ++ MIP.D H ∷ []} {Δ = Δ₁}
                {Λ = F ∷ Λ₁} {Ω = Ω₁}))
mip≗IL⇒L-comm₁ Γ (E ∷ Δ) .(G ∷ Ψ ++ I ∷ Λ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω₁)
  {.(Γ ++ E ∷ Δ ++ G ∷ Ψ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ G ∷ Ψ) , refl , refl)
  | inj₂ (G ∷ Ψ , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ G ∷ Ψ ++ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ψ ++ Λ₁) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ (Ψ ++ Λ₁) Δ₁ G |
          ++?-inj₂ Γ (Δ ++ G ∷ Ψ ++ I ∷ Λ₁ ++ Δ₁) (A ⇒ B ∷ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ψ ++ I ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (G ∷ Ψ ++ I ∷ Λ₁ ++ Δ₁) Δ Ω₁ (A ⇒ B) |
          ++?-inj₂ Δ (Ψ ++ I ∷ Λ₁) Δ₁ G |
          ++?-inj₂ Γ (Δ ++ G ∷ Ψ) (I ∷ Λ₁ ++ B ∷ Ω₁) E |
          cases++-inj₂ (G ∷ Ψ) Δ (Λ₁ ++ B ∷ Ω₁) I =
    let H = mip Γ (E ∷ Δ) (G ∷ Ψ ++ Λ₁ ++ B ∷ Ω₁) g refl
    in intrp≗
         (g~ (IL⇒L-comm₁ {Γ = Γ ++ MIP.D H ∷ G ∷ Ψ} {Δ = Δ₁}
                {Λ = Λ₁} {Ω = Ω₁}))
