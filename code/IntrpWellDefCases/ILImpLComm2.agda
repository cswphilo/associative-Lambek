{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILImpLComm2 where

open import IntrpWellDefCases.Base
open import IntrpWellDefCases.ImpLImpLComm using (mip⇒L~Γ)


mip≗IL⇒L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁} {Ω₁} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L f (IL {Γ₁ ++ B ∷ Λ₁} {Ω₁} g)) eq)
mip≗IL⇒L-comm₂ Γ [] Λ eq = mip[]≗ Γ Λ eq IL⇒L-comm₂
mip≗IL⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  with ++? Γ (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (E ∷ Δ ++ Λ) (I ∷ Ω₁) eq
mip≗IL⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ Ω) (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₁ (Ω , eq1 , refl)
  with cases∷ Ω eq1
mip≗IL⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (I ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Δ ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₁) (I ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ B ∷ Λ₁) (I ∷ Δ ++ Λ) =
    intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⇒L~Γ Γ₁ Λ₁ Δ Λ))
mip≗IL⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₁ (I ∷ Ω' , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite ++?-inj₁ (A ⇒ B ∷ Λ₁ ++ I ∷ Ω') (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁ ++ Ω') (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (I ∷ Ω') (Γ₁ ++ B ∷ Λ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ IL⇒L-comm₂)
mip≗IL⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with cases++ Ω Δ Ω₁ Λ (inj∷ eq2 .proj₂)
... | inj₁ (Ω' , refl , refl)
  with cases++ Γ (Γ₁ ++ Δ₁) Ω (A ⇒ B ∷ Λ₁) eq1
... | inj₁ (Ω'' , eqa , eqb)
  with cases++ Γ Γ₁ Ω'' Δ₁ eqa
mip≗IL⇒L-comm₂ Γ (E ∷ .(Ψ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω')) Λ
  {.(Γ ++ E ∷ Ψ)} {Δ₁} {Λ₁} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ψ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(Ψ ++ Δ₁) , refl , refl)
  | inj₁ (Ψ , refl , refl)
  rewrite cases++-inj₁ (Ψ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Ω' Λ I |
          ++?-inj₂ Γ (Ψ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ I ∷ Ω' ++ Λ) E |
          ++?-inj₂ Γ (Ψ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ Ω' ++ Λ) E |
          cases++-inj₁ Γ Ψ Δ₁ E |
          cases++-inj₁ (Ψ ++ Δ₁) (Λ₁ ++ I ∷ Ω') Λ (A ⇒ B) |
          cases++-inj₁ (Ψ ++ Δ₁) (Λ₁ ++ Ω') Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ψ ++ B ∷ Λ₁) (I ∷ Ω' ++ Λ) E |
          cases++-inj₁ (Ψ ++ B ∷ Λ₁) Ω' Λ I =
    intrp≗ (h~ IL⇒L-comm₂)
mip≗IL⇒L-comm₂ .(Γ₁ ++ Ψ) (E ∷ .(Ω'' ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω')) Λ
  {Γ₁} {.(Ψ ++ E ∷ Ω'')} {Λ₁} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ω'' ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ (Ψ , refl , refl)
  rewrite cases++-inj₁ (Ω'' ++ A ⇒ B ∷ Λ₁) Ω' Λ I |
          ++?-inj₂ (Γ₁ ++ Ψ) Ω'' (A ⇒ B ∷ Λ₁ ++ I ∷ Ω' ++ Λ) E |
          ++?-inj₂ (Γ₁ ++ Ψ) Ω'' (A ⇒ B ∷ Λ₁ ++ Ω' ++ Λ) E |
          cases++-inj₂ Ψ Γ₁ Ω'' E |
          cases++-inj₁ Ω'' (Λ₁ ++ I ∷ Ω') Λ (A ⇒ B) |
          cases++-inj₁ Ω'' (Λ₁ ++ Ω') Λ (A ⇒ B) |
          ++?-inj₂ Γ₁ Λ₁ (I ∷ Ω' ++ Λ) B |
          cases++-inj₁ Λ₁ Ω' Λ I =
    intrp≗ (h~ (IL⇒R ∘ ⇒R IL⇒L-comm₂))
mip≗IL⇒L-comm₂ Γ (E ∷ .(Ω ++ I ∷ Ω')) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ω' ++ Λ)} {A} {B} eq
  | inj₂ (F , Ω , eq1 , eq2)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , eqa , eqb)
  with cases∷ Ω'' eqa
mip≗IL⇒L-comm₂ .(Γ₁ ++ Δ₁) (.(A ⇒ B) ∷ .(Ω ++ I ∷ Ω')) Λ
  {Γ₁} {Δ₁} {Ω} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (.(A ⇒ B) , Ω , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ I |
          ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Ω ++ I ∷ Ω' ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Ω ++ Ω' ++ Λ) |
          ++?-inj₂ Γ₁ Ω (I ∷ Ω' ++ Λ) B |
          cases++-inj₁ Ω Ω' Λ I =
    intrp≗ (h~ (IL⇒R ∘ ⇒R IL⇒L-comm₂))
mip≗IL⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ψ) (E ∷ .(Ω ++ I ∷ Ω')) Λ
  {Γ₁} {Δ₁} {.(Ψ ++ E ∷ Ω)} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (.(A ⇒ B ∷ Ψ) , refl , refl)
  | inj₂ (Ψ , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ I |
          ++?-inj₁ (A ⇒ B ∷ Ψ) (Γ₁ ++ Δ₁) (E ∷ Ω ++ I ∷ Ω' ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ψ) (Γ₁ ++ Δ₁) (E ∷ Ω ++ Ω' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ B ∷ Ψ) Ω (I ∷ Ω' ++ Λ) E |
          cases++-inj₁ Ω Ω' Λ I =
    intrp≗ refl
mip≗IL⇒L-comm₂ Γ (E ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₂ (F , .(Δ ++ Ω') , eq1 , eq2)
  | inj₂ (Ω' , refl , refl)
  with cases++ Γ (Γ₁ ++ Δ₁) (Δ ++ Ω') (A ⇒ B ∷ Λ₁) eq1
... | inj₁ (Ω'' , eqa , eqb)
  with cases++ Γ Γ₁ Ω'' Δ₁ eqa
mip≗IL⇒L-comm₂ Γ (E ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Ψ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₂ (E , .(Δ ++ Ω') , eq1 , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(Ψ ++ Δ₁) , refl , eqb)
  | inj₁ (Ψ , refl , refl)
  with cases++ (Ψ ++ Δ₁) Δ Λ₁ Ω' eqb
mip≗IL⇒L-comm₂ Γ (E ∷ .(Ψ ++ Δ₁ ++ A ⇒ B ∷ Θ)) .(Ω' ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Ψ)} {Δ₁} {.(Θ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ψ ++ Δ₁ ++ A ⇒ B ∷ Θ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(Ψ ++ Δ₁) , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₁ (Θ , refl , refl)
  rewrite cases++-inj₂ Ω' (Ψ ++ Δ₁ ++ A ⇒ B ∷ Θ) Ω₁ I |
          ++?-inj₂ Γ (Ψ ++ Δ₁) (A ⇒ B ∷ Θ ++ Ω' ++ I ∷ Ω₁) E |
          ++?-inj₂ Γ (Ψ ++ Δ₁) (A ⇒ B ∷ Θ ++ Ω' ++ Ω₁) E |
          cases++-inj₁ Γ Ψ Δ₁ E |
          cases++-inj₁ (Ψ ++ Δ₁) Θ (Ω' ++ I ∷ Ω₁) (A ⇒ B) |
          cases++-inj₁ (Ψ ++ Δ₁) Θ (Ω' ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ Γ (Ψ ++ B ∷ Θ ++ Ω') (I ∷ Ω₁) E |
          cases++-inj₂ Ω' (Ψ ++ B ∷ Θ) Ω₁ I =
    intrp≗ refl
... | inj₂ (Θ , eqc , eqd)
  with ++? Δ Ψ Θ Δ₁ eqd
mip≗IL⇒L-comm₂ Γ (E ∷ .(Ψ ++ Ξ)) .(Θ ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Ψ)} {.(Ξ ++ Θ)} {Λ₁} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ψ ++ Ξ ++ Θ ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₂ (.(Θ ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₁ (.(Ψ ++ Ξ ++ Θ) , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₂ (Θ , refl , refl)
  | inj₁ (Ξ , refl , refl)
  rewrite cases++-inj₂ (Θ ++ A ⇒ B ∷ Λ₁) (Ψ ++ Ξ) Ω₁ I |
          ++?-inj₂ Γ (Ψ ++ Ξ ++ Θ) (A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁) E |
          ++?-inj₂ Γ (Ψ ++ Ξ ++ Θ) (A ⇒ B ∷ Λ₁ ++ Ω₁) E |
          cases++-inj₁ Γ Ψ (Ξ ++ Θ) E |
          cases++-inj₂ Θ (Ψ ++ Ξ) (Λ₁ ++ I ∷ Ω₁) (A ⇒ B) |
          cases++-inj₂ Θ (Ψ ++ Ξ) (Λ₁ ++ Ω₁) (A ⇒ B) |
          ++?-inj₁ Ξ Ψ Θ |
          ++?-inj₂ Γ (Ψ ++ B ∷ Λ₁) (I ∷ Ω₁) E |
          cases++-inj₂ (B ∷ Λ₁) Ψ Ω₁ I =
    intrp≗
      (g~ (IL⊗L-comm₂ {Γ = Γ} {Δ = Θ ++ A ⇒ B ∷ Λ₁} {Λ = Ω₁} ∘
           ⊗L (IL⇒L-comm₂
             {Γ = Γ ++ MIP.D (mip Γ (E ∷ Ψ) (B ∷ Λ₁ ++ Ω₁) g refl) ∷ []}
             {Δ = MIP.D (mip [] Ξ Θ f refl) ∷ Θ}
             {Λ = Λ₁} {Ω = Ω₁})))
mip≗IL⇒L-comm₂ Γ (E ∷ Δ) .(G ∷ Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Δ ++ G ∷ Ξ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ G ∷ Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₂ (.(G ∷ Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₁ (.(Δ ++ G ∷ Ξ ++ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ G ∷ Ξ) , refl , refl)
  | inj₂ (.(G ∷ Ξ ++ Δ₁) , refl , refl)
  | inj₂ (G , Ξ , refl , refl)
  rewrite cases++-inj₂ (G ∷ Ξ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Δ Ω₁ I |
          ++?-inj₂ Γ (Δ ++ G ∷ Ξ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁) E |
          ++?-inj₂ Γ (Δ ++ G ∷ Ξ ++ Δ₁) (A ⇒ B ∷ Λ₁ ++ Ω₁) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ξ) Δ₁ E |
          cases++-inj₂ (G ∷ Ξ ++ Δ₁) Δ (Λ₁ ++ I ∷ Ω₁) (A ⇒ B) |
          cases++-inj₂ (G ∷ Ξ ++ Δ₁) Δ (Λ₁ ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ Δ Ξ Δ₁ G |
          ++?-inj₂ Γ (Δ ++ G ∷ Ξ ++ B ∷ Λ₁) (I ∷ Ω₁) E |
          cases++-inj₂ (G ∷ Ξ ++ B ∷ Λ₁) Δ Ω₁ I =
    intrp≗ (g~ IL⇒L-comm₂)
mip≗IL⇒L-comm₂ .(Γ₁ ++ Ψ) (E ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {.(Ψ ++ F ∷ Ω'')} {Λ₁} {Ω₁} {A} {B} eq
  | inj₂ (F , .(Δ ++ Ω') , eq1 , eq2)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ω'' , eqa , eqb)
  | inj₂ (Ψ , refl , refl)
  with cases++ Ω'' Δ Λ₁ Ω' eqb
mip≗IL⇒L-comm₂ .(Γ₁ ++ Ψ) (E ∷ .(Ω'' ++ A ⇒ B ∷ Θ)) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {.(Ψ ++ E ∷ Ω'')} {.(Θ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ω'' ++ A ⇒ B ∷ Θ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ (Ψ , refl , refl)
  | inj₁ (Θ , refl , refl)
  rewrite cases++-inj₂ Ω' (Ω'' ++ A ⇒ B ∷ Θ) Ω₁ I |
          ++?-inj₂ (Γ₁ ++ Ψ) Ω'' (A ⇒ B ∷ Θ ++ Ω' ++ I ∷ Ω₁) E |
          ++?-inj₂ (Γ₁ ++ Ψ) Ω'' (A ⇒ B ∷ Θ ++ Ω' ++ Ω₁) E |
          cases++-inj₂ Ψ Γ₁ Ω'' E |
          cases++-inj₁ Ω'' Θ (Ω' ++ I ∷ Ω₁) (A ⇒ B) |
          cases++-inj₁ Ω'' Θ (Ω' ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ Γ₁ (Θ ++ Ω') (I ∷ Ω₁) B |
          cases++-inj₂ Ω' Θ Ω₁ I =
    intrp≗ (g~ IL⇒L-comm₂)
mip≗IL⇒L-comm₂ .(Γ₁ ++ Ψ) (E ∷ Δ) .(Θ ++ A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁)
  {Γ₁} {.(Ψ ++ E ∷ Δ ++ Θ)} {Λ₁} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ Θ ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₂ (.(Θ ++ A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₁ (.(Δ ++ Θ) , refl , refl)
  | inj₂ (Ψ , refl , refl)
  | inj₂ (Θ , refl , refl)
  rewrite cases++-inj₂ (Θ ++ A ⇒ B ∷ Λ₁) Δ Ω₁ I |
          ++?-inj₂ (Γ₁ ++ Ψ) (Δ ++ Θ) (A ⇒ B ∷ Λ₁ ++ I ∷ Ω₁) E |
          ++?-inj₂ (Γ₁ ++ Ψ) (Δ ++ Θ) (A ⇒ B ∷ Λ₁ ++ Ω₁) E |
          cases++-inj₂ Ψ Γ₁ (Δ ++ Θ) E |
          cases++-inj₂ Θ Δ (Λ₁ ++ I ∷ Ω₁) (A ⇒ B) |
          cases++-inj₂ Θ Δ (Λ₁ ++ Ω₁) (A ⇒ B) =
    intrp≗ (g~ IL⇒L-comm₂)
mip≗IL⇒L-comm₂ Γ (E ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₂ (F , .(Δ ++ Ω') , eq1 , eq2)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (Ω'' , eqa , eqb)
  with cases∷ Ω'' eqa
mip≗IL⇒L-comm₂ .(Γ₁ ++ Δ₁) (.(A ⇒ B) ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {Δ₁} {.(Δ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (.(A ⇒ B) , .(Δ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Ω₁ I |
          ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Ω' ++ I ∷ Ω₁) |
          ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Ω' ++ Ω₁) |
          ++?-inj₂ Γ₁ (Δ ++ Ω') (I ∷ Ω₁) B |
          cases++-inj₂ Ω' Δ Ω₁ I =
    intrp≗ (g~ IL⇒L-comm₂)
mip≗IL⇒L-comm₂ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ψ) (E ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {Δ₁} {.(Ψ ++ E ∷ Δ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(A ⇒ B ∷ Ψ) , refl , refl)
  | inj₂ (Ψ , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Ω₁ I |
          ++?-inj₁ (A ⇒ B ∷ Ψ) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Ω' ++ I ∷ Ω₁) |
          ++?-inj₁ (A ⇒ B ∷ Ψ) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Ω' ++ Ω₁) |
          ++?-inj₂ (Γ₁ ++ B ∷ Ψ) (Δ ++ Ω') (I ∷ Ω₁) E |
          cases++-inj₂ Ω' Δ Ω₁ I =
    intrp≗
      (g~ (IL⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁}
            {Λ = Ψ ++ MIP.D (mip (Γ₁ ++ B ∷ Ψ) (E ∷ Δ) (Ω' ++ Ω₁) g refl) ∷ Ω'}
            {Ω = Ω₁}))
