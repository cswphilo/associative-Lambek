{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLImpLComm where

open import IntrpWellDefCases.Base
open import IntrpWellDefCases.ILImpLAssoc using (mip⇒L~⇒; mip⇒L~Δ; mip⇒L~ΔΓ)
open import Data.Sum

mip⇒L~Γ : ∀ Γ₀ Γ₁ Δ Λ
  {Ω : Cxt} {A B C : Fma}
  {f : Ω ⊢ A} {g : Γ₀ ++ B ∷ Γ₁ ++ Δ ++ Λ ⊢ C}
  → mip (Γ₀ ++ Ω ++ A ⇒ B ∷ Γ₁) Δ Λ
      (⇒L {Γ₀} {Ω} {Γ₁ ++ Δ ++ Λ} f g) refl
      ~ ⇒L~Γ' {Γ₀ = Γ₀} {Γ₁ = Γ₁} (mip (Γ₀ ++ B ∷ Γ₁) Δ Λ g refl) f
mip⇒L~Γ Γ₀ Γ₁ [] Λ = g~ IL⇒L-comm₂
mip⇒L~Γ Γ₀ Γ₁ (E ∷ Δ) Λ {Ω} {A} {B}
  rewrite ++?-inj₁ (A ⇒ B ∷ Γ₁) (Γ₀ ++ Ω) (E ∷ Δ ++ Λ) = refl

mip≗⇒L⇒L-comm : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ Ξ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ⊢ A} {f' : Δ₁ ⊢ A'} {g : Γ₁ ++ B ∷ Λ₁ ++ B' ∷ Ξ ⊢ C}
  → (eq : Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⇒L f (⇒L {Γ₁ ++ B ∷ Λ₁} f' g)) eq)
      (mip Γ Δ Λ (⇒L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁} f' (⇒L f g)) eq)
mip≗⇒L⇒L-comm Γ [] Λ eq = mip[]≗ Γ Λ eq ⇒L⇒L-comm
mip≗⇒L⇒L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  with ++? Γ (Γ₁ ++ Δ₀) (E ∷ Δ ++ Λ) (A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) eq
mip≗⇒L⇒L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₁ (Ω , eq₁ , eq₂) with cases∷ Ω eq₁
mip≗⇒L⇒L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₁ (Ω , eq₁ , eq₂) | inj₁ (refl , refl , eq₃)
  with cases++ (Λ₁ ++ Δ₁) Δ Ξ Λ eq₃
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀) (.(A ⇒ B) ∷ .(Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀)) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {.(Ω₀ ++ Λ)} {A} {B} {A'} {B'} refl
  | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ω₀ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Δ₀) (Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ω₀ ++ Λ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ Δ₁ (A ⇒ B) |
          cases++-inj₁ (Λ₁ ++ Δ₁) Ω₀ Λ (A' ⇒ B') |
          ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀ ++ Λ) |
          ++?-inj₂ Γ₁ (Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ω₀ ++ Λ) B |
          cases++-inj₁ Γ₁ Λ₁ Δ₁ B |
          cases++-inj₁ (Λ₁ ++ Δ₁) Ω₀ Λ (A' ⇒ B') =
    intrp≗ (h~ (⇒R ⇒L⇒L-comm ∘ (~ ⇒L⇒R)))
mip≗⇒L⇒L-comm Γ (.(A ⇒ B) ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₁ (.[] , eq₁ , refl) | inj₁ (refl , refl , eq₃) | inj₂ (Ω₀ , eq₄ , eq₅)
  with ++? Δ Λ₁ Ω₀ Δ₁ eq₅
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀) (.(A ⇒ B) ∷ .(Λ₁ ++ Ω₁)) .(Ω₀ ++ A' ⇒ B' ∷ Ξ) {Γ₁} {Δ₀} {.(Ω₁ ++ Ω₀)} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Δ₀) (Λ₁ ++ Ω₁ ++ Ω₀) (A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ (Ω₁ ++ Ω₀) (A ⇒ B) |
          cases++-inj₂ Ω₀ (Λ₁ ++ Ω₁) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₁ Λ₁ Ω₀ |
          ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) |
          ++?-inj₂ Γ₁ (Λ₁ ++ Ω₁ ++ Ω₀) (A' ⇒ B' ∷ Ξ) B |
          cases++-inj₁ Γ₁ Λ₁ (Ω₁ ++ Ω₀) B |
          cases++-inj₂ Ω₀ (Λ₁ ++ Ω₁) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₁ Λ₁ Ω₀ =
    intrp≗ (↜∷
      (⇒R (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax))) ,
        ((((⊗L {Γ₁ ++ Δ₀}
            (_∘_
              (~ (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Δ₀}
                {Δ₁ = MIP.D (mip [] Ω₁ Ω₀ f' refl) ∷ Ω₀} {Λ = []} {Ξ = Ξ}))
              (_∘_
                (_∘_
                  (⇒L (~ cutaxA-right (MIP.h (mip [] Δ₀ [] f refl))) refl)
                  (~ (≡to≗ (cut⇒L-cases++₁ [] Γ₁))))
                (cut-cong₂ Γ₁ refl
                  (_∘_
                    (⇒L refl
                      (_∘_
                        (_∘_
                          (~ cutaxA-left Γ₁
                            (⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                              (MIP.g (mip [] Ω₁ Ω₀ f' refl))
                              (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))
                            refl)
                          (cut-cong₂ Γ₁ refl
                            (~ cutaxA-left
                              (Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ [])
                              (⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                                (MIP.g (mip [] Ω₁ Ω₀ f' refl))
                                (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))
                              refl)))
                        (≡to≗ (cut⊗R⊗Lcases++ Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ)
                          {f = ax} {ax}
                          {⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                            (MIP.g (mip [] Ω₁ Ω₀ f' refl))
                            (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))}))))
                    (~ cut⇒L≗ Γ₁ ax (⊗R ax ax)
                      (⊗L (⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                        (MIP.g (mip [] Ω₁ Ω₀ f' refl))
                        (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))))
                      refl)))))
            ∘ ≡to≗ (cut⊗L-cases++₂ Γ₁ [] (Ω₀ ++ A' ⇒ B' ∷ Ξ)))
          ∘ cut-cong₂ Γ₁ refl
              (~ cut⊗L≗ Γ₁ (_ ∷ []) []
                (⇒L {[]} ax (⊗R ax ax))
                (⊗L (⇒L {Γ₁ ++ _ ∷ []}
                  (MIP.g (mip [] Ω₁ Ω₀ f' refl))
                  (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))))
                refl)) ∘
          (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) Δ₀))))) ,
        ⇒R (⊗R (⇒L (cutaxA-left [] _ refl) refl) refl ∘ (~ ⇒L⊗R₁)))
      refl)
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀) (.(A ⇒ B) ∷ Δ) .(F ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {Δ₀} {Δ₁} {.(Δ ++ F ∷ Ω₁)} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.[] , refl , refl) | inj₁ (refl , refl , refl)
  | inj₂ (.(F ∷ Ω₁ ++ Δ₁) , refl , refl) | inj₂ (F , Ω₁ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (Δ ++ F ∷ Ω₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) B |
          ++?-inj₂ (Γ₁ ++ Δ₀) ((Δ ++ F ∷ Ω₁) ++ Δ₁) (A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ Γ₁ (Δ ++ F ∷ Ω₁) Δ₁ B |
          cases++-inj₁ (Γ₁ ++ Δ₀) (Δ ++ F ∷ Ω₁) Δ₁ (A ⇒ B) |
          cases++-inj₂ (F ∷ Ω₁ ++ Δ₁) Δ Ξ (A' ⇒ B') |
          ++?-inj₂ Δ Ω₁ Δ₁ F |
          ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Δ ++ F ∷ Ω₁ ++ B' ∷ Ξ) =
    intrp≗ (g~ (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = F ∷ Ω₁} {Ξ = Ξ}))
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (E ∷ Δ) Λ
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} eq
  | inj₁ (.(A ⇒ B ∷ Ω₀) , eq₁ , refl) | inj₂ (Ω₀ , eq₃ , refl)
  with cases++ (Λ₁ ++ Δ₁) Ω₀ Ξ (E ∷ Δ ++ Λ) (sym eq₃)
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) (E ∷ Δ) Λ
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {.(Ω₂ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) , refl , refl)
  | inj₂ (.(Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite ++?-inj₁ (A' ⇒ B' ∷ Ω₂) (Γ₁ ++ B ∷ Λ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A' ⇒ B' ∷ Ω₂) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₂) (Γ₁ ++ Δ₀) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁}
      {Ξ = Ω₂ ++ MIP.D (mip (Γ₁ ++ B ∷ Λ₁ ++ B' ∷ Ω₂) (E ∷ Δ) Λ g refl) ∷ Λ}))
... | inj₂ (Ω₂ , eq₄ , eq₅) with cases∷ Ω₂ eq₄
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (.(A' ⇒ B') ∷ Δ) Λ
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ Δ₁) , refl , refl)
  | inj₂ (.(Λ₁ ++ Δ₁) , refl , refl)
  | inj₂ (.[] , refl , refl) | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₀) (B' ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇒L⇒L-comm)
... | inj₂ (Ω₃ , eq₆ , refl) with cases++ Ω₃ Δ Ξ Λ eq₆
... | inj₁ (Ω₄ , refl , refl) with cases++ Ω₀ Λ₁ Ω₃ Δ₁ eq₅
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (E ∷ .(Ω₅ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₄)) Λ
  {Γ₁} {Δ₀} {Δ₁} {.(Ω₀ ++ E ∷ Ω₅)} {.(Ω₄ ++ Λ)} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (.(E ∷ Ω₅ ++ Δ₁) , refl , refl)
  | inj₂ (.(Ω₅ ++ Δ₁) , refl , refl)
  | inj₁ (Ω₄ , refl , refl)
  | inj₁ (Ω₅ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ∷ Ω₀) (Ω₅ ++ Δ₁) (A' ⇒ B' ∷ Ω₄ ++ Λ) E |
          cases++-inj₁ (Γ₁ ++ B ∷ Ω₀) Ω₅ Δ₁ E |
          cases++-inj₁ (Ω₅ ++ Δ₁) Ω₄ Λ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (Ω₅ ++ Δ₁) (A' ⇒ B' ∷ Ω₄ ++ Λ) E |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) Ω₅ Δ₁ E |
          cases++-inj₁ (Ω₅ ++ Δ₁) Ω₄ Λ (A' ⇒ B') |
          ++?-inj₁ (A ⇒ B ∷ Ω₀) (Γ₁ ++ Δ₀) (E ∷ Ω₅ ++ B' ∷ Ω₄ ++ Λ) =
    intrp≗ refl
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω₅) (E ∷ .(Ω₃ ++ A' ⇒ B' ∷ Ω₄)) Λ
  {Γ₁} {Δ₀} {.(Ω₅ ++ E ∷ Ω₃)} {Λ₁} {.(Ω₄ ++ Λ)} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ Ω₅) , refl , refl)
  | inj₂ (.(Λ₁ ++ Ω₅) , refl , refl)
  | inj₂ (.(E ∷ Ω₃) , refl , refl)
  | inj₂ (Ω₃ , refl , refl)
  | inj₁ (Ω₄ , refl , refl)
  | inj₂ (Ω₅ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ∷ Λ₁ ++ Ω₅) Ω₃ (A' ⇒ B' ∷ Ω₄ ++ Λ) E |
          cases++-inj₂ Ω₅ (Γ₁ ++ B ∷ Λ₁) Ω₃ E |
          cases++-inj₁ Ω₃ Ω₄ Λ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω₅) Ω₃ (A' ⇒ B' ∷ Ω₄ ++ Λ) E |
          cases++-inj₂ Ω₅ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₃ E |
          cases++-inj₁ Ω₃ Ω₄ Λ (A' ⇒ B') |
          ++?-inj₁ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₀) (B' ∷ Ω₄ ++ Λ) =
    intrp≗ (g~ ⇒L⇒L-comm)
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (E ∷ Δ) .(Ω₄ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} eq
  | inj₁ (.(A ⇒ B ∷ Ω₀) , eq₁ , refl)
  | inj₂ (Ω₀ , eq₃ , refl)
  | inj₂ (.(E ∷ Δ ++ Ω₄) , refl , eq₅)
  | inj₂ (.(Δ ++ Ω₄) , refl , refl)
  | inj₂ (Ω₄ , refl , refl)
  with cases++ Ω₀ Λ₁ (Δ ++ Ω₄) Δ₁ eq₅
... | inj₁ (Ω₅ , refl , eq₇) with ++? Δ Ω₅ Ω₄ Δ₁ (sym eq₇)
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (E ∷ .(Ω₅ ++ Ω₆)) .(Ω₄ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {Δ₀} {.(Ω₆ ++ Ω₄)} {.(Ω₀ ++ E ∷ Ω₅)} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (.(E ∷ Ω₅ ++ Ω₆ ++ Ω₄) , refl , refl)
  | inj₂ (.(Ω₅ ++ Ω₆ ++ Ω₄) , refl , refl)
  | inj₂ (Ω₄ , refl , refl)
  | inj₁ (Ω₅ , refl , refl)
  | inj₁ (Ω₆ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ∷ Ω₀) (Ω₅ ++ Ω₆ ++ Ω₄) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ (Γ₁ ++ B ∷ Ω₀) Ω₅ (Ω₆ ++ Ω₄) E |
          cases++-inj₂ Ω₄ (Ω₅ ++ Ω₆) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₆ Ω₅ Ω₄ |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (Ω₅ ++ Ω₆ ++ Ω₄) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) Ω₅ (Ω₆ ++ Ω₄) E |
          cases++-inj₂ Ω₄ (Ω₅ ++ Ω₆) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₆ Ω₅ Ω₄ |
          ++?-inj₁ (A ⇒ B ∷ Ω₀) (Γ₁ ++ Δ₀) (E ∷ Ω₅ ++ B' ∷ Ξ) =
    intrp≗ (g~ ((~ (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₀} {Λ = Ω₀}
      {Ω = Ω₄ ++ A' ⇒ B' ∷ Ξ}
      {A' = MIP.D (mip (Γ₁ ++ B ∷ Ω₀) (E ∷ Ω₅) (B' ∷ Ξ) g refl)}
      {B' = MIP.D (mip [] Ω₆ Ω₄ f' refl)}))
      ∘ (⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀}
        (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Δ₀}
          {Δ₁ = MIP.D (mip [] Ω₆ Ω₄ f' refl) ∷ Ω₄}
          {Λ = Ω₀ ++ MIP.D (mip (Γ₁ ++ B ∷ Ω₀) (E ∷ Ω₅) (B' ∷ Ξ) g refl) ∷ []}
          {Ξ = Ξ}))))
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (E ∷ Δ) .(F ∷ Ω₆ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {Δ₀} {Δ₁} {.(Ω₀ ++ E ∷ Δ ++ F ∷ Ω₆)} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (.(E ∷ Δ ++ F ∷ Ω₆ ++ Δ₁) , refl , refl)
  | inj₂ (.(Δ ++ F ∷ Ω₆ ++ Δ₁) , refl , refl)
  | inj₂ (.(F ∷ Ω₆ ++ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω₆) , refl , refl)
  | inj₂ (F , Ω₆ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ∷ Ω₀) (Δ ++ F ∷ Ω₆ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ (Γ₁ ++ B ∷ Ω₀) (Δ ++ F ∷ Ω₆) Δ₁ E |
          cases++-inj₂ (F ∷ Ω₆ ++ Δ₁) Δ Ξ (A' ⇒ B') |
          ++?-inj₂ Δ Ω₆ Δ₁ F |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (Δ ++ F ∷ Ω₆ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₀) (Δ ++ F ∷ Ω₆) Δ₁ E |
          cases++-inj₂ (F ∷ Ω₆ ++ Δ₁) Δ Ξ (A' ⇒ B') |
          ++?-inj₂ Δ Ω₆ Δ₁ F |
          ++?-inj₁ (A ⇒ B ∷ Ω₀) (Γ₁ ++ Δ₀) (E ∷ Δ ++ F ∷ Ω₆ ++ B' ∷ Ξ) =
    intrp≗ (g~ ⇒L⇒L-comm)
mip≗⇒L⇒L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω₅) (E ∷ Δ) .(Ω₄ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {Δ₀} {.(Ω₅ ++ E ∷ Δ ++ Ω₄)} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ Ω₅) , refl , refl)
  | inj₂ (.(Λ₁ ++ Ω₅) , refl , refl)
  | inj₂ (.(E ∷ Δ ++ Ω₄) , refl , refl)
  | inj₂ (.(Δ ++ Ω₄) , refl , refl)
  | inj₂ (Ω₄ , refl , refl)
  | inj₂ (Ω₅ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ∷ Λ₁ ++ Ω₅) (Δ ++ Ω₄) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₂ Ω₅ (Γ₁ ++ B ∷ Λ₁) (Δ ++ Ω₄) E |
          cases++-inj₂ Ω₄ Δ Ξ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω₅) (Δ ++ Ω₄) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₂ Ω₅ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Δ ++ Ω₄) E |
          cases++-inj₂ Ω₄ Δ Ξ (A' ⇒ B') =
    intrp≗ (g~ ⇒L⇒L-comm)
mip≗⇒L⇒L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq₁ , eq₂) with cases++ Γ Γ₁ Ω Δ₀ eq₁
... | inj₁ (Ω₀ , refl , refl)
  with cases++ (Ω₀ ++ Δ₀) Δ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) Λ (inj∷ eq₂ .proj₂)
... | inj₁ (Ω₁ , refl , eq₄) with cases++ (Λ₁ ++ Δ₁) Ω₁ Ξ Λ (sym eq₄)
mip≗⇒L⇒L-comm Γ (E ∷ .(Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂)) Λ
  {.(Γ ++ E ∷ Ω₀)} {Δ₀} {Δ₁} {Λ₁} {.(Ω₂ ++ Λ)} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ω₂ ++ Λ) E |
          cases++-inj₁ Γ (Ω₀ ++ B ∷ Λ₁) Δ₁ E |
          cases++-inj₁ (Ω₀ ++ B ∷ Λ₁ ++ Δ₁) Ω₂ Λ (A' ⇒ B') |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ω₂ ++ Λ) E |
          cases++-inj₁ Γ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
          cases++-inj₁ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) Ω₂ Λ (A' ⇒ B') |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₂ ++ Λ) E |
          cases++-inj₁ Γ Ω₀ Δ₀ E |
          cases++-inj₁ (Ω₀ ++ Δ₀) (Λ₁ ++ B' ∷ Ω₂) Λ (A ⇒ B) =
    intrp≗ (h~ ⇒L⇒L-comm)
... | inj₂ (Ω₂ , refl , eq₆) with ++? Ω₁ Λ₁ Ω₂ Δ₁ eq₆
mip≗⇒L⇒L-comm Γ (E ∷ .(Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω₃)) .(Ω₂ ++ A' ⇒ B' ∷ Ξ)
  {.(Γ ++ E ∷ Ω₀)} {Δ₀} {.(Ω₃ ++ Ω₂)} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₁ ++ Ω₃) , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ∷ Λ₁ ++ Ω₃ ++ Ω₂) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ B ∷ Λ₁) (Ω₃ ++ Ω₂) E |
          cases++-inj₂ Ω₂ (Ω₀ ++ B ∷ Λ₁ ++ Ω₃) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₃ (Ω₀ ++ B ∷ Λ₁) Ω₂ |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω₃ ++ Ω₂) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Ω₃ ++ Ω₂) E |
          cases++-inj₂ Ω₂ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω₃) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₃ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₂ |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ Δ₀ E |
          cases++-inj₁ (Ω₀ ++ Δ₀) Λ₁ (B' ∷ Ξ) (A ⇒ B) =
    intrp≗ (h~ ⇒L⊗R₁)
mip≗⇒L⇒L-comm Γ (E ∷ .(Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Ω₁)) .(F ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ)
  {.(Γ ++ E ∷ Ω₀)} {Δ₀} {Δ₁} {.(Ω₁ ++ F ∷ Ω₃)} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (.(F ∷ Ω₃ ++ Δ₁) , refl , refl)
  | inj₂ (F , Ω₃ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ∷ Ω₁ ++ F ∷ Ω₃ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ B ∷ Ω₁ ++ F ∷ Ω₃) Δ₁ E |
          cases++-inj₂ (F ∷ Ω₃ ++ Δ₁) (Ω₀ ++ B ∷ Ω₁) Ξ (A' ⇒ B') |
          ++?-inj₂ (Ω₀ ++ B ∷ Ω₁) Ω₃ Δ₁ F |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Ω₁ ++ F ∷ Ω₃ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Ω₁ ++ F ∷ Ω₃) Δ₁ E |
          cases++-inj₂ (F ∷ Ω₃ ++ Δ₁) (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) Ξ (A' ⇒ B') |
          ++?-inj₂ (Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) Ω₃ Δ₁ F |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀) (A ⇒ B ∷ Ω₁ ++ F ∷ Ω₃ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ Δ₀ E |
          cases++-inj₁ (Ω₀ ++ Δ₀) Ω₁ (F ∷ Ω₃ ++ B' ∷ Ξ) (A ⇒ B) =
    intrp≗ refl
mip≗⇒L⇒L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , eq₄) with ++? Δ Ω₀ Ω₁ Δ₀ eq₄
mip≗⇒L⇒L-comm Γ (E ∷ .(Ω₀ ++ Ω₂)) .(Ω₁ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ)
  {.(Γ ++ E ∷ Ω₀)} {.(Ω₂ ++ Ω₁)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Ω₂ ++ Ω₁) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  | inj₁ (Ω₂ , refl , refl) with Ω₁
... | []
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ B ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (B ∷ Λ₁ ++ Δ₁) Ω₀ Ξ (A' ⇒ B') |
          ++?-inj₂ Ω₀ Λ₁ Δ₁ B |
          ++?-inj₂ Γ (Ω₀ ++ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ Ω₂ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (A ⇒ B ∷ Λ₁ ++ Δ₁) (Ω₀ ++ Ω₂) Ξ (A' ⇒ B') |
          ++?-inj₂ (Ω₀ ++ Ω₂) Λ₁ Δ₁ (A ⇒ B) |
          ++?-inj₂ Γ (Ω₀ ++ Ω₂) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ Ω₂ E |
          cases++-inj₂ [] (Ω₀ ++ Ω₂) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Ω₀ [] =
    intrp≗ (g~ ((⊗L ⇒L⇒L-comm) ∘ ⊗L⇒L-comm₁))
... | H ∷ Ω₃
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ B ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (B ∷ Λ₁ ++ Δ₁) Ω₀ Ξ (A' ⇒ B') |
          ++?-inj₂ Ω₀ Λ₁ Δ₁ B |
          ++?-inj₂ Γ (Ω₀ ++ Ω₂ ++ H ∷ Ω₃ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Ω₀ ++ Ω₂ ++ H ∷ Ω₃ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (H ∷ Ω₃ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (Ω₀ ++ Ω₂) Ξ (A' ⇒ B') |
          ++?-inj₂ (Ω₀ ++ Ω₂) (Ω₃ ++ A ⇒ B ∷ Λ₁) Δ₁ H |
          ++?-inj₂ Γ (Ω₀ ++ Ω₂ ++ H ∷ Ω₃) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ (Ω₂ ++ H ∷ Ω₃) E |
          cases++-inj₂ (H ∷ Ω₃) (Ω₀ ++ Ω₂) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Ω₀ (H ∷ Ω₃) =
    intrp≗ (g~ ((⊗L ⇒L⇒L-comm) ∘ ⊗L⇒L-comm₁))
mip≗⇒L⇒L-comm Γ (E ∷ Δ) .(G ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ)
  {.(Γ ++ E ∷ Δ ++ G ∷ Ω₂)} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (E , .(Δ ++ G ∷ Ω₂ ++ Δ₀) , refl , refl)
  | inj₁ (.(Δ ++ G ∷ Ω₂) , refl , refl)
  | inj₂ (.(G ∷ Ω₂ ++ Δ₀) , refl , refl)
  | inj₂ (G , Ω₂ , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ G ∷ Ω₂ ++ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ω₂ ++ B ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (G ∷ Ω₂ ++ B ∷ Λ₁ ++ Δ₁) Δ Ξ (A' ⇒ B') |
          ++?-inj₂ Δ (Ω₂ ++ B ∷ Λ₁) Δ₁ G |
          ++?-inj₂ Γ (Δ ++ G ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
          cases++-inj₂ (G ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) Δ Ξ (A' ⇒ B') |
          ++?-inj₂ Δ (Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ₁ G |
          ++?-inj₂ Γ (Δ ++ G ∷ Ω₂ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Δ ++ G ∷ Ω₂) Δ₀ E |
          cases++-inj₂ (G ∷ Ω₂ ++ Δ₀) Δ (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₂ Δ Ω₂ Δ₀ G =
    intrp≗ (g~ ⇒L⇒L-comm)
mip≗⇒L⇒L-comm .(Γ₁ ++ Ω₀) (E ∷ Δ) Λ
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , refl , eq₂)
  | inj₂ (Ω₀ , refl , refl)
  with cases++ Ω Δ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) Λ (inj∷ eq₂ .proj₂)
mip≗⇒L⇒L-comm .(Γ₁ ++ Ω₀) (E ∷ .(Ω ++ A ⇒ B ∷ Ω₁)) Λ
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , refl , eq₂)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , eq₄) with cases++ (Λ₁ ++ Δ₁) Ω₁ Ξ Λ (sym eq₄)
mip≗⇒L⇒L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ .(Ω ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂)) Λ
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {Λ₁} {.(Ω₂ ++ Λ)} {A} {B} {A'} {B'} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ω₂ ++ Λ) B |
          cases++-inj₁ Γ₁ Λ₁ Δ₁ B |
          cases++-inj₁ (Λ₁ ++ Δ₁) Ω₂ Λ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Ω₀) (Ω ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ω₂ ++ Λ) F |
          cases++-inj₁ (Γ₁ ++ Ω₀) (Ω ++ A ⇒ B ∷ Λ₁) Δ₁ F |
          cases++-inj₁ (Ω ++ A ⇒ B ∷ Λ₁ ++ Δ₁) Ω₂ Λ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Ω₀) Ω (A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₂ ++ Λ) F |
          cases++-inj₂ Ω₀ Γ₁ Ω F |
          cases++-inj₁ Ω (Λ₁ ++ B' ∷ Ω₂) Λ (A ⇒ B) =
    intrp≗ (h~ ((⇒R ⇒L⇒L-comm) ∘ (~ ⇒L⇒R)))
mip≗⇒L⇒L-comm .(Γ₁ ++ Ω₀) (E ∷ .(Ω ++ A ⇒ B ∷ Ω₁)) .(Ω₂ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , refl , eq₂)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , eq₄)
  | inj₂ (Ω₂ , refl , eq₆) with ++? Ω₁ Λ₁ Ω₂ Δ₁ eq₆
mip≗⇒L⇒L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ .(Ω ++ A ⇒ B ∷ Ω₁)) .(Ω₂ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , eq₄)
  | inj₂ (Ω₂ , refl , eq₆)
  | inj₁ (Ω₃ , refl , refl)
  rewrite eq₄ |
          ++?-inj₂ Γ₁ (Λ₁ ++ Ω₃ ++ Ω₂) (A' ⇒ B' ∷ Ξ) B |
          cases++-inj₁ Γ₁ Λ₁ (Ω₃ ++ Ω₂) B |
          cases++-inj₂ Ω₂ (Λ₁ ++ Ω₃) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₃ Λ₁ Ω₂ |
          ++?-inj₂ (Γ₁ ++ Ω₀) (Ω ++ A ⇒ B ∷ Λ₁ ++ Ω₃ ++ Ω₂) (A' ⇒ B' ∷ Ξ) F |
          cases++-inj₁ (Γ₁ ++ Ω₀) (Ω ++ A ⇒ B ∷ Λ₁) (Ω₃ ++ Ω₂) F |
          cases++-inj₂ Ω₂ (Ω ++ A ⇒ B ∷ Λ₁ ++ Ω₃) Ξ (A' ⇒ B') |
          ++?-inj₁ Ω₃ (Ω ++ A ⇒ B ∷ Λ₁) Ω₂ |
          ++?-inj₂ (Γ₁ ++ Ω₀) Ω (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) F |
          cases++-inj₂ Ω₀ Γ₁ Ω F |
          cases++-inj₁ Ω Λ₁ (B' ∷ Ξ) (A ⇒ B) =
    intrp≗ (↜∷
      (⇒R (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax))) ,
        ((((⊗L {Γ₁ ++ Ω₀}
            (_∘_
              (~ (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Ω₀}
                {Δ₁ = MIP.D (mip [] Ω₃ Ω₂ f' refl) ∷ Ω₂} {Λ = []} {Ξ = Ξ}))
              (_∘_
                (_∘_
                  (⇒L (~ cutaxA-right (MIP.h (mip [] Ω₀ (F ∷ Ω) f refl))) refl)
                  (~ (≡to≗ (cut⇒L-cases++₁ [] Γ₁))))
                (cut-cong₂ Γ₁ refl
                  (_∘_
                    (⇒L refl
                      (_∘_
                        (_∘_
                          (~ cutaxA-left Γ₁
                            (⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                              (MIP.g (mip [] Ω₃ Ω₂ f' refl))
                              (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))
                            refl)
                          (cut-cong₂ Γ₁ refl
                            (~ cutaxA-left
                              (Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ [])
                              (⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                                (MIP.g (mip [] Ω₃ Ω₂ f' refl))
                                (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))
                              refl)))
                        (≡to≗ (cut⊗R⊗Lcases++ Γ₁ (Ω₂ ++ A' ⇒ B' ∷ Ξ)
                          {f = ax} {ax}
                          {⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                            (MIP.g (mip [] Ω₃ Ω₂ f' refl))
                            (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))}))))
                    (~ cut⇒L≗ Γ₁ ax (⊗R ax ax)
                      (⊗L (⇒L {Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []}
                        (MIP.g (mip [] Ω₃ Ω₂ f' refl))
                        (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))))
                      refl)))))
            ∘ ≡to≗ (cut⊗L-cases++₂ Γ₁ [] (Ω₂ ++ A' ⇒ B' ∷ Ξ)))
          ∘ cut-cong₂ Γ₁ refl
              (~ cut⊗L≗ Γ₁ (_ ∷ []) []
                (⇒L {[]} ax (⊗R ax ax))
                (⊗L (⇒L {Γ₁ ++ _ ∷ []}
                  (MIP.g (mip [] Ω₃ Ω₂ f' refl))
                  (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))))
                refl)) ∘
          (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (Ω₂ ++ A' ⇒ B' ∷ Ξ) Ω₀))))) ,
        ⇒R (⊗R (⇒L (cutaxA-left [] _ refl) refl) refl ∘ (~ ⇒L⊗R₁)))
      refl)
mip≗⇒L⇒L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ .(Ω ++ A ⇒ B ∷ Ω₁)) .(H ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {.(Ω₁ ++ H ∷ Ω₃)} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (.(H ∷ Ω₃ ++ Δ₁) , refl , refl)
  | inj₂ (H , Ω₃ , refl , refl)
  rewrite ++?-inj₂ Γ₁ (Ω₁ ++ H ∷ Ω₃ ++ Δ₁) (A' ⇒ B' ∷ Ξ) B |
          cases++-inj₁ Γ₁ (Ω₁ ++ H ∷ Ω₃) Δ₁ B |
          cases++-inj₂ (H ∷ Ω₃ ++ Δ₁) Ω₁ Ξ (A' ⇒ B') |
          ++?-inj₂ Ω₁ Ω₃ Δ₁ H |
          ++?-inj₂ (Γ₁ ++ Ω₀) (Ω ++ A ⇒ B ∷ Ω₁ ++ H ∷ Ω₃ ++ Δ₁) (A' ⇒ B' ∷ Ξ) F |
          cases++-inj₁ (Γ₁ ++ Ω₀) (Ω ++ A ⇒ B ∷ Ω₁ ++ H ∷ Ω₃) Δ₁ F |
          cases++-inj₂ (H ∷ Ω₃ ++ Δ₁) (Ω ++ A ⇒ B ∷ Ω₁) Ξ (A' ⇒ B') |
          ++?-inj₂ (Ω ++ A ⇒ B ∷ Ω₁) Ω₃ Δ₁ H |
          ++?-inj₂ (Γ₁ ++ Ω₀) Ω (A ⇒ B ∷ Ω₁ ++ H ∷ Ω₃ ++ B' ∷ Ξ) F |
          cases++-inj₂ Ω₀ Γ₁ Ω F |
          cases++-inj₁ Ω Ω₁ (H ∷ Ω₃ ++ B' ∷ Ξ) (A ⇒ B) =
    intrp≗ (g~ (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Ω₀} {Δ₁ = Δ₁} {Λ = H ∷ Ω₃} {Ξ = Ξ}))
mip≗⇒L⇒L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ Δ) .(Ω₁ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ)
  {Γ₁} {.(Ω₀ ++ F ∷ Δ ++ Ω₁)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f = f} {f'} {g} refl
  | inj₂ (F , .(Δ ++ Ω₁) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , refl) with Ω₁
... | []
  rewrite ++?-inj₂ (Γ₁ ++ Ω₀) (Δ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) F |
          cases++-inj₁ (Γ₁ ++ Ω₀) (Δ ++ A ⇒ B ∷ Λ₁) Δ₁ F |
          cases++-inj₂ (A ⇒ B ∷ Λ₁ ++ Δ₁) Δ Ξ (A' ⇒ B') |
          ++?-inj₂ Δ Λ₁ Δ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Ω₀) Δ (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) F |
          cases++-inj₂ Ω₀ Γ₁ Δ F |
          cases++-inj₂ [] Δ (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) =
    intrp≗ (g~ (⇒L⇒L-comm {Γ = Γ₁}
      {Δ₀ = Ω₀ ++ MIP.D (mip Ω₀ (F ∷ Δ) [] f refl) ∷ []}
      {Δ₁ = Δ₁} {Λ = Λ₁} {Ξ = Ξ}))
... | G ∷ Ω₂
  rewrite ++?-inj₂ (Γ₁ ++ Ω₀) (Δ ++ G ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (A' ⇒ B' ∷ Ξ) F |
          cases++-inj₁ (Γ₁ ++ Ω₀) (Δ ++ G ∷ Ω₂ ++ A ⇒ B ∷ Λ₁) Δ₁ F |
          cases++-inj₂ (G ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) Δ Ξ (A' ⇒ B') |
          ++?-inj₂ Δ (Ω₂ ++ A ⇒ B ∷ Λ₁) Δ₁ G |
          ++?-inj₂ (Γ₁ ++ Ω₀) (Δ ++ G ∷ Ω₂) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) F |
          cases++-inj₂ Ω₀ Γ₁ (Δ ++ G ∷ Ω₂) F |
          cases++-inj₂ (G ∷ Ω₂) Δ (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) =
    intrp≗ (g~ (⇒L⇒L-comm {Γ = Γ₁}
      {Δ₀ = Ω₀ ++ MIP.D (mip Ω₀ (F ∷ Δ) (G ∷ Ω₂) f refl) ∷ G ∷ Ω₂}
      {Δ₁ = Δ₁} {Λ = Λ₁} {Ξ = Ξ}))
