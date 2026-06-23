{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLTensorR1 where

open import IntrpWellDefCases.Base

mip≗⇒L⊗R₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ A'} {h : Ω₁ ⊢ B'}
  → (eq : Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⇒L f (⊗R g h)) eq)
      (mip Γ Δ Λ (⊗R (⇒L f g) h) eq)
mip≗⇒L⊗R₁ Γ [] Λ eq = mip[]≗ Γ Λ eq ⇒L⊗R₁
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  with ++? Γ (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) (A ⇒ B ∷ Λ₁ ++ Ω₁) eq
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ ([] , eq2 , refl) with inj∷ eq2
... | refl , eq2' with ++? Λ₁ Δ Ω₁ Λ (sym eq2')
mip≗⇒L⊗R₁ .(Γ₁ ++ Δ₁) (.(A ⇒ B) ∷ Δ) .(Ω ++ Ω₁)
  {Γ₁} {Δ₁} {.(Δ ++ Ω)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ ([] , refl , refl) | refl , refl | inj₁ (Ω , refl , refl)
  rewrite ++?-inj₂ Γ₁ (Δ ++ Ω) Ω₁ B |
          ++?-inj₂ (Γ₁ ++ Δ₁) (Δ ++ Ω) Ω₁ (A ⇒ B) |
          ++?-inj₁ Ω Δ Ω₁ |
          ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Ω) =
    intrp≗ (g~ ⇒L⊗R₁)
mip≗⇒L⊗R₁ .(Γ₁ ++ Δ₁) (.(A ⇒ B) ∷ .(Λ₁ ++ F ∷ Ω)) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(F ∷ Ω ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ ([] , refl , refl) | refl , refl | inj₂ (F , Ω , refl , refl)
  rewrite ++?-inj₂ Γ₁ Λ₁ (F ∷ Ω ++ Λ) B |
          ++?-inj₂ Λ₁ Ω Λ F |
          ++?-inj₂ (Γ₁ ++ Δ₁) Λ₁ (F ∷ Ω ++ Λ) (A ⇒ B) |
          ++?-inj₂ Λ₁ Ω Λ F |
          ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Λ₁) =
  let Fm = mip [] Δ₁ [] f refl
      G = mip Γ₁ (B ∷ Λ₁) [] g refl
      H = mip [] (F ∷ Ω) Λ h refl
      t = ⇒R (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))
      mid :
        ⊗L {Γ₁ ++ Δ₁}
          (⇒L (MIP.h Fm) (⊗R (MIP.g G) (MIP.g H)))
        ≗
        cut Γ₁ (MIP.h Fm)
          (cut Γ₁ (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))
            (⊗L (⊗R (MIP.g G) (MIP.g H))) refl)
          refl
      mid =
        (⊗L {Γ₁ ++ Δ₁}
          ((⇒L (~ cutaxA-right (MIP.h Fm)) refl
            ∘ (~ ≡to≗ (cut⇒L-cases++₁ [] Γ₁)))
           ∘
           cut-cong₂ Γ₁ refl
             (⇒L refl
               (((~ cutaxA-left Γ₁ (⊗R (MIP.g G) (MIP.g H)) refl)
                 ∘
                 cut-cong₂ Γ₁ refl
                   (~ cutaxA-left
                     (Γ₁ ++ MIP.D G ∷ [])
                     (⊗R (MIP.g G) (MIP.g H)) refl))
                ∘
                ≡to≗
                  (cut⊗R⊗Lcases++ Γ₁ Λ
                    {f = ax} {ax} {⊗R (MIP.g G) (MIP.g H)}))
              ∘
              (~ cut⇒L≗ Γ₁ ax (⊗R ax ax)
                (⊗L (⊗R (MIP.g G) (MIP.g H))) refl)))
          ∘ ≡to≗ (cut⊗L-cases++₂ Γ₁ [] Λ))
        ∘
        cut-cong₂ Γ₁ refl
          (~ cut⊗L≗ Γ₁ (_ ∷ []) []
            (⇒L {[]} ax (⊗R ax ax))
            (⊗L (⊗R (MIP.g G) (MIP.g H))) refl)
      eqg = ⊗L {Γ₁ ++ Δ₁} (~ ⇒L⊗R₁)
        ∘ (mid ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ Δ₁))))
      eqh = ⇒R (⊗R (⇒L (cutaxA-left [] _ refl) refl) refl ∘ (~ ⇒L⊗R₁))
  in intrp≗ (↜∷ (t , eqg , eqh) refl)
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (x ∷ Ω , eq2 , refl) with inj∷ eq2
... | refl , eq2' with ++? Ω Λ₁ (E ∷ Δ ++ Λ) Ω₁ eq2'
mip≗⇒L⊗R₁ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(A ⇒ B) ∷ .(Λ₁ ++ Ω') , refl , refl) | refl , refl
  | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₁ Ω' (Γ₁ ++ B ∷ Λ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ Ω' (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇒L⊗R₁)
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (x ∷ Ω , eq2 , refl) | refl , eq2' | inj₂ (F , Ω' , eqΛ₁ , eqΩ₁)
  with inj∷ eqΩ₁
... | refl , eqΩ₁' with ++? Ω' Δ Ω₁ Λ eqΩ₁'
mip≗⇒L⊗R₁ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) (E ∷ Δ) .(Ω'' ++ Ω₁)
  {Γ₁} {Δ₁} {.(Ω ++ E ∷ Δ ++ Ω'')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(A ⇒ B) ∷ Ω , refl , refl) | refl , refl
  | inj₂ (.(E) , .(Δ ++ Ω'') , refl , refl) | refl , refl
  | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ∷ Ω) (Δ ++ Ω'') Ω₁ E |
          ++?-inj₁ Ω'' Δ Ω₁ |
          ++?-inj₂ (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) (Δ ++ Ω'') Ω₁ E |
          ++?-inj₁ Ω'' Δ Ω₁ |
          ++?-inj₁ (A ⇒ B ∷ Ω) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Ω'') =
    intrp≗ (g~ ⇒L⊗R₁)
mip≗⇒L⊗R₁ .(Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) (E ∷ .(Ω' ++ F' ∷ Ω'')) Λ
  {Γ₁} {Δ₁} {.(Ω ++ E ∷ Ω')} {.(F' ∷ Ω'' ++ Λ)}
  {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(A ⇒ B) ∷ Ω , refl , refl) | refl , refl
  | inj₂ (.(E) , Ω' , refl , refl) | refl , refl
  | inj₂ (F' , Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ∷ Ω) Ω' (F' ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' Ω'' Λ F' |
          ++?-inj₂ (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) Ω' (F' ∷ Ω'' ++ Λ) E |
          ++?-inj₂ Ω' Ω'' Λ F' |
          ++?-inj₁ (A ⇒ B ∷ Ω) (Γ₁ ++ Δ₁) (E ∷ Ω') =
    intrp≗ (g~ ((~ ⊗L⇒L-comm₂) ∘ ⊗L {Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω} ⇒L⊗R₁))
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , Ω , eq1 , eq2) with cases++ Γ Γ₁ Ω Δ₁ eq1
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , Ω , eq1 , eq2) | inj₁ (Ω' , eqΓ₁ , eqΩ) with inj∷ eq2
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {.(Γ ++ E₀ ∷ Ω')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , .(Ω' ++ Δ₁) , eq1 , eq2) | inj₁ (Ω' , refl , refl) | refl , eq2'
  with cases++ (Ω' ++ Δ₁) Δ (Λ₁ ++ Ω₁) Λ eq2'
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {.(Γ ++ E ∷ Ω')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E , .(Ω' ++ Δ₁) , eq1 , eq2) | inj₁ (Ω' , refl , refl) | refl , eq2'
  | inj₁ (Ω'' , eqΔ , eqΛ₁) with ++? Ω'' Λ₁ Λ Ω₁ eqΛ₁
mip≗⇒L⊗R₁ Γ (E ∷ .(Ω' ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ Ω''')) Λ
  {.(Γ ++ E ∷ Ω')} {Δ₁} {Λ₁} {.(Ω''' ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (E , .(Ω' ++ Δ₁) , refl , refl) | inj₁ (Ω' , refl , refl) | refl , refl
  | inj₁ (.(Λ₁ ++ Ω''') , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₁ (Ω' ++ Δ₁) (Λ₁ ++ Ω''') Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ω' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) (Ω''' ++ Λ) E
  with Ω'''
... | [] rewrite ++?-inj₂ Γ (Ω' ++ B ∷ Λ₁) Λ E |
               ++?-inj₁ [] (Ω' ++ B ∷ Λ₁) Λ |
               ++?-inj₁ [] (Ω' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Λ |
               ++?-inj₂ Γ (Ω' ++ Δ₁) (A ⇒ B ∷ Λ₁) E |
               cases++-inj₁ Γ Ω' Δ₁ E |
               cases++-inj₁ (Ω' ++ Δ₁) Λ₁ [] (A ⇒ B) = intrp≗ refl
... | F ∷ Ω'''' rewrite ++?-inj₂ Γ (Ω' ++ B ∷ Λ₁) (F ∷ Ω'''' ++ Λ) E |
                         ++?-inj₂ (Ω' ++ B ∷ Λ₁) Ω'''' Λ F |
                         ++?-inj₂ (Ω' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Ω'''' Λ F |
                         ++?-inj₂ Γ (Ω' ++ Δ₁) (A ⇒ B ∷ Λ₁) E |
                         cases++-inj₁ Γ Ω' Δ₁ E |
                         cases++-inj₁ (Ω' ++ Δ₁) Λ₁ [] (A ⇒ B) = intrp≗ (h~ ⇒L⊗R₁)
mip≗⇒L⊗R₁ Γ (E ∷ .(Ω' ++ Δ₁ ++ A ⇒ B ∷ Ω'')) .(F ∷ Ω''' ++ Ω₁)
  {.(Γ ++ E ∷ Ω')} {Δ₁} {.(Ω'' ++ F ∷ Ω''')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (E , .(Ω' ++ Δ₁) , refl , refl) | inj₁ (Ω' , refl , refl) | refl , refl
  | inj₁ (Ω'' , refl , refl) | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₁ (Ω' ++ Δ₁) Ω'' (F ∷ Ω''' ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ Γ (Ω' ++ Δ₁ ++ A ⇒ B ∷ Ω'' ++ F ∷ Ω''') Ω₁ E |
          ++?-inj₂ Γ (Ω' ++ B ∷ Ω'' ++ F ∷ Ω''') Ω₁ E |
          ++?-inj₁ (F ∷ Ω''') (Ω' ++ B ∷ Ω'') Ω₁ |
          ++?-inj₁ (F ∷ Ω''') (Ω' ++ Δ₁ ++ A ⇒ B ∷ Ω'') Ω₁ |
          ++?-inj₂ Γ (Ω' ++ Δ₁) (A ⇒ B ∷ Ω'' ++ F ∷ Ω''') E |
          cases++-inj₁ Γ Ω' Δ₁ E |
          cases++-inj₁ (Ω' ++ Δ₁) Ω'' (F ∷ Ω''') (A ⇒ B) = intrp≗ refl
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {.(Γ ++ E ∷ Ω')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E , .(Ω' ++ Δ₁) , eq1 , eq2) | inj₁ (Ω' , refl , refl) | refl , eq2'
  | inj₂ (Ω'' , eqΛ , eqΩΔ₁) with ++? Δ Ω' Ω'' Δ₁ eqΩΔ₁
mip≗⇒L⊗R₁ Γ (E ∷ .(Ω' ++ Ω''')) .(Ω'' ++ A ⇒ B ∷ Λ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Ω')} {.(Ω''' ++ Ω'')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (E , .(Ω' ++ Ω''' ++ Ω'') , refl , refl) | inj₁ (Ω' , refl , refl) | refl , refl
  | inj₂ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₂ Ω'' (Ω' ++ Ω''') (Λ₁ ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ Γ (Ω' ++ Ω''' ++ Ω'' ++ A ⇒ B ∷ Λ₁) Ω₁ E |
          ++?-inj₁ Ω''' Ω' Ω'' |
          ++?-inj₁ (Ω'' ++ A ⇒ B ∷ Λ₁) (Ω' ++ Ω''') Ω₁ |
          ++?-inj₂ Γ (Ω' ++ B ∷ Λ₁) Ω₁ E |
          ++?-inj₁ (B ∷ Λ₁) Ω' Ω₁ |
          ++?-inj₂ Γ (Ω' ++ Ω''' ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Γ Ω' (Ω''' ++ Ω'') E |
          cases++-inj₂ Ω'' (Ω' ++ Ω''') Λ₁ (A ⇒ B) |
          ++?-inj₁ Ω''' Ω' Ω'' = intrp≗ (g~ (⊗L ⇒L⊗R₁ ∘ ⊗L⊗R₁))
mip≗⇒L⊗R₁ Γ (E ∷ Δ) .(F ∷ Ω''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Δ ++ F ∷ Ω''')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (E , .(Δ ++ F ∷ Ω''' ++ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω''') , refl , refl) | refl , refl
  | inj₂ (.(F ∷ Ω''' ++ Δ₁) , refl , refl) | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₂ (F ∷ Ω''' ++ Δ₁) Δ (Λ₁ ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Ω₁ E |
          ++?-inj₂ Δ Ω''' Δ₁ F |
          ++?-inj₁ (F ∷ Ω''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) Δ Ω₁ |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''' ++ B ∷ Λ₁) Ω₁ E |
          ++?-inj₁ (F ∷ Ω''' ++ B ∷ Λ₁) Δ Ω₁ |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''' ++ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Γ (Δ ++ F ∷ Ω''') Δ₁ E |
          cases++-inj₂ (F ∷ Ω''' ++ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω''' Δ₁ F = intrp≗ (g~ ⇒L⊗R₁)
mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , Ω , eq1 , eq2) | inj₂ (Ω' , eqΔ₁ , eqΓ) with inj∷ eq2
... | refl , eq2' with cases++ Ω Δ (Λ₁ ++ Ω₁) Λ eq2'
... | inj₁ (Ω'' , eqΔ , eqΛ) with ++? Ω'' Λ₁ Λ Ω₁ eqΛ
mip≗⇒L⊗R₁ .(Γ₁ ++ Ω') (E₀ ∷ .(Ω ++ A ⇒ B ∷ Λ₁ ++ Ω''')) Λ
  {Γ₁} {.(Ω' ++ E₀ ∷ Ω)} {Λ₁} {.(Ω''' ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (E₀ , Ω , refl , refl) | inj₂ (Ω' , refl , refl) | refl , refl
  | inj₁ (.(Λ₁ ++ Ω''') , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₁ Ω (Λ₁ ++ Ω''') Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Ω') (Ω ++ A ⇒ B ∷ Λ₁) (Ω''' ++ Λ) E₀ |
          ++?-inj₂ Γ₁ Λ₁ (Ω''' ++ Λ) B
  with Ω'''
... | [] rewrite ++?-inj₁ [] Λ₁ Λ |
               ++?-inj₁ [] (Ω ++ A ⇒ B ∷ Λ₁) Λ |
               ++?-inj₂ (Γ₁ ++ Ω') Ω (A ⇒ B ∷ Λ₁) E₀ |
               cases++-inj₂ Ω' Γ₁ Ω E₀ |
               cases++-inj₁ Ω Λ₁ [] (A ⇒ B) = intrp≗ (g~ ⇒L⊗R₁)
... | F ∷ Ω'''' rewrite ++?-inj₂ Λ₁ Ω'''' Λ F |
                         ++?-inj₂ (Ω ++ A ⇒ B ∷ Λ₁) Ω'''' Λ F |
                         ++?-inj₂ (Γ₁ ++ Ω') Ω (A ⇒ B ∷ Λ₁) E₀ |
                         cases++-inj₂ Ω' Γ₁ Ω E₀ |
                         cases++-inj₁ Ω Λ₁ [] (A ⇒ B) =
  let Fm = mip [] Ω' (E₀ ∷ Ω) f refl
      G = mip Γ₁ (B ∷ Λ₁) [] g refl
      H = mip [] (F ∷ Ω'''') Λ h refl
      t = ⇒R (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))
      mid :
        ⊗L {Γ₁ ++ Ω'}
          (⇒L (MIP.h Fm) (⊗R (MIP.g G) (MIP.g H)))
        ≗
        cut Γ₁ (MIP.h Fm)
          (cut Γ₁ (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))
            (⊗L (⊗R (MIP.g G) (MIP.g H))) refl)
          refl
      mid =
        (⊗L {Γ₁ ++ Ω'}
          ((⇒L (~ cutaxA-right (MIP.h Fm)) refl
            ∘ (~ ≡to≗ (cut⇒L-cases++₁ [] Γ₁)))
           ∘
           cut-cong₂ Γ₁ refl
             (⇒L refl
               (((~ cutaxA-left Γ₁ (⊗R (MIP.g G) (MIP.g H)) refl)
                 ∘
                 cut-cong₂ Γ₁ refl
                   (~ cutaxA-left
                     (Γ₁ ++ MIP.D G ∷ [])
                     (⊗R (MIP.g G) (MIP.g H)) refl))
                ∘
                ≡to≗
                  (cut⊗R⊗Lcases++ Γ₁ Λ
                    {f = ax} {ax} {⊗R (MIP.g G) (MIP.g H)}))
              ∘
              (~ cut⇒L≗ Γ₁ ax (⊗R ax ax)
                (⊗L (⊗R (MIP.g G) (MIP.g H))) refl)))
          ∘ ≡to≗ (cut⊗L-cases++₂ Γ₁ [] Λ))
        ∘
        cut-cong₂ Γ₁ refl
          (~ cut⊗L≗ Γ₁ (_ ∷ []) []
            (⇒L {[]} ax (⊗R ax ax))
            (⊗L (⊗R (MIP.g G) (MIP.g H))) refl)
      eqg = ⊗L {Γ₁ ++ Ω'} (~ ⇒L⊗R₁)
        ∘ (mid ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ Ω'))))
      eqh = ⇒R (⊗R (⇒L (cutaxA-left [] _ refl) refl) refl ∘ (~ ⇒L⊗R₁))
  in intrp≗ (↜∷ (t , eqg , eqh) refl)
mip≗⇒L⊗R₁ .(Γ₁ ++ Ω') (E₀ ∷ .(Ω ++ A ⇒ B ∷ Ω'')) .(F ∷ Ω''' ++ Ω₁)
  {Γ₁} {.(Ω' ++ E₀ ∷ Ω)} {.(Ω'' ++ F ∷ Ω''')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (E₀ , Ω , refl , refl) | inj₂ (Ω' , refl , refl) | refl , refl
  | inj₁ (Ω'' , refl , refl) | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₁ Ω Ω'' (F ∷ Ω''' ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Ω') (Ω ++ A ⇒ B ∷ Ω'' ++ F ∷ Ω''') Ω₁ E₀ |
          ++?-inj₂ Γ₁ (Ω'' ++ F ∷ Ω''') Ω₁ B |
          ++?-inj₁ (F ∷ Ω''') (Ω ++ A ⇒ B ∷ Ω'') Ω₁ |
          ++?-inj₁ (F ∷ Ω''') Ω'' Ω₁ |
          ++?-inj₂ (Γ₁ ++ Ω') Ω (A ⇒ B ∷ Ω'' ++ F ∷ Ω''') E₀ |
          cases++-inj₂ Ω' Γ₁ Ω E₀ |
          cases++-inj₁ Ω Ω'' (F ∷ Ω''') (A ⇒ B) = intrp≗ (g~ ⇒L⊗R₁)
mip≗⇒L⊗R₁ .(Γ₁ ++ Ω') (E₀ ∷ Δ) .(Ω'' ++ A ⇒ B ∷ Λ₁ ++ Ω₁)
  {Γ₁} {.(Ω' ++ E₀ ∷ Δ ++ Ω'')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (E₀ , .(Δ ++ Ω'') , refl , refl) | inj₂ (Ω' , refl , refl) | refl , refl
  | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₂ Ω'' Δ (Λ₁ ++ Ω₁) (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) Ω₁ E₀ |
          ++?-inj₁ (Ω'' ++ A ⇒ B ∷ Λ₁) Δ Ω₁ |
          ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ Ω' Γ₁ (Δ ++ Ω'') E₀ |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) = intrp≗ (g~ ⇒L⊗R₁)
