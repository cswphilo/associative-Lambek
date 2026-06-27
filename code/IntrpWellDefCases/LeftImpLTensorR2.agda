{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.LeftImpLTensorR2 where

open import Data.Empty using (⊥-elim)
open import IntrpWellDefCases.Base

⇐L⊗R₂-assoc-eqg : ∀ Γ Λ₀ Λ₁ {A' B' DG DH DK : Fma}
  {gG : Γ ++ DG ∷ [] ⊢ A'}
  {gH : DH ∷ Λ₁ ⊢ B'}
  {hK : Λ₀ ⊢ DK}
  → ⊗L {Γ} {Λ₀ ++ Λ₁}
      (⊗R gG (⇐L {[]} {Λ₀} {Λ₁} hK gH)) ≗
    cut Γ {DG ⊗ (DH ⇐ DK) ∷ []} {Λ = Λ₀ ++ Λ₁}
      (⇐R (⊗L {Γ = []} {Δ = DK ∷ []}
        (⊗R (ax {A = DG})
          (⇐L {Γ = []} {Δ = DK ∷ []} {Λ = []}
            (ax {A = DK}) (ax {A = DH})))))
      (⇐L {Γ} {Λ₀} {Λ₁} hK (⊗L {Γ} {Λ₁} (⊗R gG gH))) refl
⇐L⊗R₂-assoc-eqg Γ Λ₀ Λ₁ {DG = DG} {DH} {DK} {gG = gG} {gH = gH} {hK = hK}
  rewrite cases++-inj₂ [] Γ (Λ₀ ++ Λ₁) ((DG ⊗ DH) ⇐ DK) |
          cases++-inj₂ [] Γ Λ₁ (DG ⊗ DH) |
          cases++-inj₂ (DG ⊗ (DH ⇐ DK) ∷ []) Γ Λ₁ DK |
          cases++-inj₂ [] (Γ ++ DG ∷ []) Λ₁ DH |
          cases++-inj₁ Γ [] (DH ⇐ DK ∷ DK ∷ Λ₁) DG |
          cases++-inj₂ (DH ⇐ DK ∷ []) (Γ ++ DG ∷ []) Λ₁ DK =
  ⊗L
    (⊗R
      (~ cutaxA-left Γ _ refl)
      ((⇐L (~ cutaxA-right hK) refl)
      ∘ ((~ (≡to≗ (cut⇐L-cases++₁ [] []
            {Λ = []} {Λ₁ = Λ₁} {Ω = Λ₀}
            {A = DK} {B = DH}
            {f = hK} {g = ax} {h = gH})))
      ∘ cut-cong₂ (DH ⇐ DK ∷ []) refl
          (~ ((cut⇐L≗ [] (ax {A = DK}) (ax {A = DH}) gH refl)
             ∘ ⇐L refl (cutaxA-left [] gH refl))))))

mip≗⇐L⊗R₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Ω₁ ⊢ A'} {h : Γ₁ ++ B ∷ Λ₁ ⊢ B'}
  → (eq : Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⇐L {Ω₁ ++ Γ₁} {Δ₁} {Λ₁} f (⊗R {Ω₁} {Γ₁ ++ B ∷ Λ₁} g h)) eq)
      (mip Γ Δ Λ (⊗R {Ω₁} {Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁} g (⇐L {Γ₁} {Δ₁} {Λ₁} f h)) eq)
mip≗⇐L⊗R₂ Γ [] Λ eq = mip[]≗ Γ Λ eq ⇐L⊗R₂
mip≗⇐L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  with cases++ (Ω₁ ++ Γ₁) (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁) Λ (sym eq)
... | inj₁ (Ω , eq₁ , eq₂)
  with cases++ (Ω₁ ++ Γ₁) Γ Ω (E ∷ Δ) eq₁
mip≗⇐L⊗R₂ .(Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (Ω' , refl , refl)
  with ++? (Ω' ++ E ∷ Δ) Δ₁ Λ Λ₁ eq₂
... | inj₁ (Ω'' , eqΛ , eqΔ)
  with ++? Δ₁ Ω' Ω'' (E ∷ Δ) eqΔ
... | inj₁ (Ω''' , eqΩ'' , eqΔ₁)
  with cases++ [] Ω''' Δ Ω'' (sym eqΩ'')
mip≗⇐L⊗R₂ .(Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω'''' ++ Ω'')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω'''')} {.(Ω'' ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Ω'''' ++ Ω'') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (.(E ∷ Ω'''') , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₁ (E ∷ Ω'''') Ω' Ω'' |
          ++?-inj₁ (Γ₁ ++ B ⇐ A ∷ Ω') Ω₁ (E ∷ Ω'''' ++ Ω'' ++ Λ) |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω'''' ++ Ω'') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Ω'''' ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' (Ω' ++ E ∷ Ω'''') Λ |
          ++?-inj₁ (E ∷ Ω'''') Ω' Ω'' =
    intrp≗ (~-trans
      (⇐L~⊗ {Γ₀ = Ω₁ ++ Γ₁} {Γ₁ = Ω'} refl
        (mip⊗R₂~ Ω₁ (Γ₁ ++ B ∷ []) Ω'' Λ))
      (g~ ((⊗L {Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Ω'} ⇐L⊗R₂)
        ∘ ⊗L⊗R₂ {Γ = Ω₁} {Δ = Γ₁ ++ B ⇐ A ∷ Ω'} {Λ = Λ})))
mip≗⇐L⊗R₂ .(Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {.Ω'} {.(E ∷ Δ ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Δ) , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite ++?-inj₁ [] Ω' (E ∷ Δ) |
          ++?-inj₁ (Γ₁ ++ B ⇐ A ∷ Ω') Ω₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (Γ₁ ++ B ∷ []) Ω₁ (E ∷ Δ ++ Λ) |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) Ω' Λ |
          ++?-inj₁ [] Ω' (E ∷ Δ) =
    intrp≗ (g~ ((⊗L {Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Ω'} ⇐L⊗R₂)
      ∘ ⊗L⊗R₂ {Γ = Ω₁} {Δ = Γ₁ ++ B ⇐ A ∷ Ω'} {Λ = Λ}))
mip≗⇐L⊗R₂ .(Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(F ∷ Ω''' ++ E ∷ Δ ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ Δ₁ Ω''' (E ∷ Δ) F |
          ++?-inj₁ (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') Ω₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (Γ₁ ++ B ∷ F ∷ Ω''') Ω₁ (E ∷ Δ ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω''' ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ Ω''' (E ∷ Δ) F = intrp≗ (g~ ⇐L⊗R₂)
mip≗⇐L⊗R₂ .(Ω₁ ++ Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) .(F ∷ Ω'' ++ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ F ∷ Ω'')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₁ (Γ₁ ++ B ⇐ A ∷ Ω') Ω₁ (E ∷ Δ ++ F ∷ Ω'' ++ Λ₁) |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) (F ∷ Ω'' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ω' ++ E ∷ Δ) Ω'' Λ₁ F = intrp≗ (g~ ⇐L⊗R₂)
mip≗⇐L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eqΓ , eqΩ)
  with ++? Γ Ω₁ Ω' Γ₁ eqΩ
... | inj₁ (Ω'' , eqΓ₁ , eqΓ₀)
  with cases++ [] Ω' Δ (B ⇐ A ∷ Ω) (sym eqΓ)
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ .(Ω''' ++ B ⇐ A ∷ Ω)) Λ
  {.(Ω'' ++ E ∷ Ω''')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (Ω , refl , eq₂)
  | inj₂ (.(E ∷ Ω''') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  with ++? Ω Δ₁ Λ Λ₁ eq₂
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ .(Ω''' ++ ((B ⇐ A) ∷ Δ₁ ++ Ω''''))) Λ
  {.(Ω'' ++ E ∷ Ω''')} {Δ₁} {.(Ω'''' ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ Ω'''') , refl , refl)
  | inj₂ (.(E ∷ Ω''') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₁ Ω'' Ω₁ (E ∷ Ω''' ++ B ∷ Ω'''' ++ Λ) |
          ++?-inj₁ Ω'' Ω₁ (E ∷ Ω''' ++ (B ⇐ A) ∷ Δ₁ ++ Ω'''' ++ Λ) |
          cases++-inj₁ (Ω'' ++ E ∷ Ω''') (Δ₁ ++ Ω'''') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω''') Ω'' (Δ₁ ++ Ω'''') (B ⇐ A) |
          ++?-inj₁ Ω'''' Δ₁ Λ = intrp≗ refl
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ .(Ω''' ++ ((B ⇐ A) ∷ Ω))) .(F ∷ Ω'''' ++ Λ₁)
  {.(Ω'' ++ E ∷ Ω''')} {.(Ω ++ F ∷ Ω'''')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (Ω , refl , refl)
  | inj₂ (.(E ∷ Ω''') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  | inj₂ (F , Ω'''' , refl , refl)
  rewrite ++?-inj₁ Ω'' Ω₁ (E ∷ Ω''' ++ B ∷ Λ₁) |
          ++?-inj₁ Ω'' Ω₁ (E ∷ Ω''' ++ (B ⇐ A) ∷ Ω ++ F ∷ Ω'''' ++ Λ₁) |
          cases++-inj₁ (Ω'' ++ E ∷ Ω''') Ω (F ∷ Ω'''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω''') Ω'' Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω'''' Λ₁ F = intrp≗ (g~ ⇐L⊗R₂)
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω'') (.(B ⇐ A) ∷ Ω) Λ
  {Ω''} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (Ω , refl , eq₂)
  | inj₂ ([] , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ ([] , refl , refl)
  with ++? Ω Δ₁ Λ Λ₁ eq₂
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω'') ((B ⇐ A) ∷ .(Δ₁ ++ Ω''')) Λ
  {Ω''} {Δ₁} {.(Ω''' ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ Ω''') , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ Ω'' Ω₁ (B ∷ Ω''' ++ Λ) |
          ++?-inj₁ Ω'' Ω₁ (B ⇐ A ∷ Δ₁ ++ Ω''' ++ Λ) |
          cases++-inj₁ Ω'' (Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₂ [] Ω'' (Δ₁ ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' Δ₁ Λ = intrp≗ refl
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω'') ((B ⇐ A) ∷ Ω) .(F ∷ Ω''' ++ Λ₁)
  {Ω''} {.(Ω ++ F ∷ Ω''')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (Ω , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₁ Ω'' Ω₁ (B ∷ Λ₁) |
          ++?-inj₁ Ω'' Ω₁ (B ⇐ A ∷ Ω ++ F ∷ Ω''' ++ Λ₁) |
          cases++-inj₁ Ω'' Ω (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Ω'' Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω''' Λ₁ F = intrp≗ (g~ ⇐L⊗R₂)
mip≗⇐L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eqΓ , eqΩ)
  | inj₂ (F , Ω'' , eqΩ₁ , eqΩ') with ++? Ω Δ₁ Λ Λ₁ eq₂
mip≗⇐L⊗R₂ Γ (F ∷ .(Ω'' ++ Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω''')) Λ
  {Γ₁} {Δ₁} {.(Ω''' ++ Λ)} {.(Γ ++ F ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ Ω''') , refl , refl)
  | inj₂ (.(F ∷ Ω'' ++ Γ₁) , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ Ω''' Δ₁ Λ |
          ++?-inj₂ Γ Ω'' (Γ₁ ++ B ∷ Ω''' ++ Λ) F
  with Γ₁
... | [] rewrite ++?-inj₂ Ω'' Ω''' Λ B |
                 ++?-inj₂ Γ Ω'' (B ⇐ A ∷ Δ₁ ++ Ω''' ++ Λ) F |
                 ++?-inj₂ Ω'' (Δ₁ ++ Ω''') Λ (B ⇐ A) |
                 ++?-inj₁ Ω''' Δ₁ Λ = intrp≗ (h~ ⇐L⊗R₂)
... | G ∷ Γ₁' rewrite ++?-inj₂ Ω'' (Γ₁' ++ B ∷ Ω''') Λ G |
                         ++?-inj₂ Γ Ω'' (G ∷ Γ₁' ++ B ⇐ A ∷ Δ₁ ++ Ω''' ++ Λ) F |
                         ++?-inj₂ Ω'' (Γ₁' ++ B ⇐ A ∷ Δ₁ ++ Ω''') Λ G |
                         cases++-inj₁ Γ₁' (Δ₁ ++ Ω''') Λ (B ⇐ A) |
                         ++?-inj₁ Ω''' Δ₁ Λ = intrp≗ (h~ ⇐L⊗R₂)
mip≗⇐L⊗R₂ Γ (F ∷ .(Ω'' ++ Γ₁ ++ B ⇐ A ∷ Ω)) .(G ∷ Ω''' ++ Λ₁)
  {Γ₁} {.(Ω ++ G ∷ Ω''')} {Λ₁} {.(Γ ++ F ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (Ω , refl , refl)
  | inj₂ (.(F ∷ Ω'' ++ Γ₁) , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  | inj₂ (G , Ω''' , refl , refl)
  rewrite ++?-inj₂ Ω Ω''' Λ₁ G |
          ++?-inj₂ Γ Ω'' (Γ₁ ++ B ∷ Λ₁) F
  with Γ₁
... | [] rewrite ++?-inj₂ Ω'' [] Λ₁ B |
                 ++?-inj₂ Γ Ω'' (B ⇐ A ∷ Ω ++ G ∷ Ω''' ++ Λ₁) F |
                 ++?-inj₂ Ω'' Ω (G ∷ Ω''' ++ Λ₁) (B ⇐ A) |
                 ++?-inj₂ Ω Ω''' Λ₁ G =
  intrp≗
    (↜∷
      ( t
      , eqg
      , ⇐R
          ((⊗R refl
            (cutaxA-left (B ⇐ A ∷ Ω)
              (⇐L (MIP.g Km) (MIP.h Hm)) refl))
          ∘ (~ (⇐L⊗R₂ {Γ = []}
                {Δ = Ω ++ MIP.D Km ∷ []}
                {Λ = []}
                {Ω = F ∷ Ω''}))))
      refl)
  where
    Gm = mip Γ (F ∷ Ω'') [] g refl
    Hm = mip [] (B ∷ []) Λ₁ h refl
    Km = mip Ω (G ∷ Ω''') [] f refl
    t : MIP.D Gm ⊗ (MIP.D Hm ⇐ MIP.D Km) ∷ [] ⊢
        (MIP.D Gm ⊗ MIP.D Hm) ⇐ MIP.D Km
    t = ⇐R (⊗L {Γ = []} {Δ = MIP.D Km ∷ []}
      (⊗R (ax {A = MIP.D Gm})
        (⇐L {Γ = []} {Δ = MIP.D Km ∷ []} {Λ = []}
          (ax {A = MIP.D Km}) (ax {A = MIP.D Hm}))))
    eqg : ⊗L (⊗R (MIP.g Gm)
            (⇐L {Γ = []} {Δ = G ∷ Ω'''} {Λ = Λ₁} (MIP.h Km) (MIP.g Hm))) ≗
           cut Γ t
             (⇐L {Γ = Γ} {Δ = G ∷ Ω'''} {Λ = Λ₁}
               (MIP.h Km) (⊗L (⊗R (MIP.g Gm) (MIP.g Hm)))) refl
    eqg = ⇐L⊗R₂-assoc-eqg Γ (G ∷ Ω''') Λ₁
... | H ∷ Γ₁'
  rewrite ++?-inj₂ Ω'' (Γ₁' ++ B ∷ []) Λ₁ H |
          ++?-inj₂ Γ Ω'' (H ∷ Γ₁' ++ B ⇐ A ∷ Ω ++ G ∷ Ω''' ++ Λ₁) F |
          ++?-inj₂ Ω'' (Γ₁' ++ B ⇐ A ∷ Ω) (G ∷ Ω''' ++ Λ₁) H |
          cases++-inj₁ Γ₁' Ω (G ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          ++?-inj₂ Ω Ω''' Λ₁ G =
  intrp≗
    (↜∷
      ( t
      , eqg
      , ⇐R
          ((⊗R refl
            (cutaxA-left (H ∷ Γ₁' ++ B ⇐ A ∷ Ω)
              (⇐L (MIP.g Km) (MIP.h Hm)) refl))
          ∘ (~ (⇐L⊗R₂ {Γ = H ∷ Γ₁'}
                {Δ = Ω ++ MIP.D Km ∷ []}
                {Λ = []}
                {Ω = F ∷ Ω''}))))
      refl)
  where
    Gm = mip Γ (F ∷ Ω'') [] g refl
    Hm = mip [] (H ∷ Γ₁' ++ B ∷ []) Λ₁ h refl
    Km = mip Ω (G ∷ Ω''') [] f refl
    t : MIP.D Gm ⊗ (MIP.D Hm ⇐ MIP.D Km) ∷ [] ⊢
        (MIP.D Gm ⊗ MIP.D Hm) ⇐ MIP.D Km
    t = ⇐R (⊗L {Γ = []} {Δ = MIP.D Km ∷ []}
      (⊗R (ax {A = MIP.D Gm})
        (⇐L {Γ = []} {Δ = MIP.D Km ∷ []} {Λ = []}
          (ax {A = MIP.D Km}) (ax {A = MIP.D Hm}))))
    eqg : ⊗L (⊗R (MIP.g Gm)
            (⇐L {Γ = []} {Δ = G ∷ Ω'''} {Λ = Λ₁} (MIP.h Km) (MIP.g Hm))) ≗
           cut Γ t
             (⇐L {Γ = Γ} {Δ = G ∷ Ω'''} {Λ = Λ₁}
               (MIP.h Km) (⊗L (⊗R (MIP.g Gm) (MIP.g Hm)))) refl
    eqg = ⇐L⊗R₂-assoc-eqg Γ (G ∷ Ω''') Λ₁
mip≗⇐L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (Ω , eq₁ , eq₂)
  with ++? Γ Ω₁ (E ∷ Δ ++ Λ) (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁) eq
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₁ (Ω' , eq₃ , refl)
  with ++canc {xs = Γ₁} {xs' = Ω' ++ E ∷ Δ ++ Ω} Ω₁ eq₂
mip≗⇐L⊗R₂ .(Ω₁ ++ Ω') (E ∷ Δ) .(Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁)
  {.(Ω' ++ E ∷ Δ ++ Ω)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (Ω , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | refl
  rewrite ++?-inj₁ Ω' Ω₁ (E ∷ Δ ++ Ω ++ B ∷ Λ₁) |
          cases++-inj₂ Ω (Ω' ++ E ∷ Δ) (Δ₁ ++ Λ₁) (B ⇐ A) =
    intrp≗
      (g~ (⇐L⊗R₂
        {Γ = Ω' ++ mip Ω' (E ∷ Δ) (Ω ++ B ∷ Λ₁) h refl .MIP.D ∷ Ω}
        {Δ = Δ₁}
        {Λ = Λ₁}
        {Ω = Ω₁}))
mip≗⇐L⊗R₂ Γ (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ F ∷ Ω')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₂ (F , Ω' , refl , eq₄)
  with inj∷ eq₄
mip≗⇐L⊗R₂ Γ (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₂ (.(E) , Ω' , refl , eq₄)
  | refl , eq₄'
  with ++? Ω' Δ (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁) Λ eq₄'
mip≗⇐L⊗R₂ Γ (E ∷ Δ) .(Ω'' ++ Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁)
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Δ ++ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₂ (.(E) , .(Δ ++ Ω'') , refl , eq₄)
  | refl , eq₄'
  | inj₁ (Ω'' , refl , refl)
  with canc++ (Ω'' ++ Γ₁) Ω {ys = B ⇐ A ∷ Δ₁ ++ Λ₁} eq₁
mip≗⇐L⊗R₂ Γ (E ∷ Δ) .(Ω'' ++ Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁)
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Δ ++ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(Ω'' ++ Γ₁) , refl , refl)
  | inj₂ (.(E) , .(Δ ++ Ω'') , refl , refl)
  | refl , eq₄'
  | inj₁ (Ω'' , refl , refl)
  | refl
  rewrite ++?-inj₂ Γ (Δ ++ Ω'') (Γ₁ ++ B ∷ Λ₁) E |
          ++?-inj₁ Ω'' Δ (Γ₁ ++ B ∷ Λ₁) =
    intrp≗
      (g~ (⇐L⊗R₂
        {Γ = Γ₁}
        {Δ = Δ₁}
        {Λ = Λ₁}
        {Ω = Γ ++ mip Γ (E ∷ Δ) Ω'' g refl .MIP.D ∷ Ω''}))
mip≗⇐L⊗R₂ Γ (E ∷ .(Ω' ++ G ∷ Ω'')) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₂ (.(E) , Ω' , refl , eq₄)
  | refl , eq₄'
  | inj₂ (G , Ω'' , refl , eq₆)
  with cases++ Γ₁ (G ∷ Ω'') (Δ₁ ++ Λ₁) Λ (sym eq₆)
mip≗⇐L⊗R₂ Γ (E ∷ .(Ω' ++ G ∷ Ω'')) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₂ (.(E) , Ω' , refl , eq₄)
  | refl , eq₄'
  | inj₂ (G , Ω'' , refl , eq₆)
  | inj₁ (Ω''' , eq₇ , eq₈)
  with cases∷ Γ₁ eq₇
... | inj₁ (refl , refl , refl) =
  ⊥-elim (canc⊥2 (Γ ++ E ∷ Ω') eq₂)
mip≗⇐L⊗R₂ Γ (E ∷ .(Ω' ++ G ∷ Ω'''' ++ B ⇐ A ∷ Ω''')) Λ
  {.(G ∷ Ω'''')} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₂ (.(E) , Ω' , refl , eq₄)
  | refl , eq₄'
  | inj₂ (G , .(Ω'''' ++ B ⇐ A ∷ Ω''') , refl , eq₆)
  | inj₁ (Ω''' , eq₇ , eq₈)
  | inj₂ (Ω'''' , refl , refl) =
  ⊥-elim (canc⊥2 (Γ ++ E ∷ Ω' ++ G ∷ Ω'''') eq₂)
mip≗⇐L⊗R₂ Γ (E ∷ .(Ω' ++ G ∷ Ω'')) .(Ω''' ++ B ⇐ A ∷ Δ₁ ++ Λ₁)
  {.(G ∷ Ω'' ++ Ω''')} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (Ω , eq₁ , eq₂)
  | inj₂ (.(E) , Ω' , refl , eq₄)
  | refl , eq₄'
  | inj₂ (G , Ω'' , refl , eq₆)
  | inj₂ (Ω''' , refl , refl)
  with ++canc {xs = Ω'''} {xs' = Ω} (Γ ++ E ∷ Ω' ++ G ∷ Ω'') eq₂
mip≗⇐L⊗R₂ Γ (E ∷ .(Ω' ++ G ∷ Ω'')) .(Ω''' ++ B ⇐ A ∷ Δ₁ ++ Λ₁)
  {.(G ∷ Ω'' ++ Ω''')} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(Ω''') , refl , refl)
  | inj₂ (.(E) , Ω' , refl , refl)
  | refl , eq₄'
  | inj₂ (G , Ω'' , refl , refl)
  | inj₂ (Ω''' , refl , refl)
  | refl
  rewrite ++?-inj₂ Γ Ω' (G ∷ Ω'' ++ Ω''' ++ B ∷ Λ₁) E |
          ++?-inj₂ Ω' Ω'' (Ω''' ++ B ∷ Λ₁) G |
          cases++-inj₂ Ω''' Ω'' (Δ₁ ++ Λ₁) (B ⇐ A) =
  intrp≗ (g~ ((~ ⊗L⇐L-comm₁) ∘ (⊗L ⇐L⊗R₂)))
