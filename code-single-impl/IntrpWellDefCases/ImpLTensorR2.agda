{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLTensorR2 where

open import IntrpWellDefCases.Base

⇒L⊗R₂-assoc-eqg : ∀ Γ Λ₀ Λ₁ {A B A' B' DG DH DK : Fma}
  {gG : Γ ++ DG ∷ [] ⊢ A'}
  {gH : DH ∷ B ∷ Λ₁ ⊢ B'}
  {gK : DK ∷ Λ₀ ⊢ A}
  → ⊗L {Γ} {Λ₀ ++ A ⇒ B ∷ Λ₁}
      (⇒L {Γ ++ DG ⊗ DH ∷ []} {DK ∷ Λ₀} {Λ₁}
        gK (⊗L {Γ} {B ∷ Λ₁} (⊗R gG gH))) ≗
    cut Γ (⊗L {[]} (⊗L {[]} (⊗R ax (⊗R ax ax))))
      (⊗L {Γ} {Λ₀ ++ A ⇒ B ∷ Λ₁}
        (⊗R gG
          (⊗L {[]} {Λ₀ ++ A ⇒ B ∷ Λ₁}
            (⇒L {DH ∷ []} {DK ∷ Λ₀} {Λ₁} gK gH)))) refl
⇒L⊗R₂-assoc-eqg Γ Λ₀ Λ₁ {A} {B} {DG = DG} {DH} {DK}
  rewrite cases++-inj₂ [] Γ (Λ₀ ++ A ⇒ B ∷ Λ₁) (DG ⊗ (DH ⊗ DK)) |
          cases++-inj₂ [] (Γ ++ DG ∷ []) (Λ₀ ++ A ⇒ B ∷ Λ₁) (DH ⊗ DK) |
          cases++-inj₁ Γ [] (DH ∷ DK ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) DG =
  (⊗L
    ((~ (⊗L⇒L-comm₁ {Γ = Γ} {Δ = DK ∷ Λ₀} {Λ = []} {Ω = Λ₁}))
     ∘ ⊗L (⇒L⊗R₂ {Γ = DH ∷ []} {Δ = DK ∷ Λ₀} {Λ = Λ₁}
                    {Ω = Γ ++ DG ∷ []})))
  ∘ ⊗L
      (⊗L
        (⊗R (~ cutaxA-left Γ _ refl)
          (⇒L (~ cutaxA-left [] _ refl) (~ cutaxA-left [] _ refl))))

⇒L⊗R₂-unit-eqg : ∀ Γ Λ₀ Λ₁ {A B A' B' DG : Fma}
  {gG : Γ ++ DG ∷ [] ⊢ A'}
  {f : Λ₀ ⊢ A}
  {h : B ∷ Λ₁ ⊢ B'}
  → ⊗R gG (⇒L {[]} {Λ₀} {Λ₁} f h) ≗
    cut Γ (⊗R ax IR)
      (⊗L {Γ} {Λ₀ ++ A ⇒ B ∷ Λ₁}
        (⇒L {Γ ++ DG ∷ []} {I ∷ Λ₀} {Λ₁}
          (IL {[]} {Λ₀} f) (⊗R gG h))) refl
⇒L⊗R₂-unit-eqg Γ Λ₀ Λ₁ {A} {B} {DG = DG}
  rewrite cases++-inj₂ [] Γ (Λ₀ ++ A ⇒ B ∷ Λ₁) (DG ⊗ I) |
          cases++-inj₁ (Γ ++ DG ∷ []) Λ₀ (A ⇒ B ∷ Λ₁) I |
          cases++-inj₂ [] (Γ ++ DG ∷ []) Λ₀ I |
          cases++-inj₁ Γ Λ₀ (A ⇒ B ∷ Λ₁) DG |
          cases++-inj₁ Γ [] Λ₀ DG |
          cases++-inj₁ Γ [] (B ∷ Λ₁) DG =
  (~ (⇒L⊗R₂ {Γ = []} {Δ = Λ₀} {Λ = Λ₁} {Ω = Γ ++ DG ∷ []}))
  ∘ ⇒L refl (⊗R (~ cutaxA-left Γ _ refl) refl)

⇒L⊗R₂-assoc~ : ∀ Γ {Δ₀ Δ₁ Δ₂ Λ₀ Λ₁ : Cxt} {A B A' B' : Fma}
  → (G : MIP Γ Δ₀ [] A')
  → (H : MIP [] Δ₁ (B ∷ Λ₁) B')
  → (K : MIP [] Δ₂ Λ₀ A)
  → MIP≗ Γ (Δ₀ ++ Δ₁ ++ Δ₂) (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⊗ B')
      (⇒L~⊗' K (⊗R~' G H))
      (⊗R~' G (⇒L~⊗' K H))
⇒L⊗R₂-assoc~ Γ {Λ₀ = Λ₀} {Λ₁} {A} {B}
  (intrp DG gG hG) (intrp DH gH hH) (intrp DK gK hK) =
  let t : ((DG ⊗ DH) ⊗ DK) ∷ [] ⊢ DG ⊗ (DH ⊗ DK)
      t = ⊗L {[]} (⊗L {[]} (⊗R ax (⊗R ax ax)))
      eqg = ⇒L⊗R₂-assoc-eqg Γ Λ₀ Λ₁
  in intrp≗ (↝∷ (t , eqg , refl) refl)

mip≗⇒L⊗R₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Ω₁ ⊢ A'} {h : Γ₁ ++ B ∷ Λ₁ ⊢ B'}
  → (eq : Ω₁ ++ Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⇒L {Ω₁ ++ Γ₁} f (⊗R g h)) eq)
      (mip Γ Δ Λ (⊗R g (⇒L f h)) eq)
mip≗⇒L⊗R₂ Γ [] Λ eq = mip[]≗ Γ Λ eq ⇒L⊗R₂
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  with ++? Γ (Ω₁ ++ Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) (A ⇒ B ∷ Λ₁) eq
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ ([] , eq1 , eq2) with inj∷ eq1
mip≗⇒L⊗R₂ .(Ω₁ ++ Γ₁ ++ Δ₁) (.(A ⇒ B) ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Δ ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ ([] , refl , refl) | refl , refl
  rewrite ++?-inj₁ Γ₁ Ω₁ (B ∷ Δ ++ Λ) |
          ++?-inj₁ (Γ₁ ++ Δ₁) Ω₁ (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Δ₁) (A ⇒ B ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇒L⊗R₂)
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (F ∷ Ω , eq1 , eq2) with inj∷ eq1
mip≗⇒L⊗R₂ .(Ω₁ ++ Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω ++ E ∷ Δ ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(A ⇒ B) ∷ Ω , refl , refl) | refl , refl
  rewrite ++?-inj₁ (Γ₁ ++ B ∷ Ω) Ω₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω) Ω₁ (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ω) (Γ₁ ++ Δ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇒L⊗R₂)
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , Ω , eq1 , eq2) with cases++ Γ (Ω₁ ++ Γ₁) Ω Δ₁ eq1
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , Ω , eq1 , eq2) | inj₁ (Ω' , eqΓ , eqΩ)
  with cases++ Γ Ω₁ Ω' Γ₁ eqΓ
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , Ω , eq1 , eq2) | inj₁ (Ω' , eqΓ , eqΩ)
  | inj₁ (Ω'' , eqΩ₁ , eqΩ') with inj∷ eq2
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (.(E) , .(Ω'' ++ Γ₁ ++ Δ₁) , refl , eq2)
  | inj₁ (.(Ω'' ++ Γ₁) , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | refl , eq2' with cases++ (Ω'' ++ Γ₁ ++ Δ₁) Δ Λ₁ Λ eq2'
mip≗⇒L⊗R₂ Γ (E ∷ .(Ω'' ++ Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω''')) Λ
  {Γ₁} {Δ₁} {.(Ω''' ++ Λ)} {.(Γ ++ E ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Ω'' ++ Γ₁ ++ Δ₁) , refl , refl)
  | inj₁ (.(Ω'' ++ Γ₁) , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | refl , refl | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₁ (Ω'' ++ Γ₁ ++ Δ₁) Ω''' Λ (A ⇒ B) |
          ++?-inj₂ Γ Ω'' (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Ω''' ++ Λ) E |
          ++?-inj₂ Γ Ω'' (Γ₁ ++ B ∷ Ω''' ++ Λ) E
  with Γ₁
... | F ∷ Γ₁'
  rewrite ++?-inj₂ Ω'' (Γ₁' ++ B ∷ Ω''') Λ F |
          ++?-inj₂ Ω'' (Γ₁' ++ Δ₁ ++ A ⇒ B ∷ Ω''') Λ F |
          cases++-inj₁ (Γ₁' ++ Δ₁) Ω''' Λ (A ⇒ B) =
    intrp≗ (h~ ⇒L⊗R₂)
... | [] rewrite ++?-inj₂ Ω'' Ω''' Λ B with Δ₁
... | [] rewrite ++?-inj₂ Ω'' Ω''' Λ (A ⇒ B) =
  let G = mip Γ (E ∷ Ω'') [] g refl
      H = mip [] (B ∷ Ω''') Λ h refl
      t' : (I ⇒ MIP.D H) ∷ [] ⊢ MIP.D H
      t' = ⇒L {[]} {[]} {[]} IR ax
      t : (MIP.D G ⊗ (I ⇒ MIP.D H)) ∷ [] ⊢ MIP.D G ⊗ MIP.D H
      t = ⊗L {[]} (⊗R ax t')
      body = ⊗R (MIP.g G) (MIP.g H)
      p : cut [] t' (MIP.g H) refl ≗
          ⇒L {[]} {[]} {Λ} IR (MIP.g H)
      p = cut⇒L≗ [] {Δ = []} {Δ₀ = []} {Δ₁ = []} {Λ = Λ}
            IR ax (MIP.g H) refl
            ∘ ⇒L {Γ = []} {Δ = []} {Λ = Λ}
                refl (cutaxA-left [] (MIP.g H) refl)
      eqg =
        ((⊗L
          (((⊗R refl (~ p)
             ∘ ≡to≗ (cut⊗Rcases++₂ [] Λ (Γ ++ MIP.D G ∷ [])))
             ∘ (~ (cutaxA-left Γ (cut (Γ ++ MIP.D G ∷ []) t' body refl) refl)))
           ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ Λ
               {f = ax} {g = t'} {h = body})))
         ∘ (~ (cut⊗L≗ Γ [] [] (⊗R ax t') (⊗L body) refl)))
      eqh = ~ ⇒L⊗R₂
  in intrp≗ (↜∷ (t , eqg , eqh) refl)
... | F ∷ Δ₁'
  rewrite ++?-inj₂ Ω'' (Δ₁' ++ A ⇒ B ∷ Ω''') Λ F |
          cases++-inj₁ Δ₁' Ω''' Λ (A ⇒ B) =
  let G = mip Γ (E ∷ Ω'') [] g refl
      H = mip [] (B ∷ Ω''') Λ h refl
      t' : (I ⇒ MIP.D H) ∷ [] ⊢ MIP.D H
      t' = ⇒L {[]} {[]} {[]} IR ax
      t : (MIP.D G ⊗ (I ⇒ MIP.D H)) ∷ [] ⊢ MIP.D G ⊗ MIP.D H
      t = ⊗L {[]} (⊗R ax t')
      body = ⊗R (MIP.g G) (MIP.g H)
      p : cut [] t' (MIP.g H) refl ≗
          ⇒L {[]} {[]} {Λ} IR (MIP.g H)
      p = cut⇒L≗ [] {Δ = []} {Δ₀ = []} {Δ₁ = []} {Λ = Λ}
            IR ax (MIP.g H) refl
            ∘ ⇒L {Γ = []} {Δ = []} {Λ = Λ}
                refl (cutaxA-left [] (MIP.g H) refl)
      eqg =
        ((⊗L
          (((⊗R refl (~ p)
             ∘ ≡to≗ (cut⊗Rcases++₂ [] Λ (Γ ++ MIP.D G ∷ [])))
             ∘ (~ (cutaxA-left Γ (cut (Γ ++ MIP.D G ∷ []) t' body refl) refl)))
           ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ Λ
               {f = ax} {g = t'} {h = body})))
         ∘ (~ (cut⊗L≗ Γ [] [] (⊗R ax t') (⊗L body) refl)))
      eqh = ~ ⇒L⊗R₂
  in intrp≗ (↜∷ (t , eqg , eqh) refl)
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (.(E) , .(Ω'' ++ Γ₁ ++ Δ₁) , refl , eq2)
  | inj₁ (.(Ω'' ++ Γ₁) , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | refl , eq2' | inj₂ (Ω''' , eqΛ , eqΔΩ)
  with ++? Δ (Ω'' ++ Γ₁) Ω''' Δ₁ eqΔΩ
mip≗⇒L⊗R₂ Γ (E ∷ .(Ω'' ++ Γ₁ ++ Ω'''')) .(Ω''' ++ A ⇒ B ∷ Λ₁)
  {Γ₁} {.(Ω'''' ++ Ω''')} {Λ₁} {.(Γ ++ E ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Ω'' ++ Γ₁ ++ Ω'''' ++ Ω''') , refl , refl)
  | inj₁ (.(Ω'' ++ Γ₁) , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | refl , refl | inj₂ (Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite cases++-inj₂ Ω''' (Ω'' ++ Γ₁ ++ Ω'''') Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ Ω'' (Γ₁ ++ Ω'''' ++ Ω''' ++ A ⇒ B ∷ Λ₁) E |
          ++?-inj₁ Ω'''' (Ω'' ++ Γ₁) Ω'''
  with Γ₁
... | F ∷ Γ₁'
  rewrite ++?-inj₂ Γ Ω'' (F ∷ Γ₁' ++ B ∷ Λ₁) E |
          ++?-inj₂ Ω'' Γ₁' (B ∷ Λ₁) F |
          ++?-inj₂ Ω'' (Γ₁' ++ Ω'''') (Ω''' ++ A ⇒ B ∷ Λ₁) F |
          cases++-inj₂ Ω''' (Γ₁' ++ Ω'''') Λ₁ (A ⇒ B) |
          ++?-inj₁ Ω'''' Γ₁' Ω''' =
  let G = mip Γ (E ∷ Ω'') [] g refl
      H = mip [] (F ∷ Γ₁') (B ∷ Λ₁) h refl
      K = mip [] Ω'''' Ω''' f refl
  in ⇒L⊗R₂-assoc~ Γ G H K
... | [] rewrite ++?-inj₂ Γ Ω'' (B ∷ Λ₁) E with Ω''''
... | [] rewrite ++?-inj₁ [] Ω'' (B ∷ Λ₁) |
                 ++?-inj₁ [] Ω'' (Ω''' ++ A ⇒ B ∷ Λ₁) =
  let G = mip Γ (E ∷ Ω'') [] g refl
      t : MIP.D G ∷ [] ⊢ MIP.D G ⊗ I
      t = ⊗R ax IR
  in intrp≗ (↜∷ (t , ⇒L⊗R₂-unit-eqg Γ Ω''' Λ₁ , refl) refl)
... | F ∷ Ω'''''
  rewrite ++?-inj₁ [] Ω'' (B ∷ Λ₁) |
          ++?-inj₂ Ω'' Ω''''' (Ω''' ++ A ⇒ B ∷ Λ₁) F |
          cases++-inj₂ Ω''' Ω''''' Λ₁ (A ⇒ B) =
    intrp≗ (g~ (⊗L ⇒L⊗R₂))
mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (.(E) , .(Ω'' ++ Γ₁ ++ Δ₁) , refl , eq2)
  | inj₁ (.(Ω'' ++ Γ₁) , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | refl , eq2' | inj₂ (Ω''' , eqΛ , eqΔΩ)
  | inj₂ (F , Ω'''' , eqΩ , eqΔ₁)
  with cases++ Δ Ω'' Ω'''' Γ₁ eqΩ
mip≗⇒L⊗R₂ Γ (E ∷ Δ) .(F ∷ Ω''''₀ ++ Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁)
  {Γ₁} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Δ ++ F ∷ Ω''''₀)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Δ ++ F ∷ Ω''''₀ ++ Γ₁ ++ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω''''₀ ++ Γ₁) , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω''''₀) , refl , refl)
  | refl , refl | inj₂ (.(F ∷ Ω''''₀ ++ Γ₁ ++ Δ₁) , refl , refl)
  | inj₂ (F , .(Ω''''₀ ++ Γ₁) , refl , refl)
  | inj₁ (Ω''''₀ , refl , refl)
  rewrite cases++-inj₂ (F ∷ Ω''''₀ ++ Γ₁ ++ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''''₀) (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) E |
          ++?-inj₂ Δ (Ω''''₀ ++ Γ₁) Δ₁ F |
          ++?-inj₁ (F ∷ Ω''''₀) Δ (Γ₁ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ Γ (Δ ++ F ∷ Ω''''₀) (Γ₁ ++ B ∷ Λ₁) E |
          ++?-inj₁ (F ∷ Ω''''₀) Δ (Γ₁ ++ B ∷ Λ₁) =
    intrp≗ (g~ ⇒L⊗R₂)
mip≗⇒L⊗R₂ Γ (E ∷ .(Ω'' ++ Ω''''₀)) .(F ∷ Ω'''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁)
  {.(Ω''''₀ ++ F ∷ Ω'''')} {Δ₁} {Λ₁} {.(Γ ++ E ∷ Ω'')} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Ω'' ++ Ω''''₀ ++ F ∷ Ω'''' ++ Δ₁) , refl , refl)
  | inj₁ (.(Ω'' ++ Ω''''₀ ++ F ∷ Ω'''') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | refl , refl | inj₂ (.(F ∷ Ω'''' ++ Δ₁) , refl , refl)
  | inj₂ (F , Ω'''' , refl , refl)
  | inj₂ (Ω''''₀ , refl , refl)
  rewrite cases++-inj₂ (F ∷ Ω'''' ++ Δ₁) (Ω'' ++ Ω''''₀) Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ Ω'' (Ω''''₀ ++ F ∷ Ω'''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) E |
          ++?-inj₂ (Ω'' ++ Ω''''₀) Ω'''' Δ₁ F
  with Ω''''₀
... | [] rewrite ++?-inj₁ [] Ω'' (F ∷ Ω'''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) |
                 ++?-inj₂ Γ Ω'' (F ∷ Ω'''' ++ B ∷ Λ₁) E |
                 ++?-inj₁ [] Ω'' (F ∷ Ω'''' ++ B ∷ Λ₁) =
  intrp≗ (g~ ⇒L⊗R₂)
... | G ∷ Ω''''₁
  rewrite ++?-inj₂ Γ Ω'' (G ∷ Ω''''₁ ++ F ∷ Ω'''' ++ B ∷ Λ₁) E |
          ++?-inj₂ Ω'' Ω''''₁ (F ∷ Ω'''' ++ B ∷ Λ₁) G |
          ++?-inj₂ Ω'' Ω''''₁ (F ∷ Ω'''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) G |
          cases++-inj₂ (F ∷ Ω'''' ++ Δ₁) Ω''''₁ Λ₁ (A ⇒ B) |
          ++?-inj₂ Ω''''₁ Ω'''' Δ₁ F =
    intrp≗ (g~ ((~ ⊗L⇒L-comm₁) ∘ ⊗L ⇒L⊗R₂))
mip≗⇒L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ Δ) Λ
  {.(Ω'' ++ E₀ ∷ Ω')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , .(Ω' ++ Δ₁) , refl , eq2) | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl) with inj∷ eq2
mip≗⇒L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ Δ) Λ
  {.(Ω'' ++ E ∷ Ω')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (.(E) , .(Ω' ++ Δ₁) , refl , eq2) | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl) | refl , eq2' with cases++ (Ω' ++ Δ₁) Δ Λ₁ Λ eq2'
mip≗⇒L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ .(Ω' ++ Δ₁ ++ A ⇒ B ∷ Ω''')) Λ
  {.(Ω'' ++ E ∷ Ω')} {Δ₁} {.(Ω''' ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Ω' ++ Δ₁) , refl , refl) | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl) | refl , refl
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ Ω'' Ω₁ (E ∷ Ω' ++ Δ₁ ++ A ⇒ B ∷ Ω''' ++ Λ) |
          ++?-inj₁ Ω'' Ω₁ (E ∷ Ω' ++ B ∷ Ω''' ++ Λ) |
          ++?-inj₂ Ω'' (Ω' ++ Δ₁) (A ⇒ B ∷ Ω''' ++ Λ) E |
          cases++-inj₁ Ω'' Ω' Δ₁ E |
          cases++-inj₁ (Ω' ++ Δ₁) Ω''' Λ (A ⇒ B) = intrp≗ refl
... | inj₂ (Ω''' , refl , eqΛ) with ++? Δ Ω' Ω''' Δ₁ eqΛ
mip≗⇒L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ .(Ω' ++ Ω'''')) .(Ω''' ++ ((A ⇒ B) ∷ Λ₁))
  {.(Ω'' ++ E ∷ Ω')} {.(Ω'''' ++ Ω''')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Ω' ++ Ω'''' ++ Ω''') , refl , refl) | inj₁ (Ω' , refl , refl)
  | inj₂ (Ω'' , refl , refl) | refl , refl
  | inj₂ (Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₁ Ω'' Ω₁ (E ∷ Ω' ++ Ω'''' ++ Ω''' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ Ω'' Ω₁ (E ∷ Ω' ++ B ∷ Λ₁) |
          ++?-inj₂ Ω'' (Ω' ++ Ω'''' ++ Ω''') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Ω'' Ω' (Ω'''' ++ Ω''') E |
          cases++-inj₂ Ω''' (Ω' ++ Ω'''') Λ₁ (A ⇒ B) |
          ++?-inj₁ Ω'''' Ω' Ω''' =
    intrp≗
      (g~ (⊗L {Γ = Ω₁ ++ Ω''}
             (⇒L⊗R₂
               {Γ = Ω'' ++ mip Ω'' (E ∷ Ω') (B ∷ Λ₁) h refl .MIP.D ∷ []}
               {Δ = mip [] Ω'''' Ω''' f refl .MIP.D ∷ Ω'''}
               {Λ = Λ₁}
               {Ω = Ω₁})
           ∘ ⊗L⊗R₂ {Γ = Ω₁} {Δ = Ω''}
               {Λ = Ω''' ++ ((A ⇒ B) ∷ Λ₁)}))
mip≗⇒L⊗R₂ .(Ω₁ ++ Ω'') (E ∷ Δ) .(F ∷ Ω'''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁)
  {.(Ω'' ++ E ∷ Δ ++ F ∷ Ω'''')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Δ ++ F ∷ Ω'''' ++ Δ₁) , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω'''') , refl , refl)
  | inj₂ (Ω'' , refl , refl) | refl , refl
  | inj₂ (.(F ∷ Ω'''' ++ Δ₁) , refl , refl)
  | inj₂ (F , Ω'''' , refl , refl)
  rewrite ++?-inj₁ Ω'' Ω₁ (E ∷ Δ ++ F ∷ Ω'''' ++ B ∷ Λ₁) |
          ++?-inj₁ Ω'' Ω₁ (E ∷ Δ ++ F ∷ Ω'''' ++ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ Ω'' (Δ ++ F ∷ Ω'''' ++ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Ω'' (Δ ++ F ∷ Ω'''') Δ₁ E |
          cases++-inj₂ (F ∷ Ω'''' ++ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω'''' Δ₁ F =
    intrp≗
      (g~ (⇒L⊗R₂
        {Γ = Ω'' ++ mip Ω'' (E ∷ Δ) (F ∷ Ω'''' ++ B ∷ Λ₁) h refl .MIP.D ∷ F ∷ Ω''''}
        {Δ = Δ₁}
        {Λ = Λ₁}
        {Ω = Ω₁}))
mip≗⇒L⊗R₂ .(Ω₁ ++ Γ₁ ++ Ω') (E ∷ Δ) Λ
  {Γ₁} {.(Ω' ++ E₀ ∷ Ω)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (E₀ , Ω , refl , eq2) | inj₂ (Ω' , refl , refl) with inj∷ eq2
mip≗⇒L⊗R₂ .(Ω₁ ++ Γ₁ ++ Ω') (E ∷ Δ) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₂ (.(E) , Ω , refl , eq2) | inj₂ (Ω' , refl , refl) | refl , eq2'
  with cases++ Ω Δ Λ₁ Λ eq2'
mip≗⇒L⊗R₂ .(Ω₁ ++ Γ₁ ++ Ω') (E ∷ .(Ω ++ A ⇒ B ∷ Ω'')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω)} {.(Ω'' ++ Λ)} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , Ω , refl , refl) | inj₂ (Ω' , refl , refl) | refl , refl
  | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (Γ₁ ++ Ω') Ω₁ (E ∷ Ω ++ A ⇒ B ∷ Ω'' ++ Λ) |
          ++?-inj₁ Γ₁ Ω₁ (B ∷ Ω'' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ Ω') Ω (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ Ω' Γ₁ Ω E |
          cases++-inj₁ Ω Ω'' Λ (A ⇒ B) =
    intrp≗ (g~ (⇒L⊗R₂ {Γ = Γ₁} {Δ = Ω'} {Λ = Λ} {Ω = Ω₁}))
mip≗⇒L⊗R₂ .(Ω₁ ++ Γ₁ ++ Ω') (E ∷ Δ) .(Ω'' ++ (A ⇒ B) ∷ Λ₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ Ω'')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (.(E) , .(Δ ++ Ω'') , refl , refl) | inj₂ (Ω' , refl , refl) | refl , refl
  | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (Γ₁ ++ Ω') Ω₁ (E ∷ Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ Ω' Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) =
    intrp≗
      (g~ (⇒L⊗R₂
        {Γ = Γ₁}
        {Δ = Ω' ++ mip Ω' (E ∷ Δ) Ω'' f refl .MIP.D ∷ Ω''}
        {Λ = Λ₁}
        {Ω = Ω₁}))
