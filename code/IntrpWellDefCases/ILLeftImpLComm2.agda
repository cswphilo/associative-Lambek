{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILLeftImpLComm2 where

open import IntrpWellDefCases.Base

mip≗IL⇐L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ I ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁} {Ω₁} (⇐L {Γ₁} {Δ₁} {Λ₁ ++ Ω₁} f g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₁} {Λ₁ ++ I ∷ Ω₁} f (IL {Γ₁ ++ B ∷ Λ₁} {Ω₁} g)) eq)
mip≗IL⇐L-comm₂ Γ [] Λ eq = mip[]≗ Γ Λ eq IL⇐L-comm₂
mip≗IL⇐L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  with ++? Γ (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁) (E ∷ Δ ++ Λ) (I ∷ Ω₁) eq
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ Ω) (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₁ (Ω , eq1 , refl)
  with cases∷ Ω eq1
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁) (I ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Δ ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁ ++ I ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁) (I ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ I ∷ Δ) Δ₁ Λ
  with Λ₁
... | []
  rewrite ++?-inj₁ [] Δ₁ (I ∷ Δ) |
          ++?-inj₁ [] (Γ₁ ++ B ∷ []) (I ∷ Δ ++ Λ) =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⇐L~⊗mid-base Γ₁ Δ₁ [] Δ Λ))
        (h~ (IL⊗R₂ {Γ = []} {Δ = []} {Λ = Δ})))
... | F ∷ Ω
  rewrite ++?-inj₂ Δ₁ Ω (I ∷ Δ) F |
          ++?-inj₁ [] (Γ₁ ++ B ∷ F ∷ Ω) (I ∷ Δ ++ Λ) =
    intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⇐L~Γ Γ₁ F Ω Δ Λ {Ω = Δ₁}))
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ I ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ω' ++ E ∷ Δ ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₁ (I ∷ Ω' , refl , refl)
  | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁ ++ Ω' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁ ++ Ω') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ Ω' ++ E ∷ Δ) Δ₁ Λ
  with Λ₁ | Ω'
... | [] | []
  rewrite ++?-inj₁ [] Δ₁ (E ∷ Δ) |
          cases++-inj₁ Γ₁ (Δ₁ ++ I ∷ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ I ∷ []) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (I ∷ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ [] (E ∷ Δ) I |
          ++?-inj₁ (I ∷ []) (Γ₁ ++ B ∷ []) (E ∷ Δ ++ Λ) =
  intrp≗ (↜∷ (⊗R IR ax , eqg , refl) refl)
  where
    H₀ = mip (Γ₁ ++ B ∷ []) (E ∷ Δ) Λ g refl

    eqg : ⇐L f (IL {Γ₁ ++ B ∷ []} {MIP.D H₀ ∷ Λ} (MIP.g H₀)) ≗
      cut (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ I ∷ []) (⊗R IR ax)
        (IL {Γ₁ ++ B ⇐ A ∷ Δ₁} {I ⊗ MIP.D H₀ ∷ Λ}
          (⊗L {Γ₁ ++ B ⇐ A ∷ Δ₁} {Λ}
            (⇐L (IL {Δ₁} {[]} f) (MIP.g H₀)))) refl
    eqg rewrite cases++-inj₂ (I ∷ []) (Γ₁ ++ B ⇐ A ∷ Δ₁) Λ
                  (I ⊗ MIP.D H₀) |
                  cases++-inj₂ [] (Γ₁ ++ B ⇐ A ∷ Δ₁) Λ
                  (I ⊗ MIP.D H₀) |
                  cases++-inj₂ (B ⇐ A ∷ Δ₁ ++ I ∷ []) Γ₁ Λ
                  (MIP.D H₀) |
                  cases++-inj₂ [] (Δ₁ ++ I ∷ []) Λ (MIP.D H₀) |
                  cases++-inj₂ (B ⇐ A ∷ Δ₁) Γ₁ (MIP.D H₀ ∷ Λ) I |
                  cases++-inj₁ Δ₁ [] (MIP.D H₀ ∷ Λ) I |
                  cases++-inj₂ [] Δ₁ [] I =
      (~ (IL⇐L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = []}
            {Ω = MIP.D H₀ ∷ Λ} {f = f} {g = MIP.g H₀}))
      ∘ IL {Γ₁ ++ B ⇐ A ∷ Δ₁} {MIP.D H₀ ∷ Λ}
          (⇐L refl (~ (cutaxA-left (Γ₁ ++ B ∷ []) (MIP.g H₀) refl)))
... | [] | H ∷ Ψ
  rewrite ++?-inj₂ Δ₁ Ψ (E ∷ Δ) H |
          cases++-inj₁ Γ₁ (Δ₁ ++ I ∷ H ∷ Ψ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ I ∷ H ∷ Ψ) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (I ∷ H ∷ Ψ ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ (H ∷ Ψ) (E ∷ Δ) I |
          ++?-inj₁ (I ∷ H ∷ Ψ) (Γ₁ ++ B ∷ []) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ (IL⇐L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = []}))
... | F ∷ Ω | Ω''
  rewrite ++?-inj₂ Δ₁ (Ω ++ Ω'') (E ∷ Δ) F |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω ++ I ∷ Ω'' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω ++ I ∷ Ω'') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω ++ I ∷ Ω'' ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ (Ω ++ I ∷ Ω'') (E ∷ Δ) F |
          ++?-inj₁ (I ∷ Ω'') (Γ₁ ++ B ∷ F ∷ Ω) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ (IL⇐L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = F ∷ Ω}))
mip≗IL⇐L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with cases++ Ω Δ Ω₁ Λ (inj∷ eq2 .proj₂)
... | inj₁ (Ω' , refl , refl)
  with cases++ Γ Γ₁ Ω (B ⇐ A ∷ Δ₁ ++ Λ₁) eq1
mip≗IL⇐L-comm₂ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ I ∷ Ω')) Λ
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {Λ₁} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁) Ω' Λ I |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Δ₁ ++ Λ₁ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ (Δ₁ ++ Λ₁ ++ Ω') (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ Ω') Δ₁ Λ |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Δ₁ ++ Λ₁ ++ I ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ (Δ₁ ++ Λ₁ ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ I ∷ Ω') Δ₁ Λ |
          ++?-inj₂ Γ (Ω'' ++ B ∷ Λ₁) (I ∷ Ω' ++ Λ) E |
          cases++-inj₁ (Ω'' ++ B ∷ Λ₁) Ω' Λ I =
    intrp≗ (h~ (IL⇐L-comm₂ {Γ = E ∷ Ω''} {Δ = Δ₁} {Λ = Λ₁}))
... | inj₂ (Ω'' , eqa , eqb)
  with cases∷ Ω'' eqa
mip≗IL⇐L-comm₂ .Γ₁ (.(B ⇐ A) ∷ .(Δ₁ ++ Λ₁ ++ I ∷ Ω')) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (.(B ⇐ A) , .(Δ₁ ++ Λ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite cases++-inj₁ (Δ₁ ++ Λ₁) Ω' Λ I |
          cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Δ₁ ++ Λ₁ ++ Ω') (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ Ω') Δ₁ Λ |
          cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁ ++ I ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Δ₁ ++ Λ₁ ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ I ∷ Ω') Δ₁ Λ |
          ++?-inj₂ Γ₁ Λ₁ (I ∷ Ω' ++ Λ) B |
          cases++-inj₁ Λ₁ Ω' Λ I =
    intrp≗ (h~ (IL⇐L-comm₂ {Γ = []} {Δ = Δ₁} {Λ = Λ₁}))
... | inj₂ (Ω''' , eqc , eqd)
  with cases++ Ω''' Δ₁ Ω Λ₁ eqc
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω''') (F ∷ .(Ω'''' ++ Λ₁ ++ I ∷ Ω')) Λ
  {Γ₁} {.(Ω''' ++ F ∷ Ω'''')} {Λ₁} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (F , .(Ω'''' ++ Λ₁) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ω''') , refl , refl)
  | inj₂ (Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite cases++-inj₁ (Ω'''' ++ Λ₁) Ω' Λ I |
          cases++-inj₁ Γ₁ (Ω''' ++ F ∷ Ω'''' ++ Λ₁ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω''' (F ∷ Ω'''' ++ Λ₁ ++ Ω') (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ Ω') (Ω''' ++ F ∷ Ω'''') Λ |
          ++?-inj₁ (F ∷ Ω'''') Ω''' (Λ₁ ++ Ω') |
          cases++-inj₁ Γ₁ (Ω''' ++ F ∷ Ω'''' ++ Λ₁ ++ I ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω''' (F ∷ Ω'''' ++ Λ₁ ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ I ∷ Ω') (Ω''' ++ F ∷ Ω'''') Λ |
          ++?-inj₁ (F ∷ Ω'''') Ω''' (Λ₁ ++ I ∷ Ω') =
    intrp≗
      (~-trans
        (h~ (IL⊗R₂ {Γ = F ∷ Ω''''} {Δ = Λ₁} {Λ = Ω'}))
        (~-sym (⇐L~⊗ refl (mipIL~Δ (Γ₁ ++ B ∷ []) Λ₁ Ω' Λ {f = g}))))
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω'''') (F ∷ .(Ω ++ I ∷ Ω')) Λ
  {Γ₁} {Δ₁} {.(Ω'''' ++ F ∷ Ω)} {.(Ω' ++ Λ)} {A} {B} {f = f} {g} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Δ₁ ++ Ω'''') , refl , refl)
  | inj₂ (.(Δ₁ ++ Ω'''') , refl , refl)
  | inj₂ (Ω'''' , refl , refl)
  rewrite cases++-inj₁ Ω Ω' Λ I |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω'''' ++ F ∷ Ω ++ Ω') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω'''') (F ∷ Ω ++ Ω') (B ⇐ A) |
          ++?-inj₁ (Ω'''' ++ F ∷ Ω ++ Ω') Δ₁ Λ
  with Ω''''
... | []
  rewrite ++?-inj₁ [] Δ₁ (F ∷ Ω ++ Ω') |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω ++ I ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₁ (F ∷ Ω ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω ++ I ∷ Ω') Δ₁ Λ |
          ++?-inj₁ [] Δ₁ (F ∷ Ω ++ I ∷ Ω') |
          ++?-inj₂ (Γ₁ ++ B ∷ []) Ω (I ∷ Ω' ++ Λ) F |
          cases++-inj₁ Ω Ω' Λ I =
    intrp≗ (h~ (IL⊗R₂ {Γ = []} {Δ = F ∷ Ω} {Λ = Ω'}))
... | H ∷ Ψ
  rewrite ++?-inj₂ Δ₁ Ψ (F ∷ Ω ++ Ω') H |
          cases++-inj₁ Γ₁ (Δ₁ ++ H ∷ Ψ ++ F ∷ Ω ++ I ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ H ∷ Ψ) (F ∷ Ω ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (H ∷ Ψ ++ F ∷ Ω ++ I ∷ Ω') Δ₁ Λ |
          ++?-inj₂ Δ₁ Ψ (F ∷ Ω ++ I ∷ Ω') H |
          ++?-inj₂ (Γ₁ ++ B ∷ H ∷ Ψ) Ω (I ∷ Ω' ++ Λ) F |
          cases++-inj₁ Ω Ω' Λ I = intrp≗ refl
mip≗IL⇐L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} eq
  | inj₂ (F , Ω , eq1 , eq2)
  | inj₂ (Ω' , eqa , eqb)
  with cases++ Γ Γ₁ Ω (B ⇐ A ∷ Δ₁ ++ Λ₁) eq1
... | inj₂ (Ω'' , eqa₁ , eqb₁)
  with cases∷ Ω'' eqa₁
... | inj₁ (refl , refl , refl)
  with ++? Δ Δ₁ Ω' Λ₁ eqb
mip≗IL⇐L-comm₂ .Γ₁ (.(B ⇐ A) ∷ .(Δ₁ ++ Θ)) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {Δ₁} {.(Θ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (.(B ⇐ A) , .(Δ₁ ++ Θ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Θ , refl , refl)
  rewrite cases++-inj₂ Ω' (Δ₁ ++ Θ) Ω₁ I |
          cases++-inj₁ Γ₁ (Δ₁ ++ Θ) (Ω' ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Θ) (Ω' ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Δ₁ ++ Θ) (B ⇐ A) |
          ++?-inj₁ Θ Δ₁ (Ω' ++ Ω₁) |
          ++?-inj₁ Θ Δ₁ (Ω' ++ I ∷ Ω₁) |
          ++?-inj₂ Γ₁ (Θ ++ Ω') (I ∷ Ω₁) B |
          cases++-inj₂ Ω' Θ Ω₁ I = intrp≗ refl
mip≗IL⇐L-comm₂ .Γ₁ (.(B ⇐ A) ∷ Δ) .((H ∷ Ξ ++ Λ₁) ++ I ∷ Ω₁)
  {Γ₁} {.(Δ ++ H ∷ Ξ)} {Λ₁} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (.(B ⇐ A) , .(Δ ++ H ∷ Ξ ++ Λ₁) , refl , refl)
  | inj₂ (.(H ∷ Ξ ++ Λ₁) , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (H , Ξ , refl , refl)
  rewrite cases++-inj₂ (H ∷ Ξ ++ Λ₁) Δ Ω₁ I |
          cases++-inj₁ Γ₁ Δ (H ∷ Ξ ++ Λ₁ ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ (H ∷ Ξ ++ Λ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₂ Δ Ξ (Λ₁ ++ Ω₁) H |
          ++?-inj₂ Δ Ξ (Λ₁ ++ I ∷ Ω₁) H |
          ++?-inj₂ Γ₁ Λ₁ (I ∷ Ω₁) B |
          cases++-inj₂ Λ₁ [] Ω₁ I =
    intrp≗ (g~ IL⇐L-comm₂)
mip≗IL⇐L-comm₂ Γ (E ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {f = f} {g} eq
  | inj₂ (F , .(Δ ++ Ω') , eq1 , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ψ) , eqa₁ , eqb₁)
  | inj₂ (Ψ , eqc , refl)
  with cases++ Ψ Δ₁ (Δ ++ Ω') Λ₁ eqc
... | inj₁ (Θ , refl , eqe)
  with ++? Δ Θ Ω' Λ₁ (sym eqe)
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ψ) (F ∷ .(Θ ++ Φ)) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {.(Ψ ++ F ∷ Θ)} {.(Φ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (F , .(Θ ++ Φ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ψ) , refl , refl)
  | inj₂ (Ψ , refl , refl)
  | inj₁ (Θ , refl , refl)
  | inj₁ (Φ , refl , refl)
  rewrite cases++-inj₂ Ω' (Θ ++ Φ) Ω₁ I |
          cases++-inj₁ Γ₁ (Ψ ++ F ∷ Θ ++ Φ) (Ω' ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ψ ++ F ∷ Θ ++ Φ) (Ω' ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ψ (F ∷ Θ ++ Φ) (B ⇐ A) |
          ++?-inj₁ Φ (Ψ ++ F ∷ Θ) (Ω' ++ Ω₁) |
          ++?-inj₁ Φ (Ψ ++ F ∷ Θ) (Ω' ++ I ∷ Ω₁) |
          ++?-inj₁ (F ∷ Θ) Ψ Φ =
    intrp≗
      (~-trans
        (g~ (IL⊗L-comm₂ {Γ = Γ₁ ++ B ⇐ A ∷ Ψ} {Δ = Ω'} {Λ = Ω₁} ∘
             ⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Ψ} (IL⇐L-comm₂
               {Γ = Γ₁}
               {Δ = Ψ ++ MIP.D (mip Ψ (F ∷ Θ) [] f refl) ∷ []}
               {Λ = MIP.D (mip (Γ₁ ++ B ∷ []) Φ (Ω' ++ Ω₁) g refl) ∷ Ω'}
               {Ω = Ω₁})))
        (~-sym
          (⇐L~⊗ refl (mipIL~Λ (Γ₁ ++ B ∷ []) Φ Ω' Ω₁ {f = g}))))
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ψ) (F ∷ Δ) .((H ∷ Ξ ++ Λ₁) ++ I ∷ Ω₁)
  {Γ₁} {.(Ψ ++ F ∷ Δ ++ H ∷ Ξ)} {Λ₁} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (F , .(Δ ++ H ∷ Ξ ++ Λ₁) , refl , refl)
  | inj₂ (.(H ∷ Ξ ++ Λ₁) , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ψ) , refl , refl)
  | inj₂ (Ψ , refl , refl)
  | inj₁ (.(Δ ++ H ∷ Ξ) , refl , refl)
  | inj₂ (H , Ξ , refl , refl)
  rewrite cases++-inj₂ (H ∷ Ξ ++ Λ₁) Δ Ω₁ I |
          cases++-inj₁ Γ₁ (Ψ ++ F ∷ Δ) (H ∷ Ξ ++ Λ₁ ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ψ ++ F ∷ Δ) (H ∷ Ξ ++ Λ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ψ (F ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ψ ++ F ∷ Δ) Ξ (Λ₁ ++ Ω₁) H |
          ++?-inj₂ (Ψ ++ F ∷ Δ) Ξ (Λ₁ ++ I ∷ Ω₁) H =
    intrp≗ (g~ IL⇐L-comm₂)
mip≗IL⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Θ) (F ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {Γ₁} {Δ₁} {.(Θ ++ F ∷ Δ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (F , .(Δ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Δ₁ ++ Θ) , refl , refl)
  | inj₂ (.(Δ₁ ++ Θ) , refl , refl)
  | inj₂ (Θ , refl , refl)
  rewrite cases++-inj₂ Ω' Δ Ω₁ I |
          cases++-inj₁ Γ₁ (Δ₁ ++ Θ ++ F ∷ Δ) (Ω' ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Θ ++ F ∷ Δ) (Ω' ++ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Θ) (F ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Θ ++ F ∷ Δ) Δ₁ (Ω' ++ Ω₁) |
          ++?-inj₁ (Θ ++ F ∷ Δ) Δ₁ (Ω' ++ I ∷ Ω₁)
  with Θ
... | []
  rewrite ++?-inj₁ [] Δ₁ (F ∷ Δ) =
    intrp≗
      (~-trans
        (g~ (IL⊗L-comm₂ {Γ = Γ₁ ++ B ⇐ A ∷ Δ₁} {Δ = Ω'} {Λ = Ω₁} ∘
             ⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Δ₁} (IL⇐L-comm₂
               {Γ = Γ₁}
               {Δ = Δ₁ ++ I ∷ []}
               {Λ = MIP.D (mip (Γ₁ ++ B ∷ []) (F ∷ Δ) (Ω' ++ Ω₁) g refl) ∷ Ω'}
               {Ω = Ω₁})))
        (~-sym
          (⇐L~⊗ refl (mipIL~Λ (Γ₁ ++ B ∷ []) (F ∷ Δ) Ω' Ω₁ {f = g}))))
... | H ∷ Ξ
  rewrite ++?-inj₂ Δ₁ Ξ (F ∷ Δ) H =
    intrp≗
      (~-trans
        (g~ (IL⇐L-comm₂
          {Γ = Γ₁}
          {Δ = Δ₁}
          {Λ = H ∷ Ξ ++ MIP.D (mip (Γ₁ ++ B ∷ H ∷ Ξ) (F ∷ Δ) (Ω' ++ Ω₁) g refl) ∷ Ω'}
          {Ω = Ω₁}))
        (~-sym
          (⇐L~Γ (mipIL~Λ (Γ₁ ++ B ∷ H ∷ Ξ) (F ∷ Δ) Ω' Ω₁ {f = g}) refl)))
mip≗IL⇐L-comm₂ Γ (E ∷ Δ) .(Ω' ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Ψ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {f = f} {g} eq
  | inj₂ (E , .(Δ ++ Ω') , eq1 , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ψ , refl , eqb₁)
  with cases++ Ψ Δ (Δ₁ ++ Λ₁) Ω' eqb₁
mip≗IL⇐L-comm₂ Γ (E ∷ Δ) .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Δ ++ Ω'')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Δ ++ Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁) , refl , refl)
  | inj₂ (.(Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁) , refl , refl)
  | inj₁ (.(Δ ++ Ω'') , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₂ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁) Δ Ω₁ I |
          cases++-inj₂ Ω'' (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁ ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ Ω'' (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁ ++ Ω₁) (B ⇐ A) =
    intrp≗
      (~-trans
        (g~ (IL⇐L-comm₂
          {Γ = Γ ++ MIP.D (mip Γ (E ∷ Δ) (Ω'' ++ B ∷ Λ₁ ++ Ω₁) g refl) ∷ Ω''}
          {Δ = Δ₁}
          {Λ = Λ₁}
          {Ω = Ω₁}))
        (~-sym
          (⇐L~Λ (mipIL~Λ Γ (E ∷ Δ) (Ω'' ++ B ∷ Λ₁) Ω₁ {f = g}) refl)))
... | inj₁ (Ω'' , refl , eqd)
  with ++? Ω'' Δ₁ Ω' Λ₁ eqd
mip≗IL⇐L-comm₂ Γ (E ∷ .(Ψ ++ B ⇐ A ∷ Δ₁ ++ Θ)) .(Ω' ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Ψ)} {Δ₁} {.(Θ ++ Ω')} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ψ ++ B ⇐ A ∷ Δ₁ ++ Θ ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₁ (.(Δ₁ ++ Θ) , refl , refl)
  | inj₁ (Θ , refl , refl)
  rewrite cases++-inj₂ Ω' (Ψ ++ B ⇐ A ∷ Δ₁ ++ Θ) Ω₁ I |
          cases++-inj₁ (Γ ++ E ∷ Ψ) (Δ₁ ++ Θ) (Ω' ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ψ) (Δ₁ ++ Θ) (Ω' ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ψ) Γ (Δ₁ ++ Θ) (B ⇐ A) |
          ++?-inj₁ Θ Δ₁ (Ω' ++ Ω₁) |
          ++?-inj₁ Θ Δ₁ (Ω' ++ I ∷ Ω₁) =
    intrp≗
      (~-sym
        (⇐L~ΓΛ
          (mipIL~Λ Γ (E ∷ Ψ ++ B ∷ Θ) Ω' Ω₁ {f = g})
          refl))
mip≗IL⇐L-comm₂ Γ (E ∷ .(Ψ ++ B ⇐ A ∷ Ω'')) .((H ∷ Ξ ++ Λ₁) ++ I ∷ Ω₁)
  {.(Γ ++ E ∷ Ψ)} {.(Ω'' ++ H ∷ Ξ)} {Λ₁} {Ω₁} {A} {B} {f = f} {g} refl
  | inj₂ (E , .(Ψ ++ B ⇐ A ∷ Ω'' ++ H ∷ Ξ ++ Λ₁) , refl , refl)
  | inj₂ (.(H ∷ Ξ ++ Λ₁) , refl , refl)
  | inj₁ (Ψ , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ (H , Ξ , refl , refl)
  rewrite cases++-inj₂ (H ∷ Ξ ++ Λ₁) (Ψ ++ B ⇐ A ∷ Ω'') Ω₁ I |
          cases++-inj₁ (Γ ++ E ∷ Ψ) Ω'' (H ∷ Ξ ++ Λ₁ ++ I ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ψ) Ω'' (H ∷ Ξ ++ Λ₁ ++ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ψ) Γ Ω'' (B ⇐ A) |
          ++?-inj₂ Ω'' Ξ (Λ₁ ++ Ω₁) H |
          ++?-inj₂ Ω'' Ξ (Λ₁ ++ I ∷ Ω₁) H =
    intrp≗
      (~-trans
        (g~ (IL⇐L-comm₂ {Γ = Γ} {Δ = H ∷ Ξ} {Λ = Λ₁} {Ω = Ω₁}))
        (~-sym
          (⇐L~⇐
            refl
            (mipIL~Λ Γ (E ∷ Ψ ++ B ∷ []) Λ₁ Ω₁ {f = g}))))
