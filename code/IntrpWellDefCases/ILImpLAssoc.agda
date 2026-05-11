{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILImpLAssoc where

open import IntrpWellDefCases.Base


mip≗IL⇒L-assoc : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ : Cxt} {A B C : Fma}
  {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ₁ ++ Δ₀} {Δ₁ ++ A ⇒ B ∷ Λ₁} (⇒L f g)) eq)
      (mip Γ Δ Λ (⇒L {Γ₁}{Δ₀ ++ I ∷ Δ₁}{Λ₁} (IL {Δ₀} {Δ₁} f) g) eq)
mip≗IL⇒L-assoc Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq with cases++ (Γ₁ ++ Δ₀) Γ (Δ₁ ++ A ⇒ B ∷ Λ₁) (Δ ++ Λ) (sym eq)
... | inj₁ (Ω , refl , eq2) with cases++ Δ₁ Ω Λ₁ (Δ ++ Λ) (sym eq2)
mip≗IL⇒L-assoc .(Γ₁ ++ Δ₀ ++ I ∷ Ω) Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₁ (Ω , refl , refl) | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₁ (Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Ω' ++ Δ) Γ₁ Λ |
          ++?-inj₁ (Δ₀ ++ Δ₁ ++ A ⇒ B ∷ Ω' ++ Δ) Γ₁ Λ |
          cases++-inj₁ (Δ₀ ++ I ∷ Δ₁) (Ω' ++ Δ) Λ (A ⇒ B) |
          cases++-inj₁ (Δ₀ ++ Δ₁) (Ω' ++ Δ) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ I ∷ Δ₁) Ω' Δ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ Δ₁) Ω' Δ (A ⇒ B)
            = intrp≗ (g~ IL⇒L-assoc)
... | inj₂ (Ω' , eq1 , refl) with cases++ Ω' Δ Λ₁ Λ eq1
mip≗IL⇒L-assoc .(Γ₁ ++ Δ₀ ++ I ∷ Ω) Δ Λ {Γ₁} {Δ₀} {.(Ω ++ Ω')} {Λ₁} {A} {B} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (Δ₀ ++ I ∷ Ω ++ Ω' ++ A ⇒ B ∷ Ω'') Γ₁ Λ |
          ++?-inj₁ (Δ₀ ++ Ω ++ Ω' ++ A ⇒ B ∷ Ω'') Γ₁ Λ |
          cases++-inj₁ (Δ₀ ++ I ∷ Ω ++ Ω') Ω'' Λ (A ⇒ B) |
          cases++-inj₁ (Δ₀ ++ Ω ++ Ω') Ω'' Λ (A ⇒ B) |
          cases++-inj₂ Ω' (Γ₁ ++ Δ₀ ++ I ∷ Ω) Ω'' (A ⇒ B) |
          cases++-inj₂ Ω' (Γ₁ ++ Δ₀ ++ Ω) Ω'' (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ I ∷ Ω) Γ₁ Ω' |
          ++?-inj₁ (Δ₀ ++ Ω) Γ₁ Ω' |
          cases++-inj₁ Δ₀ Ω Ω' I
            = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc .(Γ₁ ++ A' ∷ Δ₀ ++ I ∷ Ω) Δ Λ {Γ₁} {A' ∷ Δ₀} {.(Ω ++ Ω')} {Λ₁} {A} {B} {f = f} {g} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (A' ∷ Δ₀ ++ I ∷ Ω ++ Δ) Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ (A' ∷ Δ₀ ++ Ω ++ Δ) Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω'' (A' ∷ Δ₀ ++ I ∷ Ω ++ Δ) Λ₁ (A ⇒ B) |
          cases++-inj₂ Ω'' (A' ∷ Δ₀ ++ Ω ++ Δ) Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ₁ (Δ₀ ++ I ∷ Ω) Δ A' |
          ++?-inj₂ Γ₁ (Δ₀ ++ Ω) Δ A' |
          cases++-inj₁ Δ₀ Ω (Δ ++ Ω'') I
            = intrp≗ (g~ (IL⇒L-assoc {Γ₁} {A' ∷ Δ₀} {Ω ++ _ ∷ Ω''}))
mip≗IL⇒L-assoc ._ Δ Λ {Γ₁} {[]} {_} {Λ₁} {A} {B} {f = f} {g} refl | inj₁ ([] , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (I ∷ Δ) Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ Δ Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω'' (I ∷ Δ) Λ₁ (A ⇒ B) |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ₁ [] Δ I |
          ++?-inj₁ [] Γ₁ Δ
            = intrp≗ (↜∷ (⊗R {[]} (mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.h) ax , p , refl) refl)
  where
    p : ⇒L {Γ₁}{I ∷ _  ∷ Ω''}{Λ₁} (IL {[]} (mip [] Δ Ω'' f refl .MIP.g)) g
          ≗ cut (Γ₁ ++ I ∷ [])
                (⊗R (mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.h) ax)
                (IL (⊗L {Γ₁}
                (⇒L {Γ₁ ++ _ ∷ []} {_ ∷ Ω''}
                    (mip [] Δ Ω'' f refl .MIP.g)
                    (mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.g))))
                 refl
    p rewrite cases++-inj₂ (I ∷ []) Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) (mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.D ⊗ mip [] Δ Ω'' f refl .MIP.D) |
              cases++-inj₂ [] Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) (mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.D ⊗ mip [] Δ Ω'' f refl .MIP.D) |
              cases++-inj₁ (Γ₁ ++ mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.D ∷ []) Ω'' (A ⇒ B ∷ Λ₁) (mip [] Δ Ω'' f refl .MIP.D) |
              cases++-inj₂ [] (Γ₁ ++ mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.D ∷ []) Ω'' (mip [] Δ Ω'' f refl .MIP.D) |
              cases++-inj₁ Γ₁ (mip [] Δ Ω'' f refl .MIP.D ∷ Ω'') (A ⇒ B ∷ Λ₁) (mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.D) |
              cases++-inj₁ Γ₁ [] (mip [] Δ Ω'' f refl .MIP.D ∷ Ω'') (mip Γ₁ [] (B ∷ Λ₁) g refl .MIP.D)
      = ~ (IL⇒L-assoc ∘ ⇒L (IL (cutaxA-left [] _ refl)) {!!})
mip≗IL⇒L-assoc .(Γ₁ ++ I ∷ B' ∷ Ω) Δ Λ {Γ₁} {[]} {.(B' ∷ Ω ++ Ω')} {Λ₁} {A} {B} refl | inj₁ (B' ∷ Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (I ∷ B' ∷ Ω ++ Δ) Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ (B' ∷ Ω ++ Δ) Γ₁ (Ω'' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω'' (I ∷ B' ∷ Ω ++ Δ) Λ₁ (A ⇒ B) |
          cases++-inj₂ Ω'' (B' ∷ Ω ++ Δ) Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ₁ (B' ∷ Ω) Δ I |
          ++?-inj₂ Γ₁ Ω Δ B'
            = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₂ (Ω , eq1 , eq2) with cases++ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) Λ eq1 | ++? Γ Γ₁ Ω Δ₀ eq2
... | inj₁ (Ω , refl , eq4) | inj₁ (Ξ , refl , refl) with cases++ Δ₁ Ω Λ₁ Λ (sym eq4)
mip≗IL⇒L-assoc .(Γ₁ ++ Ξ) .(Ω₁ ++ I ∷ Ω) Λ {Γ₁} {.(Ξ ++ Ω₁)} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₁ (Ξ ++ Ω₁ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Ξ') Γ₁ Λ |
          cases++-inj₁ Ω₁ (Δ₁ ++ A ⇒ B ∷ Ξ') Λ I |
          cases++-inj₁ (Ξ ++ Ω₁ ++ I ∷ Δ₁) Ξ' Λ (A ⇒ B) |
          ++?-inj₁ (Ξ ++ Ω₁ ++ Δ₁ ++ A ⇒ B ∷ Ξ') Γ₁ Λ |
          cases++-inj₂ (Ω₁ ++ I ∷ Δ₁) (Γ₁ ++ Ξ) Ξ' (A ⇒ B) |
          cases++-inj₁ (Ξ ++ Ω₁ ++ Δ₁) Ξ' Λ (A ⇒ B) |
          ++?-inj₁ Ξ Γ₁ (Ω₁ ++ I ∷ Δ₁) |
          cases++-inj₂ (Ω₁ ++ Δ₁) (Γ₁ ++ Ξ) Ξ' (A ⇒ B) |
          cases++-inj₂ Ω₁ Ξ Δ₁ I |
          ++?-inj₁ Ξ Γ₁ (Ω₁ ++ Δ₁)
            = intrp≗ (h~ (IL⇒R ∘ ⇒R IL⇒L-assoc))
mip≗IL⇒L-assoc ._ .(Ω₁ ++ I ∷ Ω) Λ {Γ₁} {._} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ ([] , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite cases++-inj₁ Ω₁ Ω (Ξ' ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₁ (Ω₁ ++ I ∷ Ω) Γ₁ (Ξ' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ (Ω₁ ++ Ω) Γ₁ (Ξ' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ξ' (Ω₁ ++ I ∷ Ω) Λ₁ (A ⇒ B) |
          cases++-inj₂ Ξ' (Ω₁ ++ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Γ₁ (Ω₁ ++ I ∷ Ω) |
          ++?-inj₁ [] Γ₁ (Ω₁ ++ Ω) |
          cases++-inj₁ Ω₁ Ω Ξ' I
            = intrp≗ (h~ IL⊗R₂)
mip≗IL⇒L-assoc .(Γ₁ ++ _ ∷ Ξ) .(Ω₁ ++ I ∷ Ω) Λ {Γ₁} {.(_ ∷ Ξ ++ Ω₁)} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ (A' ∷ Ξ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite cases++-inj₁ Ω₁ Ω (Ξ' ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₁ (A' ∷ Ξ ++ Ω₁ ++ I ∷ Ω) Γ₁ (Ξ' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ (A' ∷ Ξ ++ Ω₁ ++ Ω) Γ₁ (Ξ' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ξ' (A' ∷ Ξ ++ Ω₁ ++ I ∷ Ω) Λ₁ (A ⇒ B) |
          cases++-inj₂ Ξ' (A' ∷ Ξ ++ Ω₁ ++ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ₁ Ξ (Ω₁ ++ I ∷ Ω) A' |
          ++?-inj₂ Γ₁ Ξ (Ω₁ ++ Ω) A' |
          cases++-inj₂ Ω₁ Ξ (Ω ++ Ξ') I |
          cases++-inj₁ Ω₁ Ω Ξ' I = intrp≗ refl
mip≗IL⇒L-assoc Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} eq | inj₂ (Ω₁ , eq1 , eq2) | inj₁ (Ω , refl , eq4) | inj₂ (C' , Ξ , refl , refl) with cases++ Δ₁ Ω Λ₁ Λ (sym eq4)
mip≗IL⇒L-assoc Γ .((C' ∷ Ξ ++ Δ₀) ++ I ∷ Ω) Λ {.(Γ ++ C' ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} refl | inj₂ (.(C' ∷ Ξ ++ Δ₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite cases++-inj₁ (Ξ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Ξ') Λ I |
          ++?-inj₁ (Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Ξ') (Γ ++ C' ∷ Ξ) Λ |
          ++?-inj₁ (Δ₀ ++ Δ₁ ++ A ⇒ B ∷ Ξ') (Γ ++ C' ∷ Ξ) Λ |
          cases++-inj₁ (Δ₀ ++ I ∷ Δ₁) Ξ' Λ (A ⇒ B) |
          cases++-inj₁ (Δ₀ ++ Δ₁) Ξ' Λ (A ⇒ B) |
          cases++-inj₂ (C' ∷ Ξ ++ Δ₀ ++ I ∷ Δ₁) Γ Ξ' (A ⇒ B) |
          cases++-inj₂ (C' ∷ Ξ ++ Δ₀ ++ Δ₁) Γ Ξ' (A ⇒ B) |
          ++?-inj₂ Γ Ξ (Δ₀ ++ I ∷ Δ₁) C' |
          ++?-inj₂ Γ Ξ (Δ₀ ++ Δ₁) C'
            = intrp≗ (h~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ .((C' ∷ Ξ ++ Δ₀) ++ I ∷ Ω) Λ {.(Γ ++ C' ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} refl | inj₂ (.(C' ∷ Ξ ++ Δ₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite cases++-inj₁ (Ξ ++ Δ₀) Ω (Ξ' ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₁ (Δ₀ ++ I ∷ Ω) (Γ ++ C' ∷ Ξ) (Ξ' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ (Δ₀ ++ Ω) (Γ ++ C' ∷ Ξ) (Ξ' ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ξ' (Δ₀ ++ I ∷ Ω) Λ₁ (A ⇒ B) |
          cases++-inj₂ Ξ' (Δ₀ ++ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₁ (C' ∷ Ξ) Γ (Δ₀ ++ I ∷ Ω) |
          ++?-inj₁ (C' ∷ Ξ) Γ (Δ₀ ++ Ω) |
          cases++-inj₁ Δ₀ Ω Ξ' I
            = intrp≗ (h~ IL⊗R₂)
mip≗IL⇒L-assoc Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} refl | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω , refl , refl) | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₁ Δ Γ₁ (Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ Δ Γ₁ (Ω ++ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ (Ω ++ I ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          cases++-inj₂ (Ω ++ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Γ₁ Δ |
          cases++-inj₂ Ω Δ Δ₁ I
            = intrp≗ (g~ (IL⊗L-comm₂ ∘ ⊗L IL⇒L-assoc))
mip≗IL⇒L-assoc Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f = f} refl | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω , refl , refl) | inj₁ (A' ∷ Ξ , refl , refl)
  rewrite cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₁ (A' ∷ Ξ ++ Δ) Γ₁ (Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ (A' ∷ Ξ ++ Δ) Γ₁ (Ω ++ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ (Ω ++ I ∷ Δ₁) (A' ∷ Ξ ++ Δ) Λ₁ (A ⇒ B) |
          cases++-inj₂ (Ω ++ Δ₁) (A' ∷ Ξ ++ Δ) Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ₁ Ξ Δ A' |
          cases++-inj₂ (Δ ++ Ω) Ξ Δ₁ I |
          cases++-inj₂ Ω Δ Δ₁ I
            = intrp≗ (g~ (IL⇒L-assoc {_}{A' ∷ Ξ ++ _ ∷ Ω}))
mip≗IL⇒L-assoc Γ [] Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , refl)
  rewrite ++?-inj₂ Γ Ξ (Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) C' |
          ++?-inj₂ Γ Ξ (Δ₀ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) C'
            = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ (x ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₂ (Ω₁ , eq1 , eq2) | inj₂ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , eq5) with inj∷ eq5
... | refl , eq3 with ++? Ξ Δ Δ₀ Ω eq3
mip≗IL⇒L-assoc Γ (x ∷ Δ) .(Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₁ ([] , refl , refl)
   rewrite cases++-inj₂ Δ₀ Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
           ++?-inj₁ [] (Γ ++ x ∷ Δ) (Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) |
           ++?-inj₁ [] (Γ ++ x ∷ Δ) (Δ₀ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) |
           ++?-inj₁ (x ∷ Δ) Γ []
             = intrp≗ (g~ (IL⊗L-comm₂ ∘ ⊗L IL⇒L-assoc))
mip≗IL⇒L-assoc Γ (x ∷ Δ) .(Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₁ (A' ∷ Ξ' , refl , refl)
   rewrite cases++-inj₂ (A' ∷ Ξ' ++ Δ₀) Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
           ++?-inj₂ (Γ ++ x ∷ Δ) Ξ' (Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) A' |
           ++?-inj₂ (Γ ++ x ∷ Δ) Ξ' (Δ₀ ++ Δ₁ ++ A ⇒ B ∷ Λ₁) A'
             = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ (x ∷ Δ) .(Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₂ (C'' , Ξ' , refl , refl)
  rewrite cases++-inj₂ Ω (Ξ ++ C'' ∷ Ξ') (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₁ (C'' ∷ Ξ') (Γ ++ x ∷ Ξ) (Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₁ (C'' ∷ Ξ') (Γ ++ x ∷ Ξ) (Ω ++ Δ₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ (Ω ++ I ∷ Δ₁) Ξ' Λ₁ (A ⇒ B) |
          cases++-inj₂ (Ω ++ Δ₁) Ξ' Λ₁ (A ⇒ B) |
          ++?-inj₁ (x ∷ Ξ) Γ (C'' ∷ Ξ') |
          cases++-inj₂ Ω Ξ' Δ₁ I
            = intrp≗ (g~ (IL⊗L-comm₂ ∘ ⊗L IL⇒L-assoc))
