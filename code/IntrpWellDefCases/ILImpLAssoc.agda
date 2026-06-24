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
mip≗IL⇒L-assoc Γ [] Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq
  with cases++ (Γ₁ ++ Δ₀) Γ (Δ₁ ++ A ⇒ B ∷ Λ₁) Λ (sym eq)
... | inj₁ (Ω , refl , eq2)
  with cases++ Δ₁ Ω Λ₁ Λ (sym eq2)
mip≗IL⇒L-assoc .(Γ₁ ++ Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Ω') [] Λ {Γ₁} {Δ₀} {Δ₁} {.(Ω' ++ Λ)} {A} {B} refl
  | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) =
    intrp≗ (g~ (IL {Γ₁ ++ Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Ω'} {Λ}
      (IL⇒L-assoc {Γ₁} {Δ₀} {Δ₁} {Ω' ++ Λ})))
mip≗IL⇒L-assoc .(Γ₁ ++ Δ₀ ++ I ∷ Ω) [] .(Ω' ++ A ⇒ B ∷ Λ₁) {Γ₁} {Δ₀} {.(Ω ++ Ω')} {Λ₁} {A} {B} refl
  | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) =
    intrp≗ (g~ (IL {Γ₁ ++ Δ₀ ++ I ∷ Ω} {Ω' ++ A ⇒ B ∷ Λ₁}
      (IL⇒L-assoc {Γ₁} {Δ₀} {Ω ++ Ω'} {Λ₁})))
mip≗IL⇒L-assoc Γ [] Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq
  | inj₂ (Ω , refl , eqΓ)
  with ++? Γ Γ₁ Ω Δ₀ eqΓ
mip≗IL⇒L-assoc .(Γ₁ ++ Ξ) [] .(Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(Ξ ++ Ω)} {Δ₁} {Λ₁} {A} {B} refl
  | inj₂ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ₁ ++ Ξ} {Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁}
      (IL⇒L-assoc {Γ₁} {Ξ ++ Ω} {Δ₁} {Λ₁})))
mip≗IL⇒L-assoc Γ [] .(F ∷ Ξ ++ Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ F ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl
  | inj₂ (.(F ∷ Ξ ++ Δ₀) , refl , refl) | inj₂ (F , Ξ , refl , refl) =
    intrp≗ (g~ (IL {Γ} {F ∷ Ξ ++ Δ₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁}
      (IL⇒L-assoc {Γ ++ F ∷ Ξ} {Δ₀} {Δ₁} {Λ₁})))
mip≗IL⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq with cases++ (Γ₁ ++ Δ₀) Γ (Δ₁ ++ A ⇒ B ∷ Λ₁) (E ∷ Δ ++ Λ) (sym eq)
... | inj₁ (Ω , refl , eq2) with cases++ Δ₁ Ω Λ₁ (E ∷ Δ ++ Λ) (sym eq2)
mip≗IL⇒L-assoc .(Γ₁ ++ Δ₀ ++ I ∷ Ω) (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₁ (Ω , refl , refl) | inj₁ (Ω' , refl , refl)
  rewrite ++?-inj₁ (I ∷ Δ₁ ++ A ⇒ B ∷ Ω') (Γ₁ ++ Δ₀) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ω') (Γ₁ ++ Δ₀ ++ I ∷ Δ₁) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (A ⇒ B ∷ Ω') (Γ₁ ++ Δ₀ ++ Δ₁) (E ∷ Δ ++ Λ)
            = intrp≗ (g~ IL⇒L-assoc)
... | inj₂ (Ω' , eq1 , refl) with cases++ Ω' (E ∷ Δ) Λ₁ Λ eq1
... | inj₁ (Ω'' , eqMid , refl) with cases∷ Ω' eqMid
mip≗IL⇒L-assoc .(Γ₁ ++ Δ₀ ++ I ∷ Ω) (A ⇒ B ∷ Ω'') Λ {Γ₁} {Δ₀} {Ω} {.(Ω'' ++ Λ)} {A} {B} refl
  | inj₁ (Ω , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ (I ∷ Ω) (Γ₁ ++ Δ₀) (A ⇒ B ∷ Ω'' ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ Ω) (A ⇒ B ∷ Ω'' ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ I ∷ Ω) (A ⇒ B ∷ Ω'' ++ Λ)
            = intrp≗
                (~-trans
                  (g~ IL⇒L-assoc)
                  (~-sym (⇒L~⇒ (mipIL~Δ [] Δ₀ Ω []) refl)))
mip≗IL⇒L-assoc .(Γ₁ ++ Δ₀ ++ I ∷ Ω) (E ∷ .(Ω₀ ++ A ⇒ B ∷ Ω'')) Λ {Γ₁} {Δ₀} {.(Ω ++ E ∷ Ω₀)} {.(Ω'' ++ Λ)} {A} {B} refl
  | inj₁ (Ω , refl , refl) | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (Ω₀ , refl , refl)
  rewrite ++?-inj₁ (I ∷ Ω) (Γ₁ ++ Δ₀) (E ∷ Ω₀ ++ A ⇒ B ∷ Ω'' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ Ω) Ω₀ (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ (Δ₀ ++ Ω) Γ₁ Ω₀ E |
          cases++-inj₁ Ω₀ Ω'' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ I ∷ Ω) Ω₀ (A ⇒ B ∷ Ω'' ++ Λ) E |
          cases++-inj₂ (Δ₀ ++ I ∷ Ω) Γ₁ Ω₀ E |
          cases++-inj₁ Ω₀ Ω'' Λ (A ⇒ B)
            = intrp≗
                (~-trans
                  (g~ IL⇒L-assoc)
                  (~-sym (⇒L~⇒ (mipIL~Δ [] Δ₀ Ω (E ∷ Ω₀)) refl)))
mip≗IL⇒L-assoc .(Γ₁ ++ A' ∷ Δ₀ ++ I ∷ Ω) (E ∷ Δ) Λ {Γ₁} {A' ∷ Δ₀} {.(Ω ++ Ω')} {Λ₁} {A} {B} {f = f} {g} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (I ∷ Ω) (Γ₁ ++ A' ∷ Δ₀) (E ∷ Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ A' ∷ Δ₀ ++ I ∷ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          ++?-inj₂ (Γ₁ ++ A' ∷ Δ₀ ++ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ∷ Δ₀ ++ I ∷ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ (A' ∷ Δ₀ ++ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ (I ∷ Ω) (A' ∷ Δ₀) (E ∷ Δ ++ Ω'')
            = intrp≗ (g~ (IL⇒L-assoc {Γ₁} {A' ∷ Δ₀} {Ω ++ _ ∷ Ω''}))
mip≗IL⇒L-assoc ._ (E ∷ Δ) Λ {Γ₁} {[]} {_} {Λ₁} {A} {B} {f = f} {g} refl | inj₁ ([] , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (I ∷ []) Γ₁ (E ∷ Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ Γ₁ (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ [] Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ []) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (I ∷ []) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ (I ∷ []) [] (E ∷ Δ ++ Ω'')
            = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc .(Γ₁ ++ I ∷ B' ∷ Ω) (E ∷ Δ) Λ {Γ₁} {[]} {.(B' ∷ Ω ++ Ω')} {Λ₁} {A} {B} refl | inj₁ (B' ∷ Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite ++?-inj₁ (I ∷ B' ∷ Ω) Γ₁ (E ∷ Δ ++ Ω'' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ B' ∷ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (B' ∷ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ I ∷ B' ∷ Ω) (Δ ++ Ω'') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (I ∷ B' ∷ Ω) Γ₁ (Δ ++ Ω'') E |
          cases++-inj₂ Ω'' Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ (I ∷ B' ∷ Ω) [] (E ∷ Δ ++ Ω'')
            = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₂ (Ω₁ , eq1 , eq2) with cases++ Ω₁ (E ∷ Δ) (Δ₁ ++ A ⇒ B ∷ Λ₁) Λ eq1 | ++? Γ Γ₁ Ω₁ Δ₀ eq2
mip≗IL⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq
  | inj₂ (Ω₁ , eqTop , eqΓ) | inj₁ (Ω , eqΔ , eq4) | inj₁ (Ξ , refl , refl)
  with cases∷ Ω₁ eqΔ | cases++ Δ₁ Ω Λ₁ Λ (sym eq4)
mip≗IL⇒L-assoc .(Γ₁ ++ Ξ) (I ∷ .(Δ₁ ++ A ⇒ B ∷ Ξ')) Λ {Γ₁} {Ξ} {Δ₁} {.(Ξ' ++ Λ)} {A} {B} refl
  | inj₂ ([] , refl , refl) | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ξ') , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₁ (refl , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ Ξ) (I ∷ Δ₁ ++ A ⇒ B ∷ Ξ' ++ Λ) |
          ++?-inj₂ (Γ₁ ++ Ξ) Δ₁ (A ⇒ B ∷ Ξ' ++ Λ) I |
          cases++-inj₂ Ξ Γ₁ Δ₁ I |
          cases++-inj₁ Δ₁ Ξ' Λ (A ⇒ B)
            = intrp≗
                (~-trans
                  (IL~Δ {Δ₀ = []} {Δ₁ = Δ₁ ++ A ⇒ B ∷ Ξ'}
                    (mip⇒L~⇒ Γ₁ Ξ Δ₁ Ξ' Λ))
                  (~-trans
                    (h~ (IL⇒R ∘ ⇒R IL⇒L-assoc))
                    (~-sym (⇒L~⇒ (mipIL~Λ [] Ξ [] Δ₁) refl))))
mip≗IL⇒L-assoc .(Γ₁ ++ Ξ) (E ∷ .(Ω₀ ++ I ∷ Δ₁ ++ A ⇒ B ∷ Ξ')) Λ {Γ₁} {.(Ξ ++ E ∷ Ω₀)} {Δ₁} {.(Ξ' ++ Λ)} {A} {B} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (.(Δ₁ ++ A ⇒ B ∷ Ξ') , refl , refl) | inj₁ (Ξ , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ξ) Ω₀ (I ∷ Δ₁ ++ A ⇒ B ∷ Ξ' ++ Λ) E |
          cases++-inj₁ Ω₀ (Δ₁ ++ A ⇒ B ∷ Ξ') Λ I |
          ++?-inj₂ (Γ₁ ++ Ξ) (Ω₀ ++ I ∷ Δ₁) (A ⇒ B ∷ Ξ' ++ Λ) E |
          cases++-inj₂ Ξ Γ₁ (Ω₀ ++ I ∷ Δ₁) E |
          cases++-inj₁ (Ω₀ ++ I ∷ Δ₁) Ξ' Λ (A ⇒ B)
            = intrp≗
                (~-trans
                  (IL~Δ {Δ₀ = E ∷ Ω₀} {Δ₁ = Δ₁ ++ A ⇒ B ∷ Ξ'}
                    (mip⇒L~⇒ Γ₁ Ξ (E ∷ Ω₀ ++ Δ₁) Ξ' Λ))
                  (~-trans
                    (h~ (IL⇒R ∘ ⇒R IL⇒L-assoc))
                    (~-sym (⇒L~⇒ (mipIL~Λ [] Ξ (E ∷ Ω₀) Δ₁) refl))))
mip≗IL⇒L-assoc Γ (I ∷ Ω) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {[]} {.(Ω ++ Ξ')} {Λ₁} {A} {B} refl
  | inj₂ ([] , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₁ [] Γ₁ (I ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ Γ₁ (Ω ++ Ξ') (A ⇒ B ∷ Λ₁) I |
          cases++-inj₂ [] Γ₁ (Ω ++ Ξ') I |
          cases++-inj₂ Ξ' Ω Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (IL~Δ {Δ₀ = []} {Δ₁ = Ω} (mip⇒L~Δ Γ₁ Ω Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mipIL~Δ [] [] Ω Ξ') refl)))
mip≗IL⇒L-assoc Γ (E ∷ .(Ω₀ ++ I ∷ Ω)) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(E ∷ Ω₀)} {.(Ω ++ Ξ')} {Λ₁} {A} {B} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ ([] , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ₁ Ω₀ (I ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Ω₀ Ω (Ξ' ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₂ Γ₁ (Ω₀ ++ I ∷ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ [] Γ₁ (Ω₀ ++ I ∷ Ω ++ Ξ') E |
          cases++-inj₂ Ξ' (Ω₀ ++ I ∷ Ω) Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (IL~Δ {Δ₀ = E ∷ Ω₀} {Δ₁ = Ω}
                    (mip⇒L~Δ Γ₁ (E ∷ Ω₀ ++ Ω) Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mipIL~Δ [] (E ∷ Ω₀) Ω Ξ') refl)))
mip≗IL⇒L-assoc .(Γ₁ ++ A' ∷ Ξ) (I ∷ Ω) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {A' ∷ Ξ} {.(Ω ++ Ξ')} {Λ₁} {A} {B} refl
  | inj₂ ([] , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ (A' ∷ Ξ , refl , refl)
  | inj₁ (refl , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ A' ∷ Ξ) (I ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) |
          ++?-inj₂ (Γ₁ ++ A' ∷ Ξ) (Ω ++ Ξ') (A ⇒ B ∷ Λ₁) I |
          cases++-inj₂ (A' ∷ Ξ) Γ₁ (Ω ++ Ξ') I |
          cases++-inj₂ Ξ' Ω Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (IL~Δ {Δ₀ = []} {Δ₁ = Ω}
                    (mip⇒L~ΔΓ Γ₁ (A' ∷ Ξ) Ω Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mipIL~Δ (A' ∷ Ξ) [] Ω Ξ') refl)))
mip≗IL⇒L-assoc .(Γ₁ ++ A' ∷ Ξ) (E ∷ .(Ω₀ ++ I ∷ Ω)) .(Ξ' ++ A ⇒ B ∷ Λ₁) {Γ₁} {.(A' ∷ Ξ ++ E ∷ Ω₀)} {.(Ω ++ Ξ')} {Λ₁} {A} {B} refl
  | inj₂ (.(E ∷ Ω₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₁ (A' ∷ Ξ , refl , refl)
  | inj₂ (Ω₀ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ Ξ) Ω₀ (I ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₁ Ω₀ Ω (Ξ' ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₂ (Γ₁ ++ A' ∷ Ξ) (Ω₀ ++ I ∷ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ∷ Ξ) Γ₁ (Ω₀ ++ I ∷ Ω ++ Ξ') E |
          cases++-inj₂ Ξ' (Ω₀ ++ I ∷ Ω) Λ₁ (A ⇒ B)
            = intrp≗
                (~-trans
                  (IL~Δ {Δ₀ = E ∷ Ω₀} {Δ₁ = Ω}
                    (mip⇒L~ΔΓ Γ₁ (A' ∷ Ξ) (E ∷ Ω₀ ++ Ω) Ξ' Λ₁))
                  (~-sym (⇒L~Δ (mipIL~Δ (A' ∷ Ξ) (E ∷ Ω₀) Ω Ξ') refl)))
mip≗IL⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} eq | inj₂ (Ω₁ , eq1 , eq2) | inj₁ (Ω , refl , eq4) | inj₂ (C' , Ξ , refl , refl) with cases++ Δ₁ Ω Λ₁ Λ (sym eq4)
mip≗IL⇒L-assoc Γ .((C' ∷ Ξ ++ Δ₀) ++ I ∷ Ω) Λ {.(Γ ++ C' ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} refl | inj₂ (.(C' ∷ Ξ ++ Δ₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ Δ₀) (I ∷ Δ₁ ++ A ⇒ B ∷ Ξ' ++ Λ) C' |
          cases++-inj₁ (Ξ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Ξ') Λ I |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ Δ₁) (A ⇒ B ∷ Ξ' ++ Λ) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ Δ₁) C' |
          cases++-inj₁ (Ξ ++ Δ₀ ++ Δ₁) Ξ' Λ (A ⇒ B) |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ I ∷ Δ₁) (A ⇒ B ∷ Ξ' ++ Λ) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ I ∷ Δ₁) C' |
          cases++-inj₁ (Ξ ++ Δ₀ ++ I ∷ Δ₁) Ξ' Λ (A ⇒ B)
            = intrp≗ (h~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ .((C' ∷ Ξ ++ Δ₀) ++ I ∷ Ω) Λ {.(Γ ++ C' ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} refl | inj₂ (.(C' ∷ Ξ ++ Δ₀) , refl , refl) | inj₁ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , refl) | inj₂ (Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ Δ₀) (I ∷ Ω ++ Ξ' ++ A ⇒ B ∷ Λ₁) C' |
          cases++-inj₁ (Ξ ++ Δ₀) Ω (Ξ' ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ Ω ++ Ξ') C' |
          cases++-inj₂ Ξ' (Ξ ++ Δ₀ ++ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ Ω) Ξ Ξ' |
          ++?-inj₂ Γ (Ξ ++ Δ₀ ++ I ∷ Ω ++ Ξ') (A ⇒ B ∷ Λ₁) C' |
          cases++-inj₁ Γ Ξ (Δ₀ ++ I ∷ Ω ++ Ξ') C' |
          cases++-inj₂ Ξ' (Ξ ++ Δ₀ ++ I ∷ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ I ∷ Ω) Ξ Ξ'
            = intrp≗
                (~-trans
                  (h~ IL⊗R₂)
                  (~-sym (⇒L~⊗ (mipIL~Δ [] Δ₀ Ω Ξ') refl)))
mip≗IL⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} refl | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ω) (I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₂ Γ (Δ ++ Ω ++ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ [] Γ (Δ ++ Ω ++ Δ₁) E |
          cases++-inj₂ (Ω ++ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ (Δ ++ Ω ++ I ∷ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ [] Γ (Δ ++ Ω ++ I ∷ Δ₁) E |
          cases++-inj₂ (Ω ++ I ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ [] (Δ ++ Ω) (I ∷ Δ₁) E |
          cases++-inj₂ Ω Δ Δ₁ I
            = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f = f} refl | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω , refl , refl) | inj₁ (A' ∷ Ξ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ A' ∷ Ξ) (Δ ++ Ω) (I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₂ (Γ₁ ++ A' ∷ Ξ) (Δ ++ Ω ++ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ∷ Ξ) Γ₁ (Δ ++ Ω ++ Δ₁) E |
          cases++-inj₂ (Ω ++ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ A' ∷ Ξ) (Δ ++ Ω ++ I ∷ Δ₁) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (A' ∷ Ξ) Γ₁ (Δ ++ Ω ++ I ∷ Δ₁) E |
          cases++-inj₂ (Ω ++ I ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (A' ∷ Ξ) (Δ ++ Ω) (I ∷ Δ₁) E |
          cases++-inj₂ Ω Δ Δ₁ I
            = intrp≗ (g~ (IL⇒L-assoc {_}{A' ∷ Ξ ++ _ ∷ Ω}))
mip≗IL⇒L-assoc Γ (x ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₂ (Ω₁ , eq1 , eq2) | inj₂ (Ω , refl , refl) | inj₂ (C' , Ξ , refl , eq5) with inj∷ eq5
... | refl , eq3 with ++? Ξ Δ Δ₀ Ω eq3
mip≗IL⇒L-assoc Γ (x ∷ Δ) .(Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₁ ([] , refl , refl)
   rewrite ++?-inj₂ Γ (Δ ++ Ω) (I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) x |
           cases++-inj₂ Ω Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
           ++?-inj₂ Γ (Δ ++ Ω ++ Δ₁) (A ⇒ B ∷ Λ₁) x |
           cases++-inj₁ Γ Δ (Ω ++ Δ₁) x |
           cases++-inj₂ (Ω ++ Δ₁) Δ Λ₁ (A ⇒ B) |
           ++?-inj₁ [] Δ (Ω ++ Δ₁) |
           ++?-inj₂ Γ (Δ ++ Ω ++ I ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
           cases++-inj₁ Γ Δ (Ω ++ I ∷ Δ₁) x |
           cases++-inj₂ (Ω ++ I ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
           ++?-inj₁ [] Δ (Ω ++ I ∷ Δ₁)
             = intrp≗
                 (g~ (IL⊗L-comm₂ ∘
                   ⊗L (IL⇒L-assoc {Γ ++ _ ∷ []} {I ∷ Ω} {Δ₁} ∘ ⇒L ILIL refl)))
mip≗IL⇒L-assoc Γ (x ∷ Δ) .(Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₁ (A' ∷ Ξ' , refl , refl)
   rewrite ++?-inj₂ Γ (Δ ++ A' ∷ Ξ' ++ Δ₀) (I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) x |
           cases++-inj₂ (A' ∷ Ξ' ++ Δ₀) Δ (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
           ++?-inj₂ Γ (Δ ++ A' ∷ Ξ' ++ Δ₀ ++ Δ₁) (A ⇒ B ∷ Λ₁) x |
           cases++-inj₁ Γ (Δ ++ A' ∷ Ξ') (Δ₀ ++ Δ₁) x |
           cases++-inj₂ (A' ∷ Ξ' ++ Δ₀ ++ Δ₁) Δ Λ₁ (A ⇒ B) |
           ++?-inj₂ Δ Ξ' (Δ₀ ++ Δ₁) A' |
           ++?-inj₂ Γ (Δ ++ A' ∷ Ξ' ++ Δ₀ ++ I ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
           cases++-inj₁ Γ (Δ ++ A' ∷ Ξ') (Δ₀ ++ I ∷ Δ₁) x |
           cases++-inj₂ (A' ∷ Ξ' ++ Δ₀ ++ I ∷ Δ₁) Δ Λ₁ (A ⇒ B) |
           ++?-inj₂ Δ Ξ' (Δ₀ ++ I ∷ Δ₁) A'
             = intrp≗ (g~ IL⇒L-assoc)
mip≗IL⇒L-assoc Γ (x ∷ Δ) .(Ω ++ I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) {.(Γ ++ x ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₂ (.((x ∷ Δ) ++ Ω) , refl , refl) | inj₂ (Ω , refl , refl) | inj₂ (x , Ξ , refl , refl) | refl , refl | inj₂ (C'' , Ξ' , refl , refl)
  rewrite ++?-inj₂ Γ (Ξ ++ C'' ∷ Ξ' ++ Ω) (I ∷ Δ₁ ++ A ⇒ B ∷ Λ₁) x |
          cases++-inj₂ Ω (Ξ ++ C'' ∷ Ξ') (Δ₁ ++ A ⇒ B ∷ Λ₁) I |
          ++?-inj₂ Γ (Ξ ++ C'' ∷ Ξ' ++ Ω ++ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ Ξ (C'' ∷ Ξ' ++ Ω ++ Δ₁) x |
          cases++-inj₂ (Ω ++ Δ₁) (Ξ ++ C'' ∷ Ξ') Λ₁ (A ⇒ B) |
          ++?-inj₁ (C'' ∷ Ξ') Ξ (Ω ++ Δ₁) |
          ++?-inj₂ Γ (Ξ ++ C'' ∷ Ξ' ++ Ω ++ I ∷ Δ₁) (A ⇒ B ∷ Λ₁) x |
          cases++-inj₁ Γ Ξ (C'' ∷ Ξ' ++ Ω ++ I ∷ Δ₁) x |
          cases++-inj₂ (Ω ++ I ∷ Δ₁) (Ξ ++ C'' ∷ Ξ') Λ₁ (A ⇒ B) |
          ++?-inj₁ (C'' ∷ Ξ') Ξ (Ω ++ I ∷ Δ₁) |
          ++?-inj₂ [] (Ξ' ++ Ω) (I ∷ Δ₁) C'' |
          cases++-inj₂ Ω Ξ' Δ₁ I
            = intrp≗ (g~ (IL⊗L-comm₂ ∘ ⊗L IL⇒L-assoc))
