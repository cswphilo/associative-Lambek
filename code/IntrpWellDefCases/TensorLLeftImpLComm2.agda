{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLLeftImpLComm2 where

open import IntrpWellDefCases.Base

mip≗⊗L⇐L-comm₂ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ++ A' ∷ B' ∷ Ω₁ ⊢ C}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ A' ⊗ B' ∷ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁} {Ω₁} {A'} {B'} (⇐L {Γ₁} {Δ₁} {Λ₁ ++ A' ∷ B' ∷ Ω₁} f g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₁} {Λ₁ ++ A' ⊗ B' ∷ Ω₁} f (⊗L {Γ₁ ++ B ∷ Λ₁} {Ω₁} {A'} {B'} g)) eq)
mip≗⊗L⇐L-comm₂ Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⇐L-comm₂
mip≗⊗L⇐L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  with cases++ Γ₁ (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁ ++ A' ⊗ B' ∷ Ω₁) Λ (sym eq)
... | inj₁ (Ω , eqΔ , eqΛ) with cases++ Γ₁ Γ Ω (E ∷ Δ) eqΔ
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eqΛ) | inj₁ (Ω' , refl , refl)
  with ++? (Ω' ++ E ∷ Δ) Δ₁ Λ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) eqΛ
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eqΛ) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , eqΛ' , eqΔ')
  with ++? Ω' Δ₁ (E ∷ Δ) Ω'' (sym eqΔ')
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(Δ₁ ++ Ω₀ ++ E ∷ Δ) , refl , eqΛ) | inj₁ (.(Δ₁ ++ Ω₀) , refl , refl) | inj₁ (.(Ω₀ ++ E ∷ Δ) , eqΛ' , refl) | inj₁ (Ω₀ , refl , refl)
  with cases++ Λ₁ Ω₀ Ω₁ (E ∷ Δ ++ Λ) (sym eqΛ')
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ A' ⊗ B' ∷ Ω₂) (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {.(Ω₂ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Δ₁ ++ Λ₁ ++ A' ⊗ B' ∷ Ω₂ ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ Λ₁ ++ A' ⊗ B' ∷ Ω₂) , refl , refl)
  | inj₁ (.(Λ₁ ++ A' ⊗ B' ∷ Ω₂ ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Λ₁ ++ A' ⊗ B' ∷ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Ω₂) (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁) (E ∷ Δ ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁ ++ A' ∷ B' ∷ Ω₂ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Λ₁ ++ A' ∷ B' ∷ Ω₂) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ A' ∷ B' ∷ Ω₂ ++ E ∷ Δ) Δ₁ Λ
  with Λ₁
... | [] rewrite ++?-inj₂ Δ₁ (B' ∷ Ω₂) (E ∷ Δ) A' |
                ++?-inj₂ Δ₁ Ω₂ (E ∷ Δ) (A' ⊗ B') |
                ++?-inj₁ (A' ⊗ B' ∷ Ω₂) (Γ₁ ++ B ∷ []) (E ∷ Δ ++ Λ) =
  intrp≗ (g~ (⊗L⇐L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = []}))
... | F ∷ Λh
  rewrite ++?-inj₂ Δ₁ (Λh ++ A' ∷ B' ∷ Ω₂) (E ∷ Δ) F |
          ++?-inj₂ Δ₁ (Λh ++ A' ⊗ B' ∷ Ω₂) (E ∷ Δ) F |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₂) (Γ₁ ++ B ∷ F ∷ Λh) (E ∷ Δ ++ Λ) =
  intrp≗ (g~ (⊗L⇐L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = F ∷ Λh}))
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(Δ₁ ++ Ω₀ ++ E ∷ Δ) , refl , eqΛ) | inj₁ (.(Δ₁ ++ Ω₀) , refl , refl) | inj₁ (.(Ω₀ ++ E ∷ Δ) , eqΛ' , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₂ , eqMid , eqΛ₁)
  with cases∷ Ω₂ eqMid
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (.(A' ⊗ B') ∷ Δ) Λ
  {Γ₁} {Δ₁} {.(Ω₀)} {.(Δ ++ Λ)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Δ₁ ++ Ω₀ ++ A' ⊗ B' ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ Ω₀) , refl , refl)
  | inj₁ (.(Ω₀ ++ A' ⊗ B' ∷ Δ) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (A' ⊗ B' ∷ Δ ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω₀ ++ A' ∷ B' ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω₀) (A' ∷ B' ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Ω₀ ++ A' ∷ B' ∷ Δ) Δ₁ Λ
  with Ω₀
... | []
  rewrite ++?-inj₁ [] Δ₁ (A' ∷ B' ∷ Δ) |
          ++?-inj₁ [] Δ₁ (A' ⊗ B' ∷ Δ) |
          ++?-inj₁ [] (Γ₁ ++ B ∷ []) (A' ⊗ B' ∷ Δ ++ Λ) =
  intrp≗ (h~ ⊗L⊗R₂)
... | F ∷ Ωh
  rewrite ++?-inj₂ Δ₁ Ωh (A' ∷ B' ∷ Δ) F |
          ++?-inj₂ Δ₁ Ωh (A' ⊗ B' ∷ Δ) F |
          ++?-inj₁ [] (Γ₁ ++ B ∷ F ∷ Ωh) (A' ⊗ B' ∷ Δ ++ Λ) =
  intrp≗ refl
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(Δ₁ ++ Ω₀ ++ E ∷ Δ) , refl , eqΛ) | inj₁ (.(Δ₁ ++ Ω₀) , refl , refl) | inj₁ (.(Ω₀ ++ E ∷ Δ) , eqΛ' , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₂ , eqMid , eqΛ₁) | inj₂ (Ω₃ , eqΔ , eqΩ₂)
  with cases++ Ω₃ Δ Ω₁ Λ eqΔ
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Δ₁ ++ Ω₀ ++ E ∷ Δ) , refl , refl) | inj₁ (.(Δ₁ ++ Ω₀) , refl , refl) | inj₁ (.(Ω₀ ++ E ∷ Δ) , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) Ω₃ (A' ⊗ B' ∷ Ω₄ ++ Λ) E |
          cases++-inj₁ Ω₃ Ω₄ Λ (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω₀ ++ E ∷ Ω₃ ++ A' ∷ B' ∷ Ω₄) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω₀) (E ∷ Ω₃ ++ A' ∷ B' ∷ Ω₄) (B ⇐ A) |
          ++?-inj₁ (Ω₀ ++ E ∷ Ω₃ ++ A' ∷ B' ∷ Ω₄) Δ₁ Λ
  with Ω₀
... | []
  rewrite ++?-inj₁ [] Δ₁ (E ∷ Ω₃ ++ A' ∷ B' ∷ Ω₄) |
          ++?-inj₁ [] Δ₁ (E ∷ Ω₃ ++ A' ⊗ B' ∷ Ω₄) |
          ++?-inj₂ (Γ₁ ++ B ∷ []) Ω₃ (A' ⊗ B' ∷ Ω₄ ++ Λ) E |
          cases++-inj₁ Ω₃ Ω₄ Λ (A' ⊗ B') =
  intrp≗ (h~ ⊗L⊗R₂)
... | F ∷ Ωh
  rewrite ++?-inj₂ Δ₁ Ωh (E ∷ Ω₃ ++ A' ∷ B' ∷ Ω₄) F |
          ++?-inj₂ Δ₁ Ωh (E ∷ Ω₃ ++ A' ⊗ B' ∷ Ω₄) F |
          ++?-inj₂ (Γ₁ ++ B ∷ F ∷ Ωh) Ω₃ (A' ⊗ B' ∷ Ω₄ ++ Λ) E |
          cases++-inj₁ Ω₃ Ω₄ Λ (A' ⊗ B') =
  intrp≗ refl
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Δ₁ ++ Ω₀ ++ E ∷ Δ) , refl , refl) | inj₁ (.(Δ₁ ++ Ω₀) , refl , refl) | inj₁ (.(Ω₀ ++ E ∷ Δ) , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) | inj₂ (Ω₄ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Ω₀) (Δ ++ Ω₄) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ω₄ Δ Ω₁ (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω₀ ++ E ∷ Δ) (Ω₄ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ Ω₀) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Ω₀ ++ E ∷ Δ) Δ₁ (Ω₄ ++ A' ∷ B' ∷ Ω₁)
  with Ω₀
... | []
  rewrite ++?-inj₁ [] Δ₁ (E ∷ Δ) |
          ++?-inj₂ (Γ₁ ++ B ∷ []) (Δ ++ Ω₄) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ω₄ Δ Ω₁ (A' ⊗ B') =
  intrp≗ (g~ (⊗L⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Δ₁} {Δ = Ω₄} {Λ = Ω₁} {A = I} {B = _} {A' = A'} {B' = B'} ∘
              ⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Δ₁} {A = I} {B = _}
                (⊗L⇐L-comm₂ {Γ = Γ₁} {Δ = Δ₁ ++ I ∷ []} {Λ = _ ∷ Ω₄} {Ω = Ω₁})))
... | F ∷ Ωh
  rewrite ++?-inj₂ Δ₁ Ωh (E ∷ Δ) F |
          ++?-inj₂ (Γ₁ ++ B ∷ F ∷ Ωh) (Δ ++ Ω₄) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ω₄ Δ Ω₁ (A' ⊗ B') =
  intrp≗ (g~ (⊗L⇐L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = F ∷ Ωh ++ _ ∷ Ω₄} {Ω = Ω₁}))
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , eqΛ) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , eqΛ' , refl) | inj₂ (F , Ω₀ , refl , refl)
  with ++? Ω'' Λ₁ Λ (A' ⊗ B' ∷ Ω₁) eqΛ'
... | inj₁ (Ψ , eqΩ₁ , eqΩ'')
  with Λ
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω₀ ++ Ω'')) Λ {Γ₁} {.(Ω' ++ E ∷ Ω₀)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Ω' ++ E ∷ Ω₀ ++ Ω'') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (E , Ω₀ , refl , refl)
  | inj₁ (Ψ , refl , refl) | []
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Ω₀ ++ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₁ (Ω₀ ++ Λ₁) Ω₁ [] (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω₀ ++ Λ₁ ++ A' ∷ B' ∷ Ω₁) [] (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Ω₀ ++ Λ₁ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ A' ∷ B' ∷ Ω₁) (Ω' ++ E ∷ Ω₀) [] |
          ++?-inj₁ (E ∷ Ω₀) Ω' (Λ₁ ++ A' ∷ B' ∷ Ω₁) |
          ++?-inj₁ (E ∷ Ω₀) Ω' (Λ₁ ++ A' ⊗ B' ∷ Ω₁) =
  intrp≗
    (~-trans
      (h~ ⊗L⊗R₂)
      (⇐L~⊗ refl (~-sym (mip⊗L~Δ (Γ₁ ++ B ∷ []) Λ₁ Ω₁ []))))
... | H ∷ Λh
  with cases∷ Ψ eqΩ₁
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω₀ ++ Λ₁)) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω₀)} {Λ₁} {Λh} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Ω' ++ E ∷ Ω₀ ++ Λ₁) , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Λ₁ , refl , refl) | inj₂ (E , Ω₀ , refl , refl)
  | inj₁ ([] , refl , refl) | .(A' ⊗ B') ∷ Λh
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Ω₀ ++ Λ₁) (A' ⊗ B' ∷ Λh) E |
          cases++-inj₂ [] (Ω₀ ++ Λ₁) Λh (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω₀ ++ Λ₁) (A' ∷ B' ∷ Λh) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Ω₀ ++ Λ₁) (B ⇐ A) |
          ++?-inj₁ Λ₁ (Ω' ++ E ∷ Ω₀) (A' ∷ B' ∷ Λh) |
          ++?-inj₁ (E ∷ Ω₀) Ω' Λ₁ =
  intrp≗
    (~-trans
      (g~
        (⊗L⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Ω'} {Δ = []} {Λ = Λh}
          {A = _} {B = _} {A' = A'} {B' = B'} ∘
          ⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Ω'} {A = _} {B = _}
            (⊗L⇐L-comm₂ {Γ = Γ₁} {Δ = Ω' ++ _ ∷ []} {Λ = _ ∷ []} {Ω = Λh})))
      (⇐L~⊗ refl (~-sym (mip⊗L~Λ (Γ₁ ++ B ∷ []) Λ₁ [] Λh))))
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω₀ ++ Λ₁ ++ A' ⊗ B' ∷ Ψ')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω₀)} {Λ₁} {.(Ψ' ++ H ∷ Λh)} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Ω' ++ E ∷ Ω₀ ++ Λ₁ ++ A' ⊗ B' ∷ Ψ') , refl , refl) | inj₁ (Ω' , refl , refl)
  | inj₁ (.(Λ₁ ++ A' ⊗ B' ∷ Ψ') , refl , refl) | inj₂ (E , Ω₀ , refl , refl)
  | inj₁ (.(A' ⊗ B' ∷ Ψ') , refl , refl) | H ∷ Λh
  | inj₂ (Ψ' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Ω₀ ++ Λ₁) (A' ⊗ B' ∷ Ψ' ++ H ∷ Λh) E |
          cases++-inj₁ (Ω₀ ++ Λ₁) Ψ' (H ∷ Λh) (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω₀ ++ Λ₁ ++ A' ∷ B' ∷ Ψ') (H ∷ Λh) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Ω₀ ++ Λ₁ ++ A' ∷ B' ∷ Ψ') (B ⇐ A) |
          ++?-inj₁ (Λ₁ ++ A' ∷ B' ∷ Ψ') (Ω' ++ E ∷ Ω₀) (H ∷ Λh) |
          ++?-inj₁ (E ∷ Ω₀) Ω' (Λ₁ ++ A' ∷ B' ∷ Ψ') |
          ++?-inj₁ (E ∷ Ω₀) Ω' (Λ₁ ++ A' ⊗ B' ∷ Ψ') =
  intrp≗
    (~-trans
      (h~ ⊗L⊗R₂)
      (⇐L~⊗ refl (~-sym (mip⊗L~Δ (Γ₁ ++ B ∷ []) Λ₁ Ψ' (H ∷ Λh)))))
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω₀ ++ Ω'')) .(G ∷ Ψ ++ A' ⊗ B' ∷ Ω₁)
  {Γ₁} {.(Ω' ++ E ∷ Ω₀)} {.(Ω'' ++ G ∷ Ψ)} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Ω' ++ E ∷ Ω₀ ++ Ω'') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (E , Ω₀ , refl , refl)
  | inj₂ (G , Ψ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Ω₀ ++ Ω'' ++ G ∷ Ψ) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (G ∷ Ψ) (Ω₀ ++ Ω'') Ω₁ (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω₀ ++ Ω'') (G ∷ Ψ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Ω₀ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' (Ω' ++ E ∷ Ω₀) (G ∷ Ψ ++ A' ∷ B' ∷ Ω₁) |
          ++?-inj₁ (E ∷ Ω₀) Ω' Ω'' =
  intrp≗
    (~-trans
      (g~
        (⊗L⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Ω'} {Δ = G ∷ Ψ} {Λ = Ω₁}
          {A = _} {B = _} {A' = A'} {B' = B'} ∘
          ⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Ω'} {A = _} {B = _}
            (⊗L⇐L-comm₂ {Γ = Γ₁} {Δ = Ω' ++ _ ∷ []} {Λ = _ ∷ G ∷ Ψ} {Ω = Ω₁})))
      (⇐L~⊗ refl (~-sym (mip⊗L~Λ (Γ₁ ++ B ∷ []) Ω'' (G ∷ Ψ) Ω₁))))
mip≗⊗L⇐L-comm₂ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) .(F ∷ Ω'' ++ Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ F ∷ Ω'')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Δ ++ F ∷ Ω'' ++ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (F ∷ Ω'' ++ Λ₁) Δ Ω₁ (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) (F ∷ Ω'' ++ Λ₁ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ω' ++ E ∷ Δ) Ω'' (Λ₁ ++ A' ∷ B' ∷ Ω₁) F =
  intrp≗ (g~ (⊗L⇐L-comm₂ {Γ = Γ₁} {Δ = Ω' ++ _ ∷ F ∷ Ω''} {Λ = Λ₁} {Ω = Ω₁}))
mip≗⊗L⇐L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (Ω , eqΔ , eqΛ) | inj₂ (Ω' , eqMid , eqΓ)
  with cases∷ Ω' eqMid
mip≗⊗L⇐L-comm₂ Γ (B ⇐ A ∷ Δ) Λ {Γ} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (Δ , refl , eqΛ) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  with ++? Δ Δ₁ Λ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) eqΛ
mip≗⊗L⇐L-comm₂ Γ (B ⇐ A ∷ Δ) .(Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {Γ} {Δ} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Δ , refl , refl) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Λ₁) (A' ⊗ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ Λ₁ Δ Ω₁ (A' ⊗ B') |
          cases++-inj₁ Γ Δ (Λ₁ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] Γ Δ (B ⇐ A) |
          ++?-inj₁ [] Δ (Λ₁ ++ A' ∷ B' ∷ Ω₁) |
          ++?-inj₂ Γ Λ₁ (A' ⊗ B' ∷ Ω₁) B = intrp≗ refl
... | inj₁ (F ∷ Ω₂ , eqΛ₁ , refl)
  with cases∷ Λ₁ (sym eqΛ₁)
mip≗⊗L⇐L-comm₂ Γ ._ Λ
  {Γ} {Δ₁} {[]} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (._ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ ((A' ⊗ B') ∷ Ω₂ , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ Γ Δ₁ ((A' ⊗ B') ∷ Ω₂ ++ Λ) (B ⇐ A) |
          cases++-inj₁ Δ₁ Ω₂ Λ (A' ⊗ B') |
          cases++-inj₁ Γ (Δ₁ ++ A' ∷ B' ∷ Ω₂) Λ (B ⇐ A) |
          cases++-inj₂ [] Γ (Δ₁ ++ A' ∷ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₁ (A' ∷ B' ∷ Ω₂) Δ₁ Λ |
          ++?-inj₂ Γ [] ((A' ⊗ B') ∷ Ω₂ ++ Λ) B =
  intrp≗ (h~ (⊗L⇐L-comm₂ {Γ = []} {Δ = Δ₁} {Λ = []} {Ω = Ω₂}))
... | inj₂ (Λ₂ , eqΛ₂ , refl)
  with cases++ Λ₂ Ω₂ Ω₁ Λ eqΛ₂
mip≗⊗L⇐L-comm₂ Γ ._ Λ
  {Γ} {Δ₁} {F ∷ Λ₂} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (._ , refl , refl) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (F ∷ ._ , refl , refl)
  | inj₂ (Λ₂ , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  rewrite ++?-inj₂ Γ (Δ₁ ++ F ∷ Λ₂) ((A' ⊗ B') ∷ Ω₃ ++ Λ) (B ⇐ A) |
          cases++-inj₁ (Δ₁ ++ F ∷ Λ₂) Ω₃ Λ (A' ⊗ B') |
          cases++-inj₁ Γ (Δ₁ ++ F ∷ Λ₂ ++ A' ∷ B' ∷ Ω₃) Λ (B ⇐ A) |
          cases++-inj₂ [] Γ (Δ₁ ++ F ∷ Λ₂ ++ A' ∷ B' ∷ Ω₃) (B ⇐ A) |
          ++?-inj₁ (F ∷ Λ₂ ++ A' ∷ B' ∷ Ω₃) Δ₁ Λ |
          ++?-inj₂ Γ (F ∷ Λ₂) ((A' ⊗ B') ∷ Ω₃ ++ Λ) B |
          cases++-inj₁ Λ₂ Ω₃ Λ (A' ⊗ B') =
  intrp≗ (h~ (⊗L⇐L-comm₂ {Γ = []} {Δ = Δ₁} {Λ = F ∷ Λ₂} {Ω = Ω₃}))
mip≗⊗L⇐L-comm₂ Γ ._ ._
  {Γ} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (._ , refl , refl) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (F ∷ Ω₂ , refl , refl)
  | inj₂ (._ , refl , refl)
  | inj₂ (Ω₃ , refl , refl)
  rewrite ++?-inj₂ Γ (Δ₁ ++ F ∷ Ω₂ ++ Ω₃) (A' ⊗ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ Ω₃ (Δ₁ ++ F ∷ Ω₂) Ω₁ (A' ⊗ B') |
          cases++-inj₁ Γ (Δ₁ ++ F ∷ Ω₂) (Ω₃ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] Γ (Δ₁ ++ F ∷ Ω₂) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω₂) Δ₁ (Ω₃ ++ A' ∷ B' ∷ Ω₁) |
          ++?-inj₂ Γ (F ∷ Ω₂ ++ Ω₃) (A' ⊗ B' ∷ Ω₁) B |
          cases++-inj₂ Ω₃ Ω₂ Ω₁ (A' ⊗ B') = intrp≗ refl
mip≗⊗L⇐L-comm₂ Γ (B ⇐ A ∷ Δ) ._ {Γ} {._} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Δ , refl , refl) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω₂ , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ F ∷ Ω₂ ++ Λ₁) (A' ⊗ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ (F ∷ Ω₂ ++ Λ₁) Δ Ω₁ (A' ⊗ B') |
          cases++-inj₁ Γ Δ (F ∷ Ω₂ ++ Λ₁ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] Γ Δ (B ⇐ A) |
          ++?-inj₂ Δ Ω₂ (Λ₁ ++ A' ∷ B' ∷ Ω₁) F |
          ++?-inj₂ Γ Λ₁ (A' ⊗ B' ∷ Ω₁) B =
  intrp≗ (g~ (⊗L⇐L-comm₂ {Γ = Γ} {Δ = F ∷ Ω₂} {Λ = Λ₁} {Ω = Ω₁}))
mip≗⊗L⇐L-comm₂ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Ω)) Λ
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (Ω , eqΔ , eqΛ) | inj₂ (E ∷ Ω'' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  with ++? Ω Δ₁ Λ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) eqΛ
mip≗⊗L⇐L-comm₂ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Ω)) ._
  {.(Γ ++ E ∷ Ω'')} {Ω} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Ω , refl , refl) | inj₂ (E ∷ Ω'' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Ω ++ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Λ₁ (Ω'' ++ B ⇐ A ∷ Ω) Ω₁ (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω'') Ω (Λ₁ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ Ω (B ⇐ A) |
          ++?-inj₁ [] Ω (Λ₁ ++ A' ∷ B' ∷ Ω₁) |
          ++?-inj₁ [] Ω (Λ₁ ++ A' ⊗ B' ∷ Ω₁) |
          ++?-inj₂ Γ (Ω'' ++ B ∷ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Λ₁ (Ω'' ++ B ∷ []) Ω₁ (A' ⊗ B') = intrp≗ refl
... | inj₁ (F ∷ Ω₂ , eqΛ₁ , refl)
  with cases∷ Λ₁ (sym eqΛ₁)
mip≗⊗L⇐L-comm₂ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ A' ⊗ B' ∷ Ω₂)) Λ
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {[]} {.(Ω₂ ++ Λ)} {A} {B} {A'} {B'} {C} {g = g} refl
  | inj₁ (.(Δ₁ ++ A' ⊗ B' ∷ Ω₂) , refl , refl)
  | inj₂ (E ∷ Ω'' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ ((A' ⊗ B') ∷ Ω₂ , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Δ₁) (A' ⊗ B' ∷ Ω₂ ++ Λ) E |
          cases++-inj₁ (Ω'' ++ B ⇐ A ∷ Δ₁) Ω₂ Λ (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Δ₁ ++ A' ∷ B' ∷ Ω₂) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ (Δ₁ ++ A' ∷ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₁ (A' ∷ B' ∷ Ω₂) Δ₁ Λ |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₂) Δ₁ Λ |
          ++?-inj₂ Γ (Ω'' ++ B ∷ []) (A' ⊗ B' ∷ Ω₂ ++ Λ) E |
          cases++-inj₁ (Ω'' ++ B ∷ []) Ω₂ Λ (A' ⊗ B') =
  intrp≗ (h~ (⊗L⇐L-comm₂
    {Γ = E ∷ Ω''} {Δ = Δ₁} {Λ = []} {Ω = Ω₂}))
... | inj₂ (Λ₂ , eqΛ₂ , refl)
  with cases++ Λ₂ Ω₂ Ω₁ Λ eqΛ₂
mip≗⊗L⇐L-comm₂ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ F ∷ Λ₂ ++ A' ⊗ B' ∷ Ω₃)) Λ
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {F ∷ Λ₂} {.(Ω₃ ++ Λ)} {A} {B} {A'} {B'} {C} {g = g} refl
  | inj₁ (.(Δ₁ ++ F ∷ Λ₂ ++ A' ⊗ B' ∷ Ω₃) , refl , refl)
  | inj₂ (E ∷ Ω'' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (F ∷ .(Λ₂ ++ A' ⊗ B' ∷ Ω₃) , refl , refl)
  | inj₂ (Λ₂ , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ F ∷ Λ₂) (A' ⊗ B' ∷ Ω₃ ++ Λ) E |
          cases++-inj₁ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ F ∷ Λ₂) Ω₃ Λ (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Δ₁ ++ F ∷ Λ₂ ++ A' ∷ B' ∷ Ω₃) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ (Δ₁ ++ F ∷ Λ₂ ++ A' ∷ B' ∷ Ω₃) (B ⇐ A) |
          ++?-inj₁ (F ∷ Λ₂ ++ A' ∷ B' ∷ Ω₃) Δ₁ Λ |
          ++?-inj₁ (F ∷ Λ₂ ++ A' ⊗ B' ∷ Ω₃) Δ₁ Λ |
          ++?-inj₂ Γ (Ω'' ++ B ∷ F ∷ Λ₂) (A' ⊗ B' ∷ Ω₃ ++ Λ) E |
          cases++-inj₁ (Ω'' ++ B ∷ F ∷ Λ₂) Ω₃ Λ (A' ⊗ B') =
  intrp≗ (h~ (⊗L⇐L-comm₂ {Γ = E ∷ Ω''} {Δ = Δ₁} {Λ = F ∷ Λ₂} {Ω = Ω₃}))
mip≗⊗L⇐L-comm₂ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω₂)) .(Ω₃ ++ A' ⊗ B' ∷ Ω₁)
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {F ∷ .(Ω₂ ++ Ω₃)} {Ω₁} {A} {B} {A'} {B'} {C} {g = g} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω₂) , refl , refl)
  | inj₂ (E ∷ Ω'' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (F ∷ Ω₂ , refl , refl)
  | inj₂ (.(Ω₂ ++ Ω₃) , refl , refl)
  | inj₂ (Ω₃ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω₂ ++ Ω₃) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ω₃ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω₂) Ω₁ (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Δ₁ ++ F ∷ Ω₂) (Ω₃ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ (Δ₁ ++ F ∷ Ω₂) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω₂) Δ₁ (Ω₃ ++ A' ∷ B' ∷ Ω₁) |
          ++?-inj₁ (F ∷ Ω₂) Δ₁ (Ω₃ ++ A' ⊗ B' ∷ Ω₁) |
          ++?-inj₂ Γ (Ω'' ++ B ∷ F ∷ Ω₂ ++ Ω₃) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Ω₃ (Ω'' ++ B ∷ F ∷ Ω₂) Ω₁ (A' ⊗ B') = intrp≗ refl
mip≗⊗L⇐L-comm₂ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Ω)) .(F ∷ Ω₂ ++ Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {.(Γ ++ E ∷ Ω'')} {.(Ω ++ F ∷ Ω₂)} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₁ (Ω , refl , refl) | inj₂ (E ∷ Ω'' , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₂ (F , Ω₂ , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Ω ++ F ∷ Ω₂ ++ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (F ∷ Ω₂ ++ Λ₁) (Ω'' ++ B ⇐ A ∷ Ω) Ω₁ (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω'') Ω (F ∷ Ω₂ ++ Λ₁ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω₂ (Λ₁ ++ A' ∷ B' ∷ Ω₁) F |
          ++?-inj₂ Ω Ω₂ (Λ₁ ++ A' ⊗ B' ∷ Ω₁) F |
          ++?-inj₂ Γ (Ω'' ++ B ∷ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ Λ₁ (Ω'' ++ B ∷ []) Ω₁ (A' ⊗ B') =
  intrp≗ (g~ (⊗L⇐L-comm₂ {Γ = Γ} {Δ = F ∷ Ω₂} {Λ = Λ₁} {Ω = Ω₁}))
mip≗⊗L⇐L-comm₂ Γ (E ∷ Δ) .(Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ A' ⊗ B' ∷ Ω₁)
  {.(Γ ++ E ∷ Δ ++ Ω)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} refl
  | inj₂ (Ω , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁) Δ Ω₁ (A' ⊗ B') |
          cases++-inj₂ Ω (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁ ++ A' ∷ B' ∷ Ω₁) (B ⇐ A) |
          ++?-inj₂ Γ (Δ ++ Ω ++ B ∷ Λ₁) (A' ⊗ B' ∷ Ω₁) E |
          cases++-inj₂ (Ω ++ B ∷ Λ₁) Δ Ω₁ (A' ⊗ B') =
  intrp≗ (g~ (⊗L⇐L-comm₂ {Γ = Γ ++ _ ∷ Ω} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁}))
