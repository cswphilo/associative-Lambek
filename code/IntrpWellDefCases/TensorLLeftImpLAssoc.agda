{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.TensorLLeftImpLAssoc where

open import Data.Empty using (⊥-elim)
open import IntrpWellDefCases.Base

mip≗⊗L⇐L-assoc : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ++ A' ∷ B' ∷ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Δ₀} {Δ₁ ++ Λ₁} {A'} {B'} (⇐L {Γ₁} {Δ₀ ++ A' ∷ B' ∷ Δ₁} {Λ₁} f g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₀ ++ A' ⊗ B' ∷ Δ₁} {Λ₁} (⊗L {Δ₀} {Δ₁} f) g) eq)
mip≗⊗L⇐L-assoc Γ [] Λ eq = mip[]≗ Γ Λ eq ⊗L⇐L-assoc
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  with ++? Γ (Γ₁ ++ B ⇐ A ∷ Δ₀) (E ∷ Δ ++ Λ) (A' ⊗ B' ∷ Δ₁ ++ Λ₁) eq
... | inj₁ ([] , eq1 , eq2)
  with inj∷ eq1
... | refl , eq3
  with ++? Δ Δ₁ Λ Λ₁ eq3
mip≗⊗L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀) (.(A' ⊗ B') ∷ .(Δ₁ ++ Ω)) Λ
  {Γ₁} {Δ₀} {Δ₁} {.(Ω ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | refl , refl
  | inj₁ (Ω , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Ω) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Ω) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (A' ∷ B' ∷ Δ₁ ++ Ω) (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (A' ⊗ B' ∷ Δ₁ ++ Ω) (B ⇐ A) |
          ++?-inj₁ Ω (Δ₀ ++ A' ∷ B' ∷ Δ₁) Λ |
          ++?-inj₁ Ω (Δ₀ ++ A' ⊗ B' ∷ Δ₁) Λ |
          ++?-inj₁ (A' ∷ B' ∷ Δ₁) Δ₀ Ω |
          ++?-inj₁ (A' ⊗ B' ∷ Δ₁) Δ₀ Ω |
          ++?-inj₁ [] Δ₀ (A' ⊗ B' ∷ Δ₁) = intrp≗ (h~ ⊗L⊗R₁)
mip≗⊗L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀) (.(A' ⊗ B') ∷ Δ) .(F ∷ Ω ++ Λ₁)
  {Γ₁} {Δ₀} {.(Δ ++ F ∷ Ω)} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ ([] , refl , refl)
  | refl , refl
  | inj₂ (F , Ω , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Δ) (F ∷ Ω ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Δ) (F ∷ Ω ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (A' ∷ B' ∷ Δ) (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (A' ⊗ B' ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Δ₀ ++ A' ∷ B' ∷ Δ) Ω Λ₁ F |
          ++?-inj₂ (Δ₀ ++ A' ⊗ B' ∷ Δ) Ω Λ₁ F |
          ++?-inj₁ [] Δ₀ (A' ⊗ B' ∷ Δ ++ F ∷ Ω) = intrp≗ refl
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} eq
  | inj₁ (F ∷ Ω' , eq1 , eq2)
  with inj∷ eq1
... | refl , eq3
  with ++? Ω' Δ₁ (E ∷ Δ ++ Λ) Λ₁ eq3
mip≗⊗L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Ω) (E ∷ Δ) Λ
  {Γ₁} {Δ₀} {Δ₁} {.(Ω ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B' ∷ Δ₁ ++ Ω) , refl , refl)
  | refl , refl
  | inj₁ (Ω , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Ω ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Ω ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Ω) (E ∷ Δ) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Ω) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Ω ++ E ∷ Δ) (Δ₀ ++ A' ∷ B' ∷ Δ₁) Λ |
          ++?-inj₁ (Ω ++ E ∷ Δ) (Δ₀ ++ A' ⊗ B' ∷ Δ₁) Λ
  with Ω
... | []
  rewrite ++?-inj₁ [] (Δ₀ ++ A' ∷ B' ∷ Δ₁) (E ∷ Δ) |
          ++?-inj₁ [] (Δ₀ ++ A' ⊗ B' ∷ Δ₁) (E ∷ Δ) =
    intrp≗
      (g~ ((~ (⊗L⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Δ₀} {Δ = Δ₁} {Λ = Λ}
            {A = A'} {B = B'} {A' = I}
            {B' = mip (Γ₁ ++ B ∷ []) (E ∷ Δ) Λ g refl .MIP.D})) ∘
        ⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Δ₀ ++ A' ⊗ B' ∷ Δ₁} {Δ = Λ}
          {A = I} {B = mip (Γ₁ ++ B ∷ []) (E ∷ Δ) Λ g refl .MIP.D}
          (⊗L⇐L-assoc {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁ ++ I ∷ []}
            {Λ = mip (Γ₁ ++ B ∷ []) (E ∷ Δ) Λ g refl .MIP.D ∷ Λ}
            ∘ ⇐L (~ (IL⊗L-comm₂ {Γ = Δ₀} {Δ = Δ₁} {Λ = []}
              {A = A'} {B = B'} {f = f})) refl)))
... | G ∷ Ω'
  rewrite ++?-inj₂ (Δ₀ ++ A' ∷ B' ∷ Δ₁) Ω' (E ∷ Δ) G |
          ++?-inj₂ (Δ₀ ++ A' ⊗ B' ∷ Δ₁) Ω' (E ∷ Δ) G =
    intrp≗
      (g~ (⊗L⇐L-assoc {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁}
        {Λ = G ∷ Ω' ++ mip (Γ₁ ++ B ∷ G ∷ Ω') (E ∷ Δ) Λ g refl .MIP.D ∷ Λ}))
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
  | inj₁ (.(A' ⊗ B') ∷ Ω' , eq1 , eq2)
  | refl , eq3
  | inj₂ (F , Ω , eq4 , eq5)
  with inj∷ eq5
... | refl , eq6
  with ++? Δ Ω Λ Λ₁ (sym eq6)
mip≗⊗L⇐L-assoc ._ (E ∷ .(Ω ++ Ω₀)) Λ
  {Γ₁} {Δ₀} {._} {.(Ω₀ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B') ∷ Ω' , refl , refl)
  | refl , refl
  | inj₂ (.E , Ω , refl , refl)
  | refl , refl
  | inj₁ (Ω₀ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Ω' ++ E ∷ Ω ++ Ω₀) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Ω' ++ E ∷ Ω ++ Ω₀) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Ω ++ Ω₀) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Ω') (E ∷ Ω ++ Ω₀) (B ⇐ A) |
          ++?-inj₁ Ω₀ (Δ₀ ++ A' ∷ B' ∷ Ω' ++ E ∷ Ω) Λ |
          ++?-inj₁ Ω₀ (Δ₀ ++ A' ⊗ B' ∷ Ω' ++ E ∷ Ω) Λ |
          ++?-inj₁ (E ∷ Ω) (Δ₀ ++ A' ∷ B' ∷ Ω') Ω₀ |
          ++?-inj₁ (E ∷ Ω) (Δ₀ ++ A' ⊗ B' ∷ Ω') Ω₀ |
          ++?-inj₁ (A' ⊗ B' ∷ Ω') Δ₀ (E ∷ Ω) =
    intrp≗
      (g~ ((~ (⊗L⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Δ₀} {Δ = Ω'} {Λ = Λ}
            {A = A'} {B = B'}
            {A' = mip (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Ω) [] f refl .MIP.D}
            {B' = mip (Γ₁ ++ B ∷ []) Ω₀ Λ g refl .MIP.D}
            {f = ⇐L (mip (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Ω) [] f refl .MIP.g)
                     (mip (Γ₁ ++ B ∷ []) Ω₀ Λ g refl .MIP.g)})) ∘
        ⊗L
          {Γ = Γ₁ ++ B ⇐ A ∷ Δ₀ ++ A' ⊗ B' ∷ Ω'}
          {Δ = Λ}
          {A = mip (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Ω) [] f refl .MIP.D}
          {B = mip (Γ₁ ++ B ∷ []) Ω₀ Λ g refl .MIP.D}
          (⊗L⇐L-assoc {Γ = Γ₁} {Δ₀ = Δ₀}
            {Δ₁ = Ω' ++ mip (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Ω) [] f refl .MIP.D ∷ []}
            {Λ = mip (Γ₁ ++ B ∷ []) Ω₀ Λ g refl .MIP.D ∷ Λ}
            {A = A} {B = B} {A' = A'} {B' = B'}
            {f = mip (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Ω) [] f refl .MIP.g}
            {g = mip (Γ₁ ++ B ∷ []) Ω₀ Λ g refl .MIP.g})))
mip≗⊗L⇐L-assoc ._ (E ∷ Δ) ._
  {Γ₁} {Δ₀} {._} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₁ (.(A' ⊗ B') ∷ Ω' , refl , refl)
  | refl , refl
  | inj₂ (.E , Ω , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₀ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Ω' ++ E ∷ Δ) (H ∷ Ω₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Ω' ++ E ∷ Δ) (H ∷ Ω₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Δ) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ A' ⊗ B' ∷ Ω') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Δ₀ ++ A' ∷ B' ∷ Ω' ++ E ∷ Δ) Ω₀ Λ₁ H |
          ++?-inj₂ (Δ₀ ++ A' ⊗ B' ∷ Ω' ++ E ∷ Δ) Ω₀ Λ₁ H |
          ++?-inj₁ (A' ⊗ B' ∷ Ω') Δ₀ (E ∷ Δ ++ H ∷ Ω₀) =
    intrp≗
      (g~ (⊗L⇐L-assoc {Γ = Γ₁} {Δ₀ = Δ₀}
        {Δ₁ = Ω' ++ mip (Δ₀ ++ A' ∷ B' ∷ Ω') (E ∷ Δ) (H ∷ Ω₀) f refl .MIP.D ∷ H ∷ Ω₀}
        {Λ = Λ₁}))
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
  | inj₂ (F , Ω , eq1 , eq2)
  with inj∷ eq2
... | refl , eq3
  with ++? Δ Ω Λ (A' ⊗ B' ∷ Δ₁ ++ Λ₁) (sym eq3)
     | ++? Γ Γ₁ (E ∷ Ω) (B ⇐ A ∷ Δ₀) eq1
mip≗⊗L⇐L-assoc .Γ₁ (.(B ⇐ A) ∷ Δ) .(H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {Γ₁} {.(Δ ++ H ∷ Ω₁)} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (.(B ⇐ A) , .(Δ ++ H ∷ Ω₁) , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₁ , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ (H ∷ Ω₁) Δ (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ Δ (H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ (H ∷ Ω₁ ++ A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₂ Δ (Ω₁ ++ A' ∷ B' ∷ Δ₁) Λ₁ H |
          ++?-inj₂ Δ (Ω₁ ++ A' ⊗ B' ∷ Δ₁) Λ₁ H |
          ++?-inj₂ Δ Ω₁ (A' ⊗ B' ∷ Δ₁) H |
          cases++-inj₁ Ω₁ Δ₁ [] (A' ⊗ B') =
    intrp≗ (g~ (⊗L⇐L-assoc {Γ = Γ₁} {Δ₀ = H ∷ Ω₁} {Δ₁ = Δ₁} {Λ = Λ₁}))
mip≗⊗L⇐L-assoc ._ (E ∷ Δ) .(H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {Γ₁} {._} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Δ ++ H ∷ Ω₁) , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₁ , refl , refl)
  | inj₁ (.(B ⇐ A) ∷ Ξ' , refl , refl)
  rewrite cases++-inj₂ (H ∷ Ω₁) Δ (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Δ) (H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Δ) (H ∷ Ω₁ ++ A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ξ' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ξ' ++ E ∷ Δ) (Ω₁ ++ A' ∷ B' ∷ Δ₁) Λ₁ H |
          ++?-inj₂ (Ξ' ++ E ∷ Δ) (Ω₁ ++ A' ⊗ B' ∷ Δ₁) Λ₁ H |
          ++?-inj₂ Ξ' (Δ ++ H ∷ Ω₁) (A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₂ (H ∷ Ω₁) Δ Δ₁ (A' ⊗ B') =
    intrp≗ (g~ (⊗L⇐L-assoc {Γ = Γ₁}
      {Δ₀ = Ξ' ++ mip Ξ' (E ∷ Δ) (H ∷ Ω₁ ++ A' ∷ B' ∷ Δ₁) f refl .MIP.D ∷ H ∷ Ω₁}
      {Δ₁ = Δ₁} {Λ = Λ₁}))
... | inj₁ (Ω₁ , eq4 , refl) | inj₂ (H , Ξ , refl , eq7)
  with inj∷ eq7
... | refl , refl
  with ++? [] Ω₁ (A' ⊗ B' ∷ Δ₁ ++ Λ₁) Λ (sym eq4)
... | inj₁ (F ∷ Ω₂ , eq9 , eq10) = ⊥-elim ([]disj∷ Ω₁ eq10)
mip≗⊗L⇐L-assoc Γ (E ∷ .(Ξ ++ B ⇐ A ∷ Δ₀)) .(A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Ξ ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  | inj₂ (E , Ξ , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ [] (Ξ ++ B ⇐ A ∷ Δ₀) (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ξ) Δ₀ (A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ξ) Δ₀ (A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) Γ Δ₀ (B ⇐ A) |
          ++?-inj₂ Δ₀ (B' ∷ Δ₁) Λ₁ A' |
          ++?-inj₂ Δ₀ Δ₁ Λ₁ (A' ⊗ B') |
          ++?-inj₁ [] Δ₀ (A' ⊗ B' ∷ Δ₁) =
    intrp≗
      (g~ (⊗L⇐L-assoc {Γ = Γ} {Δ₀ = []} {Δ₁ = Δ₁} {Λ = Λ₁}
        {A = mip Δ₀ (A' ∷ B' ∷ Δ₁) [] f refl .MIP.D}
        {B = mip Γ (E ∷ Ξ ++ B ∷ []) Λ₁ g refl .MIP.D}
        {A' = A'} {B' = B'}
        {f = mip Δ₀ (A' ∷ B' ∷ Δ₁) [] f refl .MIP.h}
        {g = mip Γ (E ∷ Ξ ++ B ∷ []) Λ₁ g refl .MIP.g}))
mip≗⊗L⇐L-assoc Γ (E ∷ .(Ξ ++ B ⇐ A ∷ Δ₀ ++ F ∷ Ω₂)) Λ
  {.(Γ ++ E ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
  | inj₂ (E , .(Ξ ++ B ⇐ A ∷ Δ₀) , eq1 , eq2)
  | refl , eq3
  | inj₁ (.(F ∷ Ω₂) , eq4 , refl)
  | inj₂ (.E , Ξ , refl , eq7)
  | refl , refl
  | inj₂ (F , Ω₂ , refl , eq9)
  with inj∷ eq9
... | refl , eq10
  with ++? Δ₁ Ω₂ Λ₁ Λ (sym eq10)
mip≗⊗L⇐L-assoc Γ (E ∷ .((Ξ ++ B ⇐ A ∷ Δ₀) ++ A' ⊗ B' ∷ Ω₂)) Λ
  {.(Γ ++ E ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Ξ ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | refl , refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₂) , refl , refl)
  | inj₂ (E , Ξ , refl , refl)
  | refl , refl
  | inj₂ (.(A' ⊗ B') , Ω₂ , refl , refl)
  | refl , refl
  | inj₂ (H , Ψ , refl , refl)
  rewrite cases++-inj₁ (Ξ ++ B ⇐ A ∷ Δ₀) (Δ₁ ++ H ∷ Ψ) Λ (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ξ) (Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ H ∷ Ψ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ξ) (Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ H ∷ Ψ) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) Γ (Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ H ∷ Ψ) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) Γ (Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ H ∷ Ψ) (B ⇐ A) |
          ++?-inj₁ (H ∷ Ψ) (Δ₀ ++ A' ⊗ B' ∷ Δ₁) Λ |
          ++?-inj₁ (H ∷ Ψ) (Δ₀ ++ A' ∷ B' ∷ Δ₁) Λ =
    intrp≗ (h~ (⊗L⇐L-assoc {Γ = E ∷ Ξ} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = H ∷ Ψ}))
mip≗⊗L⇐L-assoc Γ (E ∷ .(Ξ ++ B ⇐ A ∷ Δ₀ ++ A' ⊗ B' ∷ Ω₂)) .(Ψ ++ Λ₁)
  {.(Γ ++ E ∷ Ξ)} {Δ₀} {.(Ω₂ ++ Ψ)} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Ξ ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | refl , refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₂) , refl , refl)
  | inj₂ (E , Ξ , refl , refl)
  | refl , refl
  | inj₂ (.(A' ⊗ B') , Ω₂ , refl , refl)
  | refl , refl
  | inj₁ (Ψ , refl , refl)
  rewrite cases++-inj₁ (Ξ ++ B ⇐ A ∷ Δ₀) Ω₂ (Ψ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ξ) (Δ₀ ++ A' ⊗ B' ∷ Ω₂) (Ψ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ξ) (Δ₀ ++ A' ∷ B' ∷ Ω₂) (Ψ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) Γ (Δ₀ ++ A' ⊗ B' ∷ Ω₂) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) Γ (Δ₀ ++ A' ∷ B' ∷ Ω₂) (B ⇐ A)
  with Ψ
... | []
  rewrite ++?-inj₁ [] (Δ₀ ++ A' ∷ B' ∷ Ω₂) Λ₁ |
          ++?-inj₁ [] (Δ₀ ++ A' ⊗ B' ∷ Ω₂) Λ₁ =
    intrp≗ (h~ (⊗L⇐L-assoc {Γ = E ∷ Ξ} {Δ₀ = Δ₀} {Δ₁ = Ω₂} {Λ = []}))
... | G ∷ Ψ'
  rewrite ++?-inj₂ (Δ₀ ++ A' ∷ B' ∷ Ω₂) Ψ' Λ₁ G |
          ++?-inj₂ (Δ₀ ++ A' ⊗ B' ∷ Ω₂) Ψ' Λ₁ G |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₂) Δ₀ (G ∷ Ψ') =
    intrp≗
      (h~
        (⊗L⇐R ∘
          ⇐R
            (⊗L⇐L-assoc {Γ = E ∷ Ξ} {Δ₀ = Δ₀}
              {Δ₁ = Ω₂ ++ mip (Δ₀ ++ A' ∷ B' ∷ Ω₂) (G ∷ Ψ') [] f refl .MIP.D ∷ []}
              {Λ = []})))
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₁ (Ω₁ , eq4 , eq5)
  | inj₁ (Ξ , eq6 , eq7)
  with cases∷ Ξ eq6
... | inj₂ (Ξ' , refl , refl)
  with ++? [] Ω₁ (A' ⊗ B' ∷ Δ₁ ++ Λ₁) Λ (sym eq4)
... | inj₁ (F ∷ Ω₂ , eq8 , eq9) = ⊥-elim ([]disj∷ Ω₁ eq9)
mip≗⊗L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ξ') (E ∷ .Ω) .(A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {Γ₁} {.(Ξ' ++ E ∷ Ω)} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  | inj₁ (.(B ⇐ A) ∷ Ξ' , refl , refl)
  | inj₂ (Ξ' , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ [] Ω (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Ω) (A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ξ' (E ∷ Ω) (B ⇐ A) |
          ++?-inj₂ (Ξ' ++ E ∷ Ω) (B' ∷ Δ₁) Λ₁ A' |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Ω) (A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ξ' (E ∷ Ω) (B ⇐ A) |
          ++?-inj₂ (Ξ' ++ E ∷ Ω) Δ₁ Λ₁ (A' ⊗ B') |
          ++?-inj₂ Ξ' Ω (A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₂ [] Ω Δ₁ (A' ⊗ B') =
    intrp≗
      (g~
        (⊗L⇐L-assoc {Γ = Γ₁}
          {Δ₀ = Ξ' ++ mip Ξ' (E ∷ Ω) (A' ∷ B' ∷ Δ₁) f refl .MIP.D ∷ []}
          {Δ₁ = Δ₁} {Λ = Λ₁}))
... | inj₂ (F , Ω₂ , refl , eq8)
  with inj∷ eq8
... | refl , eq9
  with ++? Ω₂ Δ₁ Λ Λ₁ eq9
mip≗⊗L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ξ') (E ∷ .(Ω ++ A' ⊗ B' ∷ Δ₁ ++ Ω₃)) Λ
  {Γ₁} {.(Ξ' ++ E ∷ Ω)} {Δ₁} {.(Ω₃ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (.(A' ⊗ B' ∷ Δ₁ ++ Ω₃) , refl , refl)
  | inj₁ (.(B ⇐ A) ∷ Ξ' , refl , refl)
  | inj₂ (Ξ' , refl , refl)
  | inj₂ (.(A' ⊗ B') , .(Δ₁ ++ Ω₃) , refl , refl)
  | refl , refl
  | inj₁ (Ω₃ , refl , refl)
  rewrite cases++-inj₁ Ω (Δ₁ ++ Ω₃) Λ (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Ω ++ A' ∷ B' ∷ Δ₁ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ξ' (E ∷ Ω ++ A' ∷ B' ∷ Δ₁ ++ Ω₃) (B ⇐ A) |
          ++?-inj₁ Ω₃ (Ξ' ++ E ∷ Ω ++ A' ∷ B' ∷ Δ₁) Λ |
          ++?-inj₁ (E ∷ Ω ++ A' ∷ B' ∷ Δ₁) Ξ' Ω₃ |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Ω ++ A' ⊗ B' ∷ Δ₁ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ξ' (E ∷ Ω ++ A' ⊗ B' ∷ Δ₁ ++ Ω₃) (B ⇐ A) |
          ++?-inj₁ Ω₃ (Ξ' ++ E ∷ Ω ++ A' ⊗ B' ∷ Δ₁) Λ |
          ++?-inj₁ (E ∷ Ω ++ A' ⊗ B' ∷ Δ₁) Ξ' Ω₃ |
          ++?-inj₂ Ξ' Ω (A' ⊗ B' ∷ Δ₁) E |
          cases++-inj₁ Ω Δ₁ [] (A' ⊗ B') =
    intrp≗ (h~ ⊗L⊗R₁)
mip≗⊗L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ξ') (E ∷ .(Ω ++ A' ⊗ B' ∷ Ω₂)) .(H ∷ Ω₃ ++ Λ₁)
  {Γ₁} {.(Ξ' ++ E ∷ Ω)} {.(Ω₂ ++ H ∷ Ω₃)} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , Ω , refl , refl)
  | refl , refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₂) , refl , refl)
  | inj₁ (.(B ⇐ A) ∷ Ξ' , refl , refl)
  | inj₂ (Ξ' , refl , refl)
  | inj₂ (.(A' ⊗ B') , Ω₂ , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₃ , refl , refl)
  rewrite cases++-inj₁ Ω Ω₂ (H ∷ Ω₃ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Ω ++ A' ∷ B' ∷ Ω₂) (H ∷ Ω₃ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ξ' (E ∷ Ω ++ A' ∷ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₂ (Ξ' ++ E ∷ Ω ++ A' ∷ B' ∷ Ω₂) Ω₃ Λ₁ H |
          cases++-inj₁ Γ₁ (Ξ' ++ E ∷ Ω ++ A' ⊗ B' ∷ Ω₂) (H ∷ Ω₃ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ξ' (E ∷ Ω ++ A' ⊗ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₂ (Ξ' ++ E ∷ Ω ++ A' ⊗ B' ∷ Ω₂) Ω₃ Λ₁ H |
          ++?-inj₂ Ξ' Ω (A' ⊗ B' ∷ Ω₂ ++ H ∷ Ω₃) E |
          cases++-inj₁ Ω Ω₂ (H ∷ Ω₃) (A' ⊗ B') = intrp≗ refl
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
  | inj₂ (E , Ω , eq1 , eq2)
  | refl , eq3
  | inj₁ (Ω₁ , eq4 , eq5)
  | inj₁ (Ξ , eq6 , eq7)
  | inj₁ (refl , refl , refl)
  with ++? [] Ω₁ (A' ⊗ B' ∷ Δ₁ ++ Λ₁) Λ (sym eq4)
... | inj₁ (F ∷ Ω₂ , eq8 , eq9) = ⊥-elim ([]disj∷ Ω₁ eq9)
mip≗⊗L⇐L-assoc .Γ₁ (.(B ⇐ A) ∷ .Ω) .(A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {Γ₁} {Ω} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (.(B ⇐ A) , Ω , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ [] Ω (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ Ω (A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Ω (B ⇐ A) |
          ++?-inj₂ Ω (B' ∷ Δ₁) Λ₁ A' |
          cases++-inj₁ Γ₁ Ω (A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Ω (B ⇐ A) |
          ++?-inj₂ Ω Δ₁ Λ₁ (A' ⊗ B') |
          ++?-inj₁ [] Ω (A' ⊗ B' ∷ Δ₁) =
    intrp≗ (g~ (⊗L⇐L-assoc {Γ = Γ₁} {Δ₀ = []} {Δ₁ = Δ₁} {Λ = Λ₁}))
... | inj₂ (F , Ω₂ , refl , eq8)
  with inj∷ eq8
... | refl , eq9
  with ++? Ω₂ Δ₁ Λ Λ₁ eq9
mip≗⊗L⇐L-assoc .Γ₁ (.(B ⇐ A) ∷ .(Ω ++ A' ⊗ B' ∷ Δ₁ ++ Ω₃)) Λ
  {Γ₁} {Ω} {Δ₁} {.(Ω₃ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (.(B ⇐ A) , Ω , refl , refl)
  | refl , refl
  | inj₁ (.(A' ⊗ B' ∷ Δ₁ ++ Ω₃) , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (.(A' ⊗ B') , .(Δ₁ ++ Ω₃) , refl , refl)
  | refl , refl
  | inj₁ (Ω₃ , refl , refl)
  rewrite cases++-inj₁ Ω (Δ₁ ++ Ω₃) Λ (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ω ++ A' ∷ B' ∷ Δ₁ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Ω ++ A' ∷ B' ∷ Δ₁ ++ Ω₃) (B ⇐ A) |
          ++?-inj₁ Ω₃ (Ω ++ A' ∷ B' ∷ Δ₁) Λ |
          cases++-inj₁ Γ₁ (Ω ++ A' ⊗ B' ∷ Δ₁ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Ω ++ A' ⊗ B' ∷ Δ₁ ++ Ω₃) (B ⇐ A) |
          ++?-inj₁ Ω₃ (Ω ++ A' ⊗ B' ∷ Δ₁) Λ =
    intrp≗ (h~ (⊗L⇐L-assoc {Γ = []} {Δ₀ = Ω} {Δ₁ = Δ₁} {Λ = Ω₃}))
mip≗⊗L⇐L-assoc .Γ₁ (.(B ⇐ A) ∷ .(Ω ++ A' ⊗ B' ∷ Ω₂)) .(H ∷ Ω₃ ++ Λ₁)
  {Γ₁} {Ω} {.(Ω₂ ++ H ∷ Ω₃)} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (.(B ⇐ A) , Ω , refl , refl)
  | refl , refl
  | inj₁ (.(A' ⊗ B' ∷ Ω₂) , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (.(A' ⊗ B') , Ω₂ , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₃ , refl , refl)
  rewrite cases++-inj₁ Ω Ω₂ (H ∷ Ω₃ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ Γ₁ (Ω ++ A' ∷ B' ∷ Ω₂) (H ∷ Ω₃ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Ω ++ A' ∷ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₂ (Ω ++ A' ∷ B' ∷ Ω₂) Ω₃ Λ₁ H |
          cases++-inj₁ Γ₁ (Ω ++ A' ⊗ B' ∷ Ω₂) (H ∷ Ω₃ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Ω ++ A' ⊗ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₂ (Ω ++ A' ⊗ B' ∷ Ω₂) Ω₃ Λ₁ H |
          ++?-inj₁ (A' ⊗ B' ∷ Ω₂) Ω (H ∷ Ω₃) =
    intrp≗
      (h~
        (⊗L⇐R ∘
          ⇐R
            (⊗L⇐L-assoc {Γ = []} {Δ₀ = Ω}
              {Δ₁ = Ω₂ ++ mip (Ω ++ A' ∷ B' ∷ Ω₂) (H ∷ Ω₃) [] f refl .MIP.D ∷ []}
              {Λ = []})))
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) .(H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
  | inj₂ (E , .(Δ ++ H ∷ Ω₁) , eq1 , refl)
  | refl , refl
  | inj₂ (H , Ω₁ , refl , refl)
  | inj₂ (K , Ξ , refl , eq7)
  with inj∷ eq7
... | refl , eq8
  with ++? Ξ Δ (B ⇐ A ∷ Δ₀) (H ∷ Ω₁) eq8
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) .(B ⇐ A ∷ Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Δ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Δ ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | refl , refl
  | inj₂ (.(B ⇐ A) , Δ₀ , refl , refl)
  | inj₂ (E , Δ , refl , refl)
  | refl , refl
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ (B ⇐ A ∷ Δ₀) Δ (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₂ [] (Γ ++ E ∷ Δ) (Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] (Γ ++ E ∷ Δ) (Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) =
    intrp≗
      (g~
        (⊗L⇐L-assoc {Γ = Γ ++ mip Γ (E ∷ Δ) (B ∷ Λ₁) g refl .MIP.D ∷ []}
          {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁}))
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) .(H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Δ ++ H ∷ Ω₁) , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₁ , refl , refl)
  | inj₂ (E , Ξ , refl , eq7)
  | refl , eq8
  | inj₁ (H ∷ Ψ , refl , refl)
  rewrite cases++-inj₂ (H ∷ Ψ ++ B ⇐ A ∷ Δ₀) Δ (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₂ (H ∷ Ψ) (Γ ++ E ∷ Δ) (Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (H ∷ Ψ) (Γ ++ E ∷ Δ) (Δ₀ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) =
    intrp≗
      (g~
        (⊗L⇐L-assoc
          {Γ = Γ ++ mip Γ (E ∷ Δ) (H ∷ Ψ ++ B ∷ Λ₁) g refl .MIP.D ∷ H ∷ Ψ}
          {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁}))
mip≗⊗L⇐L-assoc Γ (E ∷ Δ) .(H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Ξ)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} refl
  | inj₂ (E , .(Δ ++ H ∷ Ω₁) , refl , refl)
  | refl , refl
  | inj₂ (H , Ω₁ , refl , refl)
  | inj₂ (E , Ξ , refl , eq7)
  | refl , eq8
  | inj₂ (.(B ⇐ A) , Ψ , refl , refl)
  rewrite cases++-inj₂ (H ∷ Ω₁) (Ξ ++ B ⇐ A ∷ Ψ) (Δ₁ ++ Λ₁) (A' ⊗ B') |
          cases++-inj₁ (Γ ++ E ∷ Ξ) Ψ (H ∷ Ω₁ ++ A' ∷ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) Γ Ψ (B ⇐ A) |
          ++?-inj₂ Ψ (Ω₁ ++ A' ∷ B' ∷ Δ₁) Λ₁ H |
          cases++-inj₁ (Γ ++ E ∷ Ξ) Ψ (H ∷ Ω₁ ++ A' ⊗ B' ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ) Γ Ψ (B ⇐ A) |
          ++?-inj₂ Ψ (Ω₁ ++ A' ⊗ B' ∷ Δ₁) Λ₁ H |
          ++?-inj₂ Ψ Ω₁ (A' ⊗ B' ∷ Δ₁) H |
          cases++-inj₁ Ω₁ Δ₁ [] (A' ⊗ B') =
    intrp≗ (g~ (⊗L⇐L-assoc {Γ = Γ} {Δ₀ = H ∷ Ω₁} {Δ₁ = Δ₁} {Λ = Λ₁}))
