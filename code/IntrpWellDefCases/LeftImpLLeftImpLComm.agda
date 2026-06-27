{-# OPTIONS --rewriting  #-}

module IntrpWellDefCases.LeftImpLLeftImpLComm where

open import IntrpWellDefCases.Base

-- window covers the principal B'⇐A' and its argument fully, with g-material
-- Λ₀ (in the window, before B') and Ω' (after); arbitrary prefix Γ'.
mip⇐L~ΓΛ : ∀ Γ' Λ₀ Δ₁ Ω' Λ {B' A' C : Fma}
  {f : Δ₁ ⊢ A'} {g : Γ' ++ Λ₀ ++ B' ∷ Ω' ++ Λ ⊢ C}
  → mip Γ' (Λ₀ ++ B' ⇐ A' ∷ Δ₁ ++ Ω') Λ (⇐L {Γ' ++ Λ₀} {Δ₁} {Ω' ++ Λ} f g) refl
      ~ ⇐L~ΓΛ' (mip Γ' (Λ₀ ++ B' ∷ Ω') Λ g refl) f
mip⇐L~ΓΛ Γ' [] Δ₁ Ω' Λ {B'} {A'}
  rewrite cases++-inj₁ Γ' (Δ₁ ++ Ω') Λ (B' ⇐ A') |
          cases++-inj₂ [] Γ' (Δ₁ ++ Ω') (B' ⇐ A') |
          ++?-inj₁ Ω' Δ₁ Λ = refl
mip⇐L~ΓΛ Γ' (E ∷ Λ₀) Δ₁ Ω' Λ {B'} {A'}
  rewrite cases++-inj₁ (Γ' ++ E ∷ Λ₀) (Δ₁ ++ Ω') Λ (B' ⇐ A') |
          cases++-inj₂ (E ∷ Λ₀) Γ' (Δ₁ ++ Ω') (B' ⇐ A') |
          ++?-inj₁ Ω' Δ₁ Λ = refl


mip≗⇐L⇐L-comm : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ Ξ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ⊢ A} {f' : Δ₁ ⊢ A'} {g : Γ₁ ++ B ∷ Λ₁ ++ B' ∷ Ξ ⊢ C}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₀ ++ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₀} {Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ} f (⇐L {Γ₁ ++ B ∷ Λ₁} {Δ₁} {Ξ} f' g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁ ++ B ⇐ A ∷ Δ₀ ++ Λ₁} {Δ₁} {Ξ} f' (⇐L {Γ₁} {Δ₀} {Λ₁ ++ B' ∷ Ξ} f g)) eq)
mip≗⇐L⇐L-comm Γ [] Λ eq = mip[]≗ Γ Λ eq ⇐L⇐L-comm
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq 
  with cases++ (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) (Γ ++ E ∷ Δ) (Δ₀ ++ Λ₁) Λ
   (sym eq)
... | inj₁ (Ω , eq1 , eq2) 
  with ++? Ω Δ₀ Λ Λ₁ eq2
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , eq1 , refl) | inj₁ (Ω' , refl , refl) 
  with cases++ Γ Γ₀ Δ (B ⇐ A ∷ Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') (sym eq1)
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} refl | inj₁ (.(Δ₀ ++ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω'') (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'' ++ B ⇐ A ∷ Γ₁ ++ Λ₀) Γ (Δ₀ ++ Ω') (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω'') Γ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' Δ₀ Λ |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Γ₁ Λ |
          cases++-inj₁ (Γ ++ E ∷ Ω'' ++ B ∷ Λ₀) (Δ₀ ++ Ω') Λ (B' ⇐ A') |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Γ₁ ++ Λ₀ ++ B' ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'' ++ B ∷ Λ₀) Γ (Δ₀ ++ Ω') (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω'') Γ (Γ₁ ++ Λ₀ ++ B' ∷ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' Δ₀ Λ |
          ++?-inj₁ (Λ₀ ++ B' ∷ Ω') Γ₁ Λ = intrp≗ (h~ ⇐L⇐L-comm)
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , eq1 , refl) | inj₁ (Ω' , refl , refl)  | inj₂ (Ω'' , eq2 , refl)
  with cases++ Ω'' (B ⇐ A ∷ Γ₁) Δ (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') eq2
mip≗⇐L⇐L-comm .(Γ₀ ++ []) (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} refl | inj₁ (.(Δ₀ ++ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (B ⇐ A ∷ Γ₁ ++ Λ₀) Γ₀ (Δ₀ ++ Ω') (B' ⇐ A') |
          cases++-inj₂ [] Γ₀ (Ω''' ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' Δ₀ Λ |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Ω''' Λ |
          cases++-inj₁ Γ₀ (Ω''' ++ Λ₀ ++ B' ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₁ (Γ₀ ++ B ∷ Λ₀) (Δ₀ ++ Ω') Λ (B' ⇐ A') |
          cases++-inj₂ [] Γ₀ (Ω''' ++ Λ₀ ++ B' ∷ Ω') (B ⇐ A) |
          cases++-inj₂ (B ∷ Λ₀) Γ₀ (Δ₀ ++ Ω') (B' ⇐ A') |
          ++?-inj₁ (Λ₀ ++ B' ∷ Ω') Ω''' Λ |
          ++?-inj₁ Ω' Δ₀ Λ = intrp≗ (h~ ⇐L⇐L-comm)
mip≗⇐L⇐L-comm .(Γ₀ ++ x ∷ Ω'') (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} refl | inj₁ (.(Δ₀ ++ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (x ∷ Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Ω'' ++ E ∷ Ω''' ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω''' ++ Λ₀) (Γ₀ ++ B ⇐ A ∷ Ω'') (Δ₀ ++ Ω') (B' ⇐ A') |
          cases++-inj₁ Γ₀ Ω'' (E ∷ Ω''' ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' Δ₀ Λ |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') (Ω'' ++ E ∷ Ω''') Λ |
          cases++-inj₁ Γ₀ (Ω'' ++ E ∷ Ω''' ++ Λ₀ ++ B' ∷ Ω') Λ (B ⇐ A) |
          ++?-inj₁ (E ∷ Ω''') Ω'' (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') |
          cases++-inj₁ Γ₀ Ω'' (E ∷ Ω''' ++ Λ₀ ++ B' ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (Λ₀ ++ B' ∷ Ω') (Ω'' ++ E ∷ Ω''') Λ |
          ++?-inj₁ (E ∷ Ω''') Ω'' (Λ₀ ++ B' ∷ Ω') =
  intrp≗ (~-trans (⇐L~⊗ refl (mip⇐L~ΓΛ (Γ₀ ++ B ∷ []) Λ₀ Δ₀ Ω' Λ)) (h~ (~ ⇐L⊗R₂)))
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , eq1 , refl) | inj₁ (Ω' , refl , refl)  | inj₂ (Ω'' , eq2 , refl) | inj₂ (Ω''' , eq3 , refl) 
  with cases++ Ω''' Λ₀ Δ (B' ⇐ A' ∷ Δ₀ ++ Ω') eq3
mip≗⇐L⇐L-comm .(Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Ω''') (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} refl | inj₁ (.(Δ₀ ++ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (.(B ⇐ A ∷ Γ₁ ++ Ω''') , refl , refl) | inj₂ (Ω''' , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Γ₁ ++ Ω''' ++ E ∷ Ξ' ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ') (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Ω''') (Δ₀ ++ Ω') (B' ⇐ A') |
          cases++-inj₁ Γ₀ (Γ₁ ++ Ω''') (E ∷ Ξ' ++ B' ⇐ A' ∷ Δ₀ ++ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' Δ₀ Λ |
          ++?-inj₁ (Ω''' ++ E ∷ Ξ' ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Γ₁ Λ
  with Ω'''
... | [] rewrite ++?-inj₁ [] Γ₁ (E ∷ Ξ' ++ B' ⇐ A' ∷ Δ₀ ++ Ω') |
                 cases++-inj₁ Γ₀ (Γ₁ ++ E ∷ Ξ' ++ B' ∷ Ω') Λ (B ⇐ A) |
                 cases++-inj₁ Γ₀ Γ₁ (E ∷ Ξ' ++ B' ∷ Ω') (B ⇐ A) |
                 ++?-inj₁ (E ∷ Ξ' ++ B' ∷ Ω') Γ₁ Λ |
                 ++?-inj₁ [] Γ₁ (E ∷ Ξ' ++ B' ∷ Ω') =
  intrp≗
    (~-trans (⇐L~⊗ refl
      (mip⇐L~ΓΛ (Γ₀ ++ B ∷ []) (E ∷ Ξ') Δ₀ Ω' Λ))
      (h~ (~ ⇐L⊗R₂)))
... | F ∷ Ω'''' rewrite ++?-inj₂ Γ₁ Ω'''' (E ∷ Ξ' ++ B' ⇐ A' ∷ Δ₀ ++ Ω') F |
                         cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Ω'''' ++ E ∷ Ξ' ++ B' ∷ Ω') Λ (B ⇐ A) |
                         cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Ω'''') (E ∷ Ξ' ++ B' ∷ Ω') (B ⇐ A) |
                         ++?-inj₁ (F ∷ Ω'''' ++ E ∷ Ξ' ++ B' ∷ Ω') Γ₁ Λ |
                         cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Ω'''' ++ E ∷ Ξ') (Δ₀ ++ Ω') Λ (B' ⇐ A') |
                         cases++-inj₂ (E ∷ Ξ') (Γ₀ ++ B ∷ F ∷ Ω'''') (Δ₀ ++ Ω') (B' ⇐ A') |
                         ++?-inj₁ Ω' Δ₀ Λ |
                         ++?-inj₂ Γ₁ Ω'''' (E ∷ Ξ' ++ B' ∷ Ω') F =
  intrp≗ refl
mip≗⇐L⇐L-comm .(Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} refl | inj₁ (.(Δ₀ ++ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (.(B ⇐ A ∷ Γ₁ ++ Λ₀) , refl , refl) | inj₂ (Λ₀ , refl , refl) | inj₂ ([] , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Λ (B ⇐ A) |
          cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) (Δ₀ ++ Ω') (B' ⇐ A') |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀) (B' ⇐ A' ∷ Δ₀ ++ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' Δ₀ Λ |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ω') Γ₁ Λ
  with Λ₀
... | [] rewrite ++?-inj₁ [] Γ₁ (B' ⇐ A' ∷ Δ₀ ++ Ω') |
                 cases++-inj₁ Γ₀ (Γ₁ ++ B' ∷ Ω') Λ (B ⇐ A) |
                 cases++-inj₁ Γ₀ Γ₁ (B' ∷ Ω') (B ⇐ A) |
                 ++?-inj₁ (B' ∷ Ω') Γ₁ Λ |
                 ++?-inj₁ [] Γ₁ (B' ∷ Ω') =
  intrp≗
    (~-trans (⇐L~⊗ refl
      (mip⇐L~ΓΛ (Γ₀ ++ B ∷ []) [] Δ₀ Ω' Λ))
      (h~ (~ ⇐L⊗R₂)))
... | F ∷ Λ₀'
  rewrite ++?-inj₂ Γ₁ Λ₀' (B' ⇐ A' ∷ Δ₀ ++ Ω') F |
          cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Λ₀' ++ B' ∷ Ω') Λ (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Λ₀') (B' ∷ Ω') (B ⇐ A) |
          ++?-inj₁ (F ∷ Λ₀' ++ B' ∷ Ω') Γ₁ Λ |
          cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Λ₀') (Δ₀ ++ Ω') Λ (B' ⇐ A') |
          cases++-inj₂ [] (Γ₀ ++ B ∷ F ∷ Λ₀') (Δ₀ ++ Ω') (B' ⇐ A') |
          ++?-inj₁ Ω' Δ₀ Λ |
          ++?-inj₂ Γ₁ Λ₀' (B' ∷ Ω') F =
  intrp≗ refl
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} eq | inj₁ (Ω , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , eq2 , refl) | inj₂ (Ω''' , eq3 , refl) | inj₂ (x ∷ Ξ' , eq4 , refl) 
  with cases++ Ξ' Δ₀ Δ Ω' (inj∷ eq4 .proj₂)
mip≗⇐L⇐L-comm .(Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀ ++ x ∷ Ξ') (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} refl | inj₁ (.(Δ₀ ++ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (.(B ⇐ A ∷ Γ₁ ++ Λ₀ ++ x ∷ Ξ') , refl , refl) | inj₂ (.(Λ₀ ++ x ∷ Ξ') , refl , refl) | inj₂ (x ∷ Ξ' , refl , refl) | inj₁ (Ξ'' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ξ' ++ E ∷ Ξ'' ++ Ω') Λ (B ⇐ A) |
          cases++-inj₁ (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) Ξ' (E ∷ Ξ'' ++ Ω') (B' ⇐ A') |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ξ') (E ∷ Ξ'' ++ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' (Ξ' ++ E ∷ Ξ'') Λ |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Ξ' ++ E ∷ Ξ'' ++ Ω') Γ₁ Λ |
          ++?-inj₁ (E ∷ Ξ'') Ξ' Ω'
  with Λ₀
... | []
  rewrite ++?-inj₂ Γ₁ Ξ' (E ∷ Ξ'' ++ Ω') (B' ⇐ A') |
          cases++-inj₁ (Γ₀ ++ B ∷ []) (Ξ' ++ E ∷ Ξ'' ++ Ω') Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₀ ++ B ∷ []) Ξ' (E ∷ Ξ'' ++ Ω') (B' ⇐ A') |
          ++?-inj₁ Ω' (Ξ' ++ E ∷ Ξ'') Λ |
          ++?-inj₁ (E ∷ Ξ'') Ξ' Ω' =
  intrp≗
    (~-trans
      (g~
        ((~ (⊗L⇐L-comm₂ {Γ = Γ₀} {Δ = Γ₁}
              {Λ = B' ⇐ A' ∷ Ξ'} {Ω = Λ}))
        ∘ ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁ ++ B' ⇐ A' ∷ Ξ'} {Δ = Λ}
            ⇐L⇐L-comm))
      (~-sym
        (⇐L~⊗ {Γ₀ = Γ₀ ++ B ⇐ A ∷ Γ₁} {Γ₁ = Ξ'}
          {Δ₀ = E ∷ Ξ''} {Δ₁ = Ω'} {Λ = Λ} {A = A'} {B = B'}
          refl (mip⇐L~Γ Γ₀ B' [] Ω' Λ {Ω = Γ₁}))))
... | F ∷ Λ₀'
  rewrite ++?-inj₂ Γ₁ (Λ₀' ++ B' ⇐ A' ∷ Ξ') (E ∷ Ξ'' ++ Ω') F |
          cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Λ₀') (Ξ' ++ E ∷ Ξ'' ++ Ω') Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Λ₀') Ξ' (E ∷ Ξ'' ++ Ω') (B' ⇐ A') |
          ++?-inj₁ Ω' (Ξ' ++ E ∷ Ξ'') Λ |
          ++?-inj₁ (E ∷ Ξ'') Ξ' Ω' =
  intrp≗
    (~-trans
      (g~
        ((~ (⊗L⇐L-comm₂ {Γ = Γ₀} {Δ = Γ₁}
              {Λ = F ∷ Λ₀' ++ B' ⇐ A' ∷ Ξ'} {Ω = Λ}))
        ∘ ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁ ++ F ∷ Λ₀' ++ B' ⇐ A' ∷ Ξ'}
            {Δ = Λ} ⇐L⇐L-comm))
      (~-sym
        (⇐L~⊗ {Γ₀ = Γ₀ ++ B ⇐ A ∷ Γ₁ ++ F ∷ Λ₀'} {Γ₁ = Ξ'}
          {Δ₀ = E ∷ Ξ''} {Δ₁ = Ω'} {Λ = Λ} {A = A'} {B = B'}
          refl (mip⇐L~Γ Γ₀ F (Λ₀' ++ B' ∷ []) Ω' Λ {Ω = Γ₁}))))
mip≗⇐L⇐L-comm .(Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀ ++ x ∷ Ξ') (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω' ++ Λ)} {A} {B} {A'} {B'} {f = f} {f' = f'} {g = g} refl | inj₁ (.(Δ₀ ++ Ω') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (.(B ⇐ A ∷ Γ₁ ++ Λ₀ ++ x ∷ Ξ') , refl , refl) | inj₂ (.(Λ₀ ++ x ∷ Ξ') , refl , refl) | inj₂ (x ∷ Ξ' , refl , refl) | inj₂ (Ξ'' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ξ'' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ξ'') (E ∷ Δ) (B ⇐ A) |
          cases++-inj₁ (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) (Δ₀ ++ Ξ'') (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Ξ'' ++ E ∷ Δ) Γ₁ Λ |
          ++?-inj₁ (Ξ'' ++ E ∷ Δ) Δ₀ Λ
  with Λ₀ | Ξ''
... | [] | []
  rewrite ++?-inj₂ Γ₁ Δ₀ (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₁ [] Δ₀ (E ∷ Δ) |
          cases++-inj₁ (Γ₀ ++ B ∷ []) (Δ₀ ++ E ∷ Δ) Λ (B' ⇐ A') |
          cases++-inj₁ Γ₀ (Γ₁ ++ B' ∷ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ (Γ₀ ++ B ∷ []) Δ₀ (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₁ (E ∷ Δ) Δ₀ Λ |
          ++?-inj₁ [] Δ₀ (E ∷ Δ) |
          cases++-inj₁ Γ₀ (Γ₁ ++ B' ∷ []) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (B' ∷ E ∷ Δ) Γ₁ Λ |
          ++?-inj₂ Γ₁ [] (E ∷ Δ) B'
  =
  intrp≗
    (g~
      ((~ ⊗L⇐L-comm₂ {Γ = Γ₀} {Δ = Γ₁}
          {Λ = B' ⇐ A' ∷ Δ₀} {Ω = Λ})
      ∘ ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁ ++ B' ⇐ A' ∷ Δ₀}
          {Δ = Λ} ⇐L⇐L-comm))
... | [] | G ∷ Ξ'''
  rewrite ++?-inj₂ Γ₁ (Δ₀ ++ G ∷ Ξ''') (E ∷ Δ) (B' ⇐ A') |
          cases++-inj₁ (Γ₀ ++ B ∷ []) (Δ₀ ++ G ∷ Ξ''' ++ E ∷ Δ) Λ (B' ⇐ A') |
          ++?-inj₂ Δ₀ Ξ''' (E ∷ Δ) G |
          cases++-inj₁ (Γ₀ ++ B ∷ []) (Δ₀ ++ G ∷ Ξ''') (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₁ (G ∷ Ξ''' ++ E ∷ Δ) Δ₀ Λ |
          ++?-inj₂ Δ₀ Ξ''' (E ∷ Δ) G |
          cases++-inj₁ Γ₀ (Γ₁ ++ B' ∷ G ∷ Ξ''' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ B' ∷ G ∷ Ξ''') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (B' ∷ G ∷ Ξ''' ++ E ∷ Δ) Γ₁ Λ |
          ++?-inj₂ Γ₁ (G ∷ Ξ''') (E ∷ Δ) B'
  = intrp≗ (g~ ⇐L⇐L-comm)
... | F ∷ Λ₀' | []
  rewrite ++?-inj₂ Γ₁ (Λ₀' ++ B' ⇐ A' ∷ Δ₀) (E ∷ Δ) F |
          ++?-inj₁ [] Δ₀ (E ∷ Δ) |
          cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Λ₀') (Δ₀ ++ E ∷ Δ) Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Λ₀') Δ₀ (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₁ (E ∷ Δ) Δ₀ Λ |
          ++?-inj₁ [] Δ₀ (E ∷ Δ) |
          cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Λ₀' ++ B' ∷ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Λ₀' ++ B' ∷ []) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Λ₀' ++ B' ∷ E ∷ Δ) Γ₁ Λ |
          ++?-inj₂ Γ₁ (Λ₀' ++ B' ∷ []) (E ∷ Δ) F =
  intrp≗
    (g~
      ((~ ⊗L⇐L-comm₂ {Γ = Γ₀} {Δ = Γ₁}
          {Λ = F ∷ Λ₀' ++ B' ⇐ A' ∷ Δ₀} {Ω = Λ})
      ∘ ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁ ++ F ∷ Λ₀' ++ B' ⇐ A' ∷ Δ₀}
          {Δ = Λ} ⇐L⇐L-comm))
... | F ∷ Λ₀' | G ∷ Ξ'''
  rewrite ++?-inj₂ Γ₁ (Λ₀' ++ B' ⇐ A' ∷ Δ₀ ++ G ∷ Ξ''') (E ∷ Δ) F |
          cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Λ₀') (Δ₀ ++ G ∷ Ξ''' ++ E ∷ Δ) Λ (B' ⇐ A') |
          ++?-inj₂ Δ₀ Ξ''' (E ∷ Δ) G |
          cases++-inj₁ (Γ₀ ++ B ∷ F ∷ Λ₀') (Δ₀ ++ G ∷ Ξ''') (E ∷ Δ) (B' ⇐ A') |
          cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Λ₀' ++ B' ∷ G ∷ Ξ''' ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ F ∷ Λ₀' ++ B' ∷ G ∷ Ξ''') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Λ₀' ++ B' ∷ G ∷ Ξ''' ++ E ∷ Δ) Γ₁ Λ |
          ++?-inj₂ Γ₁ (Λ₀' ++ B' ∷ G ∷ Ξ''') (E ∷ Δ) F |
          ++?-inj₁ (G ∷ Ξ''' ++ E ∷ Δ) Δ₀ Λ |
          ++?-inj₂ Δ₀ Ξ''' (E ∷ Δ) G = intrp≗ (g~ ⇐L⇐L-comm)
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , eq1 , refl) | inj₂ (F , Ω' , refl , refl) 
  with  cases++ Γ Γ₀ Δ (B ⇐ A ∷ Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ω) (sym eq1)
mip≗⇐L⇐L-comm Γ (E ∷ Δ) .(F ∷ Ω' ++ Λ₁) {Γ₀} {Γ₁} {.(Ω ++ F ∷ Ω')} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (Ω , refl , refl) | inj₂ (F , Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω'') (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ω) (F ∷ Ω' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'' ++ B ⇐ A ∷ Γ₁ ++ Λ₀) Γ Ω (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω'') Γ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ω) (B ⇐ A) |
          ++?-inj₂ Ω Ω' Λ₁ F |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Ω) Γ₁ (F ∷ Ω' ++ Λ₁) |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Γ₁ ++ Λ₀ ++ B' ∷ []) Λ₁ (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω'' ++ B ∷ Λ₀) Ω (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω'' ++ B ∷ Λ₀) Γ Ω (B' ⇐ A') |
          ++?-inj₂ Ω Ω' Λ₁ F |
          cases++-inj₂ (E ∷ Ω'') Γ (Γ₁ ++ Λ₀ ++ B' ∷ []) (B ⇐ A) |
          ++?-inj₁ (Λ₀ ++ B' ∷ []) Γ₁ Λ₁ =
  intrp≗ (h~ (⇐L⇐R ∘ ⇐R ⇐L⇐L-comm))
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , eq1 , refl) | inj₂ (F , Ω' , refl , refl)  | inj₂ (Ω'' , eq2 , refl) 
  with cases++ Ω'' (B ⇐ A ∷ Γ₁) Δ (Λ₀ ++ B' ⇐ A' ∷ Ω) eq2
mip≗⇐L⇐L-comm .(Γ₀ ++ []) (E ∷ Δ) .(F ∷ Ω' ++ Λ₁) {Γ₀} {Γ₁} {.(Ω ++ F ∷ Ω')} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (Ω , refl , refl) | inj₂ (F , Ω' , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Γ₁ , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ω) (F ∷ Ω' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (B ⇐ A ∷ Γ₁ ++ Λ₀) Γ₀ Ω (B' ⇐ A') |
          cases++-inj₂ [] Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ω) (B ⇐ A) |
          ++?-inj₂ Ω Ω' Λ₁ F |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Ω) Γ₁ (F ∷ Ω' ++ Λ₁) |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ∷ []) Λ₁ (B ⇐ A) |
          cases++-inj₁ (Γ₀ ++ B ∷ Λ₀) Ω (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
          cases++-inj₂ [] Γ₀ (Γ₁ ++ Λ₀ ++ B' ∷ []) (B ⇐ A) |
          cases++-inj₂ (B ∷ Λ₀) Γ₀ Ω (B' ⇐ A') |
          ++?-inj₁ (Λ₀ ++ B' ∷ []) Γ₁ Λ₁ |
          ++?-inj₂ Ω Ω' Λ₁ F =
  intrp≗ (h~ (⇐L⇐R ∘ ⇐R ⇐L⇐L-comm))
mip≗⇐L⇐L-comm .(Γ₀ ++ x ∷ Ω'') (E ∷ Δ) .(F ∷ Ω' ++ Λ₁) {Γ₀} {Γ₁} {.(Ω ++ F ∷ Ω')} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C = C} {f = f} {f' = f'} {g = g} refl | inj₁ (Ω , refl , refl) | inj₂ (F , Ω' , refl , refl) | inj₂ (x ∷ Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Ω'' ++ E ∷ Ω''' ++ Λ₀ ++ B' ⇐ A' ∷ Ω) (F ∷ Ω' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω''' ++ Λ₀) (Γ₀ ++ B ⇐ A ∷ Ω'') Ω (B' ⇐ A') |
          cases++-inj₁ Γ₀ Ω'' (E ∷ Ω''' ++ Λ₀ ++ B' ⇐ A' ∷ Ω) (B ⇐ A) |
          ++?-inj₂ Ω Ω' Λ₁ F |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Ω) (Ω'' ++ E ∷ Ω''') (F ∷ Ω' ++ Λ₁) |
          cases++-inj₁ Γ₀ (Ω'' ++ E ∷ Ω''' ++ Λ₀ ++ B' ∷ []) Λ₁ (B ⇐ A) |
          ++?-inj₁ (E ∷ Ω''') Ω'' (Λ₀ ++ B' ⇐ A' ∷ Ω) |
          cases++-inj₁ Γ₀ Ω'' (E ∷ Ω''' ++ Λ₀ ++ B' ∷ []) (B ⇐ A) |
          ++?-inj₁ (Λ₀ ++ B' ∷ []) (Ω'' ++ E ∷ Ω''') Λ₁ |
          ++?-inj₁ (E ∷ Ω''') Ω'' (Λ₀ ++ B' ∷ []) 
  with Λ₀
... | [] rewrite cases++-inj₁ (Γ₀ ++ B ∷ []) Ω (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
                 cases++-inj₂ [] (Γ₀ ++ B ∷ []) Ω (B' ⇐ A') |
                 ++?-inj₂ Ω Ω' Λ₁ F =
  intrp≗ (↝∷ (t , eqg , eqh) refl)
  where
    Fm = mip Ω'' (E ∷ Ω''') [] f refl
    Gm = mip (Γ₀ ++ B ∷ []) (B' ∷ []) Λ₁ g refl
    Hm = mip Ω (F ∷ Ω') [] f' refl
    lhs : MIP (Γ₀ ++ B ⇐ A ∷ Ω'') (E ∷ Ω''' ++ B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    lhs =
      ⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Ω''} {Δ₀ = E ∷ Ω'''}
        {Δ₁ = B' ⇐ A' ∷ Ω} {Λ = F ∷ Ω' ++ Λ₁} {A = A} {B = B}
        Fm
        (⇐L~⇐' {Γ = Γ₀ ++ B ∷ []} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
          {Λ₀ = []} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm Gm)
    rhs : MIP (Γ₀ ++ B ⇐ A ∷ Ω'') (E ∷ Ω''' ++ B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    rhs =
      ⇐L~⇐' {Γ = Γ₀ ++ B ⇐ A ∷ Ω''} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
        {Λ₀ = E ∷ Ω'''} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm
        (⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Ω''} {Δ₀ = E ∷ Ω'''}
          {Δ₁ = B' ∷ []} {Λ = Λ₁} {A = A} {B = B} Fm Gm)
    t : MIP.D Fm ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [] ⊢
        (MIP.D Fm ⊗ MIP.D Gm) ⇐ MIP.D Hm
    t = ⇐R (⊗L {Γ = []} {Δ = MIP.D Hm ∷ []}
      (⊗R (ax {A = MIP.D Fm})
        (⇐L {Γ = []} {Δ = MIP.D Hm ∷ []} {Λ = []}
          (ax {A = MIP.D Hm}) (ax {A = MIP.D Gm}))))
    eqg :
      MIP.g lhs ≗ cut (Γ₀ ++ B ⇐ A ∷ Ω'') t (MIP.g rhs) refl
    eqg
      rewrite cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Ω'') (F ∷ Ω' ++ Λ₁)
        ((MIP.D Fm ⊗ MIP.D Gm) ⇐ MIP.D Hm) |
        cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Ω'') Λ₁ (MIP.D Fm ⊗ MIP.D Gm) |
        cases++-inj₂ (MIP.D Fm ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [])
          (Γ₀ ++ B ⇐ A ∷ Ω'') Λ₁ (MIP.D Hm) |
        cases++-inj₂ (B ⇐ A ∷ Ω'' ++ MIP.D Fm ∷ []) Γ₀ Λ₁ (MIP.D Gm) |
        cases++-inj₂ [] (Ω'' ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Gm) |
        cases++-inj₂ (B ⇐ A ∷ Ω'') Γ₀
          (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁) (MIP.D Fm) |
        cases++-inj₁ Ω'' [] (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁)
          (MIP.D Fm) |
        cases++-inj₂
          (B ⇐ A ∷ Ω'' ++ MIP.D Fm ∷ MIP.D Gm ⇐ MIP.D Hm ∷ [])
          Γ₀ Λ₁ (MIP.D Hm) |
        cases++-inj₂ (MIP.D Gm ⇐ MIP.D Hm ∷ [])
          (Ω'' ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Hm) =
      ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Ω''}
        {Δ = F ∷ Ω' ++ Λ₁}
        (⇐L (~ (cutaxA-left Ω'' (MIP.g Fm) refl))
        (((⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = F ∷ Ω'} {Λ = Λ₁}
            {A = MIP.D Hm} {B = MIP.D Gm}
            (~ (cutaxA-right (MIP.h Hm))) refl)
          ∘ (~ (≡to≗ (cut⇐L-cases++₁ [] (Γ₀ ++ B ∷ [])))))
          ∘ cut-cong₂ (Γ₀ ++ B ∷ (MIP.D Gm ⇐ MIP.D Hm) ∷ []) refl
              (~ ((cut⇐L≗ (Γ₀ ++ B ∷ []) ax ax (MIP.g Gm) refl)
                ∘ ⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = MIP.D Hm ∷ []}
                    {Λ = Λ₁} {A = MIP.D Hm} {B = MIP.D Gm}
                    refl (cutaxA-left (Γ₀ ++ B ∷ []) (MIP.g Gm) refl)))))
    eqh :
      cut [] (MIP.h lhs) t refl ≗ MIP.h rhs
    eqh rewrite cases++-inj₁ Ω [] [] (MIP.D Hm) =
      ⇐R
        ((⊗R refl
          (⇐L {Γ = []} {Δ = Ω ++ MIP.D Hm ∷ []} {Λ = []}
            {A = A'} {B = B'}
            (cutaxA-left Ω (MIP.g Hm) refl) refl))
        ∘ (~ (⇐L⊗R₂ {Γ = []} {Δ = Ω ++ MIP.D Hm ∷ []}
          {Λ = []} {Ω = E ∷ Ω'''} {A = A'} {B = B'}
          {A' = MIP.D Fm} {B' = MIP.D Gm})))
... | G ∷ Λ₀'
  rewrite cases++-inj₁ (Γ₀ ++ B ∷ G ∷ Λ₀') Ω (F ∷ Ω' ++ Λ₁)
            (B' ⇐ A') |
          cases++-inj₂ (G ∷ Λ₀') (Γ₀ ++ B ∷ []) Ω (B' ⇐ A') |
          ++?-inj₂ Ω Ω' Λ₁ F =
  intrp≗ (↝∷ (t , eqg , eqh) refl)
  where
    Fm = mip Ω'' (E ∷ Ω''') [] f refl
    Gm = mip (Γ₀ ++ B ∷ []) (G ∷ Λ₀' ++ B' ∷ []) Λ₁ g refl
    Hm = mip Ω (F ∷ Ω') [] f' refl
    lhs : MIP (Γ₀ ++ B ⇐ A ∷ Ω'')
          (E ∷ Ω''' ++ G ∷ Λ₀' ++ B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    lhs =
      ⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Ω''} {Δ₀ = E ∷ Ω'''}
        {Δ₁ = G ∷ Λ₀' ++ B' ⇐ A' ∷ Ω} {Λ = F ∷ Ω' ++ Λ₁}
        {A = A} {B = B}
        Fm
        (⇐L~⇐' {Γ = Γ₀ ++ B ∷ []} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
          {Λ₀ = G ∷ Λ₀'} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm Gm)
    rhs : MIP (Γ₀ ++ B ⇐ A ∷ Ω'')
          (E ∷ Ω''' ++ G ∷ Λ₀' ++ B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    rhs =
      ⇐L~⇐' {Γ = Γ₀ ++ B ⇐ A ∷ Ω''} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
        {Λ₀ = E ∷ Ω''' ++ G ∷ Λ₀'} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm
        (⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Ω''} {Δ₀ = E ∷ Ω'''}
          {Δ₁ = G ∷ Λ₀' ++ B' ∷ []} {Λ = Λ₁} {A = A} {B = B}
          Fm Gm)
    t : MIP.D Fm ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [] ⊢
        (MIP.D Fm ⊗ MIP.D Gm) ⇐ MIP.D Hm
    t = ⇐R (⊗L {Γ = []} {Δ = MIP.D Hm ∷ []}
      (⊗R (ax {A = MIP.D Fm})
        (⇐L {Γ = []} {Δ = MIP.D Hm ∷ []} {Λ = []}
          (ax {A = MIP.D Hm}) (ax {A = MIP.D Gm}))))
    eqg :
      MIP.g lhs ≗ cut (Γ₀ ++ B ⇐ A ∷ Ω'') t (MIP.g rhs) refl
    eqg
      rewrite cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Ω'') (F ∷ Ω' ++ Λ₁)
        ((MIP.D Fm ⊗ MIP.D Gm) ⇐ MIP.D Hm) |
        cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Ω'') Λ₁ (MIP.D Fm ⊗ MIP.D Gm) |
        cases++-inj₂ (MIP.D Fm ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [])
          (Γ₀ ++ B ⇐ A ∷ Ω'') Λ₁ (MIP.D Hm) |
        cases++-inj₂ (B ⇐ A ∷ Ω'' ++ MIP.D Fm ∷ []) Γ₀ Λ₁ (MIP.D Gm) |
        cases++-inj₂ [] (Ω'' ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Gm) |
        cases++-inj₂ (B ⇐ A ∷ Ω'') Γ₀
          (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁) (MIP.D Fm) |
        cases++-inj₁ Ω'' [] (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁)
          (MIP.D Fm) |
        cases++-inj₂
          (B ⇐ A ∷ Ω'' ++ MIP.D Fm ∷ MIP.D Gm ⇐ MIP.D Hm ∷ [])
          Γ₀ Λ₁ (MIP.D Hm) |
        cases++-inj₂ (MIP.D Gm ⇐ MIP.D Hm ∷ [])
          (Ω'' ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Hm) =
      ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Ω''}
        {Δ = F ∷ Ω' ++ Λ₁}
        (⇐L (~ (cutaxA-left Ω'' (MIP.g Fm) refl))
        (((⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = F ∷ Ω'} {Λ = Λ₁}
            {A = MIP.D Hm} {B = MIP.D Gm}
            (~ (cutaxA-right (MIP.h Hm))) refl)
          ∘ (~ (≡to≗ (cut⇐L-cases++₁ [] (Γ₀ ++ B ∷ [])))))
          ∘ cut-cong₂ (Γ₀ ++ B ∷ (MIP.D Gm ⇐ MIP.D Hm) ∷ []) refl
              (~ ((cut⇐L≗ (Γ₀ ++ B ∷ []) ax ax (MIP.g Gm) refl)
                ∘ ⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = MIP.D Hm ∷ []}
                    {Λ = Λ₁} {A = MIP.D Hm} {B = MIP.D Gm}
                    refl (cutaxA-left (Γ₀ ++ B ∷ []) (MIP.g Gm) refl)))))
    eqh :
      cut [] (MIP.h lhs) t refl ≗ MIP.h rhs
    eqh
      rewrite cases++-inj₂ (B' ⇐ A' ∷ Ω) Λ₀' [] (MIP.D Hm) |
              cases++-inj₁ Ω [] [] (MIP.D Hm) =
      ⇐R
        ((⊗R refl
          (⇐L {Γ = G ∷ Λ₀'} {Δ = Ω ++ MIP.D Hm ∷ []} {Λ = []}
            {A = A'} {B = B'}
            (cutaxA-left Ω (MIP.g Hm) refl) refl))
        ∘ (~ (⇐L⊗R₂ {Γ = G ∷ Λ₀'} {Δ = Ω ++ MIP.D Hm ∷ []}
          {Λ = []} {Ω = E ∷ Ω'''} {A = A'} {B = B'}
          {A' = MIP.D Fm} {B' = MIP.D Gm})))
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , eq1 , refl) | inj₂ (F , Ω' , refl , refl)  | inj₂ (Ω'' , eq2 , refl)  | inj₂ (Ω''' , eq3 , refl) 
  with cases++ Ω''' Λ₀ Δ (B' ⇐ A' ∷ Ω) eq3
mip≗⇐L⇐L-comm .(Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Ω''') (E ∷ Δ) .(F ∷ Ω' ++ Λ₁) {Γ₀} {Γ₁} {.(Ω ++ F ∷ Ω')} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f} {f'} {g} refl | inj₁ (Ω , eq1 , refl) | inj₂ (F , Ω' , refl , refl) | inj₂ (.(B ⇐ A ∷ Γ₁ ++ Ω''') , refl , refl) | inj₂ (Ω''' , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite eq1 |
          cases++-inj₁ Γ₀ (Γ₁ ++ Ω''' ++ E ∷ Ξ' ++ B' ⇐ A' ∷ Ω)
            (F ∷ Ω' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ξ') (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Ω''') Ω
            (B' ⇐ A') |
          cases++-inj₁ Γ₀ (Γ₁ ++ Ω''') (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω)
            (B ⇐ A) |
          ++?-inj₂ Ω Ω' Λ₁ F
  with Ω'''
... | [] rewrite ++?-inj₁ (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω) Γ₁
                    (F ∷ Ω' ++ Λ₁) |
                    ++?-inj₁ [] Γ₁ (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω) =
  intrp≗
    (~-trans (⇐L~⊗ refl inner~)
      (~-trans (↝∷ (t , eqg , eqh) refl)
        (~-sym (⇐L~⇐ refl outer~))))
  where
    Fm = mip Γ₁ [] [] f refl
    Gm = mip (Γ₀ ++ B ∷ []) (E ∷ Ξ' ++ B' ∷ []) Λ₁ g refl
    Hm = mip Ω (F ∷ Ω') [] f' refl
    inner~ :
      mip (Γ₀ ++ B ∷ []) (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω)
        (F ∷ Ω' ++ Λ₁)
        (⇐L {Γ = Γ₀ ++ B ∷ E ∷ Ξ'} {Δ = Ω ++ F ∷ Ω'}
          {Λ = Λ₁} {A = A'} {B = B'} f' g)
        refl
      ~ ⇐L~⇐' {Γ = Γ₀ ++ B ∷ []} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
          {Λ₀ = E ∷ Ξ'} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm Gm
    inner~
      rewrite cases++-inj₁ (Γ₀ ++ B ∷ E ∷ Ξ') Ω
                (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
              cases++-inj₂ (E ∷ Ξ') (Γ₀ ++ B ∷ []) Ω
                (B' ⇐ A') |
              ++?-inj₂ Ω Ω' Λ₁ F = refl
    outer~ :
      mip (Γ₀ ++ B ⇐ A ∷ Γ₁) (E ∷ Ξ' ++ B' ∷ []) Λ₁
        (⇐L {Γ = Γ₀} {Δ = Γ₁} {Λ = E ∷ Ξ' ++ B' ∷ Λ₁}
          {A = A} {B = B} f g)
        refl
      ~ ⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = []}
          {Δ₁ = E ∷ Ξ' ++ B' ∷ []} {Λ = Λ₁} {A = A} {B = B}
          Fm Gm
    outer~ = mip⇐L~⊗mid-base Γ₀ Γ₁ [] (E ∷ Ξ' ++ B' ∷ []) Λ₁
    lhs : MIP (Γ₀ ++ B ⇐ A ∷ Γ₁) (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    lhs =
      ⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = []}
        {Δ₁ = E ∷ Ξ' ++ B' ⇐ A' ∷ Ω} {Λ = F ∷ Ω' ++ Λ₁}
        {A = A} {B = B}
        Fm
        (⇐L~⇐' {Γ = Γ₀ ++ B ∷ []} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
          {Λ₀ = E ∷ Ξ'} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm Gm)
    rhs : MIP (Γ₀ ++ B ⇐ A ∷ Γ₁) (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    rhs =
      ⇐L~⇐' {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
        {Λ₀ = E ∷ Ξ'} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm
        (⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = []}
          {Δ₁ = E ∷ Ξ' ++ B' ∷ []} {Λ = Λ₁} {A = A} {B = B}
          Fm Gm)
    t : MIP.D Fm ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [] ⊢
        (MIP.D Fm ⊗ MIP.D Gm) ⇐ MIP.D Hm
    t = ⇐R (⊗L {Γ = []} {Δ = MIP.D Hm ∷ []}
      (⊗R (ax {A = MIP.D Fm})
        (⇐L {Γ = []} {Δ = MIP.D Hm ∷ []} {Λ = []}
          (ax {A = MIP.D Hm}) (ax {A = MIP.D Gm}))))
    eqg :
      MIP.g lhs ≗ cut (Γ₀ ++ B ⇐ A ∷ Γ₁) t (MIP.g rhs) refl
    eqg
      rewrite cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Γ₁) (F ∷ Ω' ++ Λ₁)
        ((MIP.D Fm ⊗ MIP.D Gm) ⇐ MIP.D Hm) |
        cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Γ₁) Λ₁ (MIP.D Fm ⊗ MIP.D Gm) |
        cases++-inj₂ (MIP.D Fm ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [])
          (Γ₀ ++ B ⇐ A ∷ Γ₁) Λ₁ (MIP.D Hm) |
        cases++-inj₂ (B ⇐ A ∷ Γ₁ ++ MIP.D Fm ∷ []) Γ₀ Λ₁ (MIP.D Gm) |
        cases++-inj₂ [] (Γ₁ ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Gm) |
        cases++-inj₂ (B ⇐ A ∷ Γ₁) Γ₀
          (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁) (MIP.D Fm) |
        cases++-inj₁ Γ₁ [] (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁)
          (MIP.D Fm) |
        cases++-inj₂
          (B ⇐ A ∷ Γ₁ ++ MIP.D Fm ∷ MIP.D Gm ⇐ MIP.D Hm ∷ [])
          Γ₀ Λ₁ (MIP.D Hm) |
        cases++-inj₂ (MIP.D Gm ⇐ MIP.D Hm ∷ [])
          (Γ₁ ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Hm) =
      ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁}
        {Δ = F ∷ Ω' ++ Λ₁}
        (⇐L (~ (cutaxA-left Γ₁ (MIP.g Fm) refl))
        (((⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = F ∷ Ω'} {Λ = Λ₁}
            {A = MIP.D Hm} {B = MIP.D Gm}
            (~ (cutaxA-right (MIP.h Hm))) refl)
          ∘ (~ (≡to≗ (cut⇐L-cases++₁ [] (Γ₀ ++ B ∷ [])))))
          ∘ cut-cong₂ (Γ₀ ++ B ∷ (MIP.D Gm ⇐ MIP.D Hm) ∷ []) refl
              (~ ((cut⇐L≗ (Γ₀ ++ B ∷ []) ax ax (MIP.g Gm) refl)
                ∘ ⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = MIP.D Hm ∷ []}
                    {Λ = Λ₁} {A = MIP.D Hm} {B = MIP.D Gm}
                    refl (cutaxA-left (Γ₀ ++ B ∷ []) (MIP.g Gm) refl)))))
    eqh :
      cut [] (MIP.h lhs) t refl ≗ MIP.h rhs
    eqh
      rewrite cases++-inj₂ (B' ⇐ A' ∷ Ω) Ξ' [] (MIP.D Hm) |
              cases++-inj₁ Ω [] [] (MIP.D Hm) =
      ⇐R
        ((⊗R refl
          (⇐L {Γ = E ∷ Ξ'} {Δ = Ω ++ MIP.D Hm ∷ []} {Λ = []}
            {A = A'} {B = B'}
            (cutaxA-left Ω (MIP.g Hm) refl) refl))
        ∘ (~ (⇐L⊗R₂ {Γ = E ∷ Ξ'} {Δ = Ω ++ MIP.D Hm ∷ []}
          {Λ = []} {Ω = []} {A = A'} {B = B'}
          {A' = MIP.D Fm} {B' = MIP.D Gm})))
... | H ∷ Ω'''' rewrite ++?-inj₁ (H ∷ Ω'''' ++ E ∷ Ξ' ++ B' ⇐ A' ∷ Ω) Γ₁
                                (F ∷ Ω' ++ Λ₁) |
                                ++?-inj₂ Γ₁ Ω'''' (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω) H =
  intrp≗
    (~-trans (⇐L~Γ inner~ refl)
      (~-trans
        (g~ (⇐L⇐L-comm {Γ = Γ₀} {Δ₀ = Γ₁} {Δ₁ = F ∷ Ω'}
              {Λ = H ∷ Ω''''} {Ξ = Λ₁} {A = A} {B = B}
              {A' = MIP.D Hm} {B' = MIP.D Gm}))
        (~-sym (⇐L~⇐ refl outer~))))
  where
    Gm = mip (Γ₀ ++ B ∷ H ∷ Ω'''') (E ∷ Ξ' ++ B' ∷ []) Λ₁ g refl
    Hm = mip Ω (F ∷ Ω') [] f' refl
    inner~ :
      mip (Γ₀ ++ B ∷ H ∷ Ω'''') (E ∷ Ξ' ++ B' ⇐ A' ∷ Ω)
        (F ∷ Ω' ++ Λ₁)
        (⇐L {Γ = Γ₀ ++ B ∷ H ∷ Ω'''' ++ E ∷ Ξ'}
          {Δ = Ω ++ F ∷ Ω'} {Λ = Λ₁} {A = A'} {B = B'} f' g)
        refl
      ~ ⇐L~⇐' {Γ = Γ₀ ++ B ∷ H ∷ Ω''''} {Δ₀ = Ω}
          {Δ₁ = F ∷ Ω'} {Λ₀ = E ∷ Ξ'} {Λ₁ = Λ₁}
          {A = A'} {B = B'} Hm Gm
    inner~
      rewrite cases++-inj₁ (Γ₀ ++ B ∷ H ∷ Ω'''' ++ E ∷ Ξ') Ω
                (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
              cases++-inj₂ (E ∷ Ξ') (Γ₀ ++ B ∷ H ∷ Ω'''') Ω
                (B' ⇐ A') |
              ++?-inj₂ Ω Ω' Λ₁ F = refl
    outer~ :
      mip (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ H ∷ Ω'''') (E ∷ Ξ' ++ B' ∷ [])
        Λ₁
        (⇐L {Γ = Γ₀} {Δ = Γ₁}
          {Λ = H ∷ Ω'''' ++ E ∷ Ξ' ++ B' ∷ Λ₁}
          {A = A} {B = B} f g)
        refl
      ~ ⇐L~Γ' {Γ₀ = Γ₀} {Γ₁ = H ∷ Ω''''}
          {Δ = E ∷ Ξ' ++ B' ∷ []} {Λ = Λ₁}
          {A = A} {B = B} Gm f
    outer~ = mip⇐L~Γ Γ₀ H Ω'''' (E ∷ Ξ' ++ B' ∷ []) Λ₁ {Ω = Γ₁}
mip≗⇐L⇐L-comm .(Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) (E ∷ Δ) .(F ∷ Ω' ++ Λ₁) {Γ₀} {Γ₁} {.(Ω ++ F ∷ Ω')} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f} {f'} {g} refl | inj₁ (Ω , eq1 , refl) | inj₂ (F , Ω' , refl , refl) | inj₂ (.(B ⇐ A ∷ Γ₁ ++ Λ₀) , refl , refl) | inj₂ (Λ₀ , refl , refl) | inj₂ ([] , refl , refl)
  rewrite eq1 |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ω)
            (F ∷ Ω' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀) (B' ⇐ A' ∷ Ω)
            (B ⇐ A) |
          cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) Ω
            (B' ⇐ A') |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Ω) Γ₁
            (F ∷ Ω' ++ Λ₁)
  with Λ₀
... | [] rewrite ++?-inj₁ [] Γ₁ (B' ⇐ A' ∷ Ω) |
                 ++?-inj₂ Ω Ω' Λ₁ F |
                 cases++-inj₁ (Γ₀ ++ B ∷ []) Ω
                   (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
                 cases++-inj₂ [] (Γ₀ ++ B ∷ []) Ω
                   (B' ⇐ A') |
                 ++?-inj₂ Ω Ω' Λ₁ F |
                 cases++-inj₁ Γ₀ (Γ₁ ++ B' ∷ []) Λ₁
                   (B ⇐ A) |
                 cases++-inj₁ Γ₀ Γ₁ (B' ∷ []) (B ⇐ A) |
                 ++?-inj₁ (B' ∷ []) Γ₁ Λ₁ |
                 ++?-inj₁ [] Γ₁ (B' ∷ []) =
  intrp≗ (↝∷ (t , eqg , eqh) refl)
  where
    Fm = mip Γ₁ [] [] f refl
    Gm = mip (Γ₀ ++ B ∷ []) (B' ∷ []) Λ₁ g refl
    Hm = mip Ω (F ∷ Ω') [] f' refl
    lhs : MIP (Γ₀ ++ B ⇐ A ∷ Γ₁) (B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    lhs =
      ⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = []}
        {Δ₁ = B' ⇐ A' ∷ Ω} {Λ = F ∷ Ω' ++ Λ₁}
        {A = A} {B = B}
        Fm
        (⇐L~⇐' {Γ = Γ₀ ++ B ∷ []} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
          {Λ₀ = []} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm Gm)
    rhs : MIP (Γ₀ ++ B ⇐ A ∷ Γ₁) (B' ⇐ A' ∷ Ω)
          (F ∷ Ω' ++ Λ₁) C
    rhs =
      ⇐L~⇐' {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁} {Δ₀ = Ω} {Δ₁ = F ∷ Ω'}
        {Λ₀ = []} {Λ₁ = Λ₁} {A = A'} {B = B'} Hm
        (⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = []}
          {Δ₁ = B' ∷ []} {Λ = Λ₁} {A = A} {B = B} Fm Gm)
    t : I ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [] ⊢
        (I ⊗ MIP.D Gm) ⇐ MIP.D Hm
    t = ⇐R (⊗L {Γ = []} {Δ = MIP.D Hm ∷ []}
      (⊗R (ax {A = I})
        (⇐L {Γ = []} {Δ = MIP.D Hm ∷ []} {Λ = []}
          (ax {A = MIP.D Hm}) (ax {A = MIP.D Gm}))))
    eqg :
      MIP.g lhs ≗ cut (Γ₀ ++ B ⇐ A ∷ Γ₁) t (MIP.g rhs) refl
    eqg
      rewrite cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Γ₁)
                (F ∷ Ω' ++ Λ₁) ((MIP.D Fm ⊗ MIP.D Gm) ⇐ MIP.D Hm) |
              cases++-inj₂ [] (Γ₀ ++ B ⇐ A ∷ Γ₁)
                Λ₁ (MIP.D Fm ⊗ MIP.D Gm) |
              cases++-inj₂ (MIP.D Fm ⊗ (MIP.D Gm ⇐ MIP.D Hm) ∷ [])
                (Γ₀ ++ B ⇐ A ∷ Γ₁) Λ₁ (MIP.D Hm) |
              cases++-inj₂ (B ⇐ A ∷ Γ₁ ++ MIP.D Fm ∷ [])
                Γ₀ Λ₁ (MIP.D Gm) |
              cases++-inj₂ [] (Γ₁ ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Gm) |
              cases++-inj₂ (B ⇐ A ∷ Γ₁) Γ₀
                (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁) (MIP.D Fm) |
              cases++-inj₁ Γ₁ [] (MIP.D Gm ⇐ MIP.D Hm ∷ MIP.D Hm ∷ Λ₁)
                (MIP.D Fm) |
              cases++-inj₂
                (B ⇐ A ∷ Γ₁ ++ MIP.D Fm ∷ MIP.D Gm ⇐ MIP.D Hm ∷ [])
                Γ₀ Λ₁ (MIP.D Hm) |
              cases++-inj₂ (MIP.D Gm ⇐ MIP.D Hm ∷ [])
                (Γ₁ ++ MIP.D Fm ∷ []) Λ₁ (MIP.D Hm) =
      ⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁}
        {Δ = F ∷ Ω' ++ Λ₁}
        (⇐L (~ (cutaxA-left Γ₁ (MIP.g Fm) refl))
        (((⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = F ∷ Ω'} {Λ = Λ₁}
            {A = MIP.D Hm} {B = MIP.D Gm}
            (~ (cutaxA-right (MIP.h Hm))) refl)
          ∘ (~ (≡to≗ (cut⇐L-cases++₁ [] (Γ₀ ++ B ∷ [])))))
          ∘ cut-cong₂ (Γ₀ ++ B ∷ (MIP.D Gm ⇐ MIP.D Hm) ∷ []) refl
              (~ ((cut⇐L≗ (Γ₀ ++ B ∷ []) ax ax (MIP.g Gm) refl)
                ∘ ⇐L {Γ = Γ₀ ++ B ∷ []} {Δ = MIP.D Hm ∷ []}
                    {Λ = Λ₁} {A = MIP.D Hm} {B = MIP.D Gm}
                    refl (cutaxA-left (Γ₀ ++ B ∷ []) (MIP.g Gm) refl)))))
    eqh :
      cut [] (MIP.h lhs) t refl ≗ MIP.h rhs
    eqh rewrite cases++-inj₁ Ω [] [] (MIP.D Hm) =
      ⇐R
        ((⊗R refl
          (⇐L {Γ = []} {Δ = Ω ++ MIP.D Hm ∷ []} {Λ = []}
            {A = A'} {B = B'}
            (cutaxA-left Ω (MIP.g Hm) refl) refl))
        ∘ (~ (⇐L⊗R₂ {Γ = []} {Δ = Ω ++ MIP.D Hm ∷ []}
          {Λ = []} {Ω = []} {A = A'} {B = B'}
          {A' = MIP.D Fm} {B' = MIP.D Gm})))
... | G ∷ Λ₀' rewrite ++?-inj₂ Γ₁ Λ₀' (B' ⇐ A' ∷ Ω) G |
                       ++?-inj₂ Ω Ω' Λ₁ F |
                       cases++-inj₁ (Γ₀ ++ B ∷ G ∷ Λ₀') Ω
                         (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
                       cases++-inj₂ [] (Γ₀ ++ B ∷ G ∷ Λ₀') Ω
                         (B' ⇐ A') |
                       ++?-inj₂ Ω Ω' Λ₁ F |
                       cases++-inj₁ Γ₀ (Γ₁ ++ G ∷ Λ₀' ++ B' ∷ []) Λ₁
                         (B ⇐ A) |
                       cases++-inj₁ Γ₀ (Γ₁ ++ G ∷ Λ₀') (B' ∷ [])
                         (B ⇐ A) |
                       ++?-inj₁ (G ∷ Λ₀' ++ B' ∷ []) Γ₁ Λ₁ |
                       ++?-inj₂ Γ₁ Λ₀' (B' ∷ []) G =
  intrp≗ (g~ (⇐L⇐L-comm {Γ = Γ₀} {Δ₀ = Γ₁} {Δ₁ = F ∷ Ω'}
                {Λ = G ∷ Λ₀'} {Ξ = Λ₁}))
mip≗⇐L⇐L-comm .(Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Ω''') (E ∷ Δ) .(F ∷ Ω' ++ Λ₁) {Γ₀} {Γ₁} {.(Ω ++ F ∷ Ω')} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f} {f'} {g} refl | inj₁ (Ω , eq1 , refl) | inj₂ (F , Ω' , refl , refl) | inj₂ (.(B ⇐ A ∷ Γ₁ ++ Ω''') , refl , refl) | inj₂ (Ω''' , refl , refl) | inj₂ (x ∷ Ξ' , refl , refl)
  rewrite eq1 |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ξ' ++ E ∷ Δ)
            (F ∷ Ω' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Ξ')
            (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Λ₀ ++ B' ⇐ A' ∷ Ξ' ++ E ∷ Δ) Γ₁
            (F ∷ Ω' ++ Λ₁) |
          cases++-inj₁ (Γ₀ ++ B ⇐ A ∷ Γ₁ ++ Λ₀) Ξ'
            (E ∷ Δ) (B' ⇐ A')
  with Λ₀
... | [] rewrite ++?-inj₂ Γ₁ Ξ' (E ∷ Δ) (B' ⇐ A') |
                 ++?-inj₂ (Ξ' ++ E ∷ Δ) Ω' Λ₁ F |
                 cases++-inj₁ (Γ₀ ++ B ∷ []) (Ξ' ++ E ∷ Δ)
                   (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
                 cases++-inj₁ (Γ₀ ++ B ∷ []) Ξ' (E ∷ Δ)
                   (B' ⇐ A') |
                 ++?-inj₂ (Ξ' ++ E ∷ Δ) Ω' Λ₁ F =
  let Hm = mip Ξ' (E ∷ Δ) (F ∷ Ω') f' refl in
  intrp≗ (g~ (⇐L⇐L-comm {Γ = Γ₀} {Δ₀ = Γ₁}
                {Δ₁ = Ξ' ++ MIP.D Hm ∷ F ∷ Ω'} {Λ = []} {Ξ = Λ₁}))
... | G ∷ Λ₀' rewrite ++?-inj₂ Γ₁ (Λ₀' ++ B' ⇐ A' ∷ Ξ')
                         (E ∷ Δ) G |
                       ++?-inj₂ (Ξ' ++ E ∷ Δ) Ω' Λ₁ F |
                       cases++-inj₁ (Γ₀ ++ B ∷ G ∷ Λ₀') (Ξ' ++ E ∷ Δ)
                         (F ∷ Ω' ++ Λ₁) (B' ⇐ A') |
                       cases++-inj₁ (Γ₀ ++ B ∷ G ∷ Λ₀') Ξ' (E ∷ Δ)
                         (B' ⇐ A') |
                       ++?-inj₂ (Ξ' ++ E ∷ Δ) Ω' Λ₁ F =
  let Hm = mip Ξ' (E ∷ Δ) (F ∷ Ω') f' refl in
  intrp≗ (g~ (⇐L⇐L-comm {Γ = Γ₀} {Δ₀ = Γ₁}
                {Δ₁ = Ξ' ++ MIP.D Hm ∷ F ∷ Ω'}
                {Λ = G ∷ Λ₀'} {Ξ = Λ₁}))
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (Ω , refl , eq2) 
  with cases++ Γ Γ₀ (Δ ++ Ω) (B ⇐ A ∷ Γ₁ ++ Λ₀) eq2
mip≗⇐L⇐L-comm Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (Ω , refl , eq2)  | inj₁ (Ω' , refl , eq4)
  with cases++ Ω' Δ (Γ₁ ++ Λ₀) Ω eq4
... | inj₁ (Ω'' , refl , eq6) 
  with ++? Ω'' Γ₁ Ω Λ₀ eq6
mip≗⇐L⇐L-comm Γ (E ∷ .(Ω' ++ B ⇐ A ∷ Ω'')) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {.(Γ ++ E ∷ Ω')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f} {f'} {g} refl | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω') (Γ₁ ++ Ξ')
            (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω') (Γ₁ ++ Ξ')
            (Ω ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω') Γ (Γ₁ ++ Ξ') (B ⇐ A) |
          ++?-inj₁ Ξ' Γ₁ (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) |
          ++?-inj₁ Ξ' Γ₁ (Ω ++ B' ∷ Λ₁) |
          cases++-inj₂ Ω (Γ ++ E ∷ Ω' ++ B ∷ Ξ')
            (Δ₀ ++ Λ₁) (B' ⇐ A') = intrp≗ refl
mip≗⇐L⇐L-comm Γ (E ∷ .(Ω' ++ B ⇐ A ∷ Ω'')) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {.(Γ ++ E ∷ Ω')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (F , Ξ' , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω') Ω''
            (F ∷ Ξ' ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω') Ω''
            (F ∷ Ξ' ++ Λ₀ ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω') Γ Ω'' (B ⇐ A) |
          ++?-inj₂ Ω'' Ξ' (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) F |
          ++?-inj₂ Ω'' Ξ' (Λ₀ ++ B' ∷ Λ₁) F |
          cases++-inj₂ Λ₀ (Γ ++ E ∷ Ω' ++ B ∷ [])
            (Δ₀ ++ Λ₁) (B' ⇐ A') = intrp≗ (g~ ⇐L⇐L-comm)
mip≗⇐L⇐L-comm Γ (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {.(Γ ++ E ∷ Ω')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₂ Ω'' (Γ ++ E ∷ Δ) (Γ₁ ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ Ω'' (Γ ++ E ∷ Δ) (Γ₁ ++ Λ₀ ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₂ (Ω'' ++ B ∷ Λ₀) (Γ ++ E ∷ Δ) (Δ₀ ++ Λ₁) (B' ⇐ A') = intrp≗ (g~ (⇐L⇐L-comm {Γ = Γ ++ _ ∷ Ω''} {Λ = Λ₀} {Ξ = Λ₁}))
mip≗⇐L⇐L-comm Γ (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (Ω , refl , eq2) | inj₂ ([] , eq3 , refl) 
  with ++? Δ Γ₁ Ω Λ₀ (inj∷ eq3 .proj₂)
mip≗⇐L⇐L-comm Γ (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {Γ} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (Ω , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω' , refl , refl)
  rewrite cases++-inj₁ Γ (Γ₁ ++ Ω')
            (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ (Γ₁ ++ Ω')
            (Ω ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ (Γ₁ ++ Ω') (B ⇐ A) |
          ++?-inj₁ Ω' Γ₁ (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) |
          ++?-inj₁ Ω' Γ₁ (Ω ++ B' ∷ Λ₁) |
          cases++-inj₂ Ω (Γ ++ B ∷ Ω') (Δ₀ ++ Λ₁)
            (B' ⇐ A') = intrp≗ refl
mip≗⇐L⇐L-comm Γ (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {Γ} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (Ω , refl , refl) | inj₂ ([] , refl , refl) | inj₂ (F , Ω' , refl , refl)
  rewrite cases++-inj₁ Γ Δ
            (F ∷ Ω' ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ Δ
            (F ∷ Ω' ++ Λ₀ ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ Δ (B ⇐ A) |
          ++?-inj₂ Δ Ω' (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) F |
          ++?-inj₂ Δ Ω' (Λ₀ ++ B' ∷ Λ₁) F |
          cases++-inj₂ Λ₀ (Γ ++ B ∷ []) (Δ₀ ++ Λ₁)
            (B' ⇐ A') = intrp≗ (g~ ⇐L⇐L-comm)
mip≗⇐L⇐L-comm Γ (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (Ω , refl , eq2) | inj₂ (x ∷ Ω' , eq3 , refl) 
  with cases++ Ω' Γ₁ (Δ ++ Ω) Λ₀ (inj∷ eq3 .proj₂)
... | inj₁ (Ω'' , refl , eq5) 
  with ++? Ω'' Δ Λ₀ Ω eq5
mip≗⇐L⇐L-comm .(Γ₀ ++ x ∷ Ω') (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {Γ₀} {.(Ω' ++ E ∷ Ω'')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (Ω , refl , refl) | inj₂ (x ∷ Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (Ξ' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Ω' ++ E ∷ Δ)
            (Ξ' ++ Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ (Ω' ++ E ∷ Δ)
            (Ξ' ++ Λ₀ ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ Ω' (E ∷ Δ) (B ⇐ A)
  with Ξ'
... | [] rewrite ++?-inj₁ [] (Ω' ++ E ∷ Δ)
                        (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) |
                      ++?-inj₁ [] (Ω' ++ E ∷ Δ)
                        (Λ₀ ++ B' ∷ Λ₁) |
                      ++?-inj₁ (E ∷ Δ) Ω' [] =
  intrp≗
    (g~
      (((⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Ω'}
          {Δ = Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁} {A = _} {B = I}
          (⇐L refl
            (IL⇐L-comm₁ {Γ = Γ₀ ++ B ∷ []} {Δ = Δ₀}
              {Λ = Λ₀} {Ω = Λ₁})))
        ∘
        (⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Ω'}
          {Δ = Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁} {A = _} {B = I}
          (⇐L⇐L-comm {Γ = Γ₀} {Δ₀ = Ω' ++ _ ∷ []}
            {Δ₁ = Δ₀} {Λ = I ∷ Λ₀} {Ξ = Λ₁})))
      ∘
      (⊗L⇐L-comm₁ {Γ = Γ₀ ++ B ⇐ A ∷ Ω'} {Δ = Δ₀}
        {Λ = Λ₀} {Ω = Λ₁} {A = A'} {B = B'} {A' = _} {B' = I})))
... | F ∷ Ξ'' rewrite
      ++?-inj₂ (Ω' ++ E ∷ Δ) Ξ''
        (Λ₀ ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) F |
      ++?-inj₂ (Ω' ++ E ∷ Δ) Ξ''
        (Λ₀ ++ B' ∷ Λ₁) F = intrp≗ (g~ ⇐L⇐L-comm)
mip≗⇐L⇐L-comm .(Γ₀ ++ x ∷ Ω') (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {Γ₀} {.(Ω' ++ E ∷ Ω'')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl | inj₂ (Ω , refl , refl) | inj₂ (x ∷ Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (F , Ξ' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Ω' ++ E ∷ Ω'' ++ F ∷ Ξ')
            (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ (Ω' ++ E ∷ Ω'' ++ F ∷ Ξ')
            (Ω ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ Ω' (E ∷ Ω'' ++ F ∷ Ξ') (B ⇐ A) |
          ++?-inj₁ (F ∷ Ξ') (Ω' ++ E ∷ Ω'')
            (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) |
          ++?-inj₁ (F ∷ Ξ') (Ω' ++ E ∷ Ω'')
            (Ω ++ B' ∷ Λ₁) |
          ++?-inj₁ (E ∷ Ω'') Ω' (F ∷ Ξ') |
          cases++-inj₂ Ω (Γ₀ ++ B ∷ F ∷ Ξ') (Δ₀ ++ Λ₁) (B' ⇐ A') = 
  let intrp D g h = mip Ω' (E ∷ Ω'') [] f refl
      intrp D'' g'' h'' = mip (Γ₀ ++ B ∷ []) (F ∷ Ξ') (Ω ++ B' ∷ Λ₁) f'' refl
  in intrp≗ (g~ (⊗L {Γ₀ ++ _ ∷ Ω'} ⇐L⇐L-comm ∘ (⊗L⇐L-comm₁ {Γ₀ ++ _ ∷ Ω'})))
mip≗⇐L⇐L-comm .(Γ₀ ++ x ∷ Ω') (E ∷ Δ) .(Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (Ω , refl , refl) | inj₂ (x ∷ Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₁ Γ₀ (Γ₁ ++ Ω'' ++ E ∷ Δ)
            (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ Ω'' ++ E ∷ Δ)
            (Ω ++ B' ∷ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₀ (Γ₁ ++ Ω'') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Ω'' ++ E ∷ Δ) Γ₁
            (Ω ++ B' ⇐ A' ∷ Δ₀ ++ Λ₁) |
          ++?-inj₁ (Ω'' ++ E ∷ Δ) Γ₁ (Ω ++ B' ∷ Λ₁)
  with Ω''
... | [] rewrite ++?-inj₁ [] Γ₁ (E ∷ Δ) |
                 cases++-inj₂ Ω (Γ₀ ++ B ∷ E ∷ Δ)
                   (Δ₀ ++ Λ₁) (B' ⇐ A') =
  intrp≗ (g~ (⊗L {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁} ⇐L⇐L-comm
    ∘ (⊗L⇐L-comm₁ {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁})))
... | F ∷ Ω''' rewrite ++?-inj₂ Γ₁ Ω''' (E ∷ Δ) F |
                         cases++-inj₂ Ω
                           (Γ₀ ++ B ∷ F ∷ Ω''' ++ E ∷ Δ)
                           (Δ₀ ++ Λ₁) (B' ⇐ A') =
  intrp≗ (g~ ⇐L⇐L-comm)
