{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.TensorLImpR where

open import IntrpWellDefCases.Base
open import Data.Sum

mip≗⊗L⇒R : ∀ Γ Δ Λ
  {Γ₁ Δ₁ : Cxt} {A B A' B' : Fma}
  {f : A' ∷ Γ₁ ++ A ∷ B ∷ Δ₁ ⊢ B'}
  → (eq : Γ₁ ++ A ⊗ B ∷ Δ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⇒ B')
      (mip Γ Δ Λ (⊗L (⇒R f)) eq)
      (mip Γ Δ Λ (⇒R (⊗L {_ ∷ _} f)) eq)
mip≗⊗L⇒R Γ Δ Λ {Γ₁} {Δ₁} eq with cases++ Γ₁ Γ Δ₁ (Δ ++ Λ) (sym eq)
mip≗⊗L⇒R Γ Δ Λ {Γ₁} {A = A} {B} {A'} {f = f} refl | inj₁ (Ω , refl , refl) 
  rewrite cases++-inj₁ Γ₁ Ω (Δ ++ Λ) (A ⊗ B) 
            = intrp≗ (↜∷ (ax , ((~ ⊗L⇒R) 
              ∘ (~ cutaxA-left (Γ₁ ++ A ⊗ B ∷ Ω) (⊗L (⇒R (MIP.g (mip (A' ∷ Γ₁ ++ A ∷ B ∷ Ω) Δ Λ f refl)))) refl)) , cutaxA-right _) refl)
... | inj₂ (Ω , eq₁ , refl) with cases++ Ω Δ Δ₁ Λ eq₁
mip≗⊗L⇒R Γ Δ Λ {A = A} {B} {A'} {f = f} refl | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) 
  rewrite cases++-inj₂ Ω Γ (Ω' ++ Λ) (A ⊗ B) |
          cases++-inj₁ Ω Ω' Λ (A ⊗ B) 
            = intrp≗ (↜∷ (ax , ⇒R (~ cutaxA-left (_ ∷ Γ) (MIP.g (mip (A' ∷ Γ) (Ω ++ A ∷ B ∷ Ω') Λ f refl)) refl) , cutaxA-right _) refl)
mip≗⊗L⇒R Γ Δ Λ {._} {Δ₁} {A} {B} {A'} {f = f} refl | inj₂ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) 
  rewrite cases++-inj₂ (Δ ++ Ω') Γ Δ₁ (A ⊗ B) |
          cases++-inj₂ Ω' Δ Δ₁ (A ⊗ B) 
            = intrp≗ (↜∷ (ax , ((~ ⊗L⇒R {Γ ++ _ ∷ Ω' }) 
              ∘ (~ cutaxA-left Γ (⊗L {Γ ++ _ ∷ Ω'} (⇒R (MIP.g (mip (A' ∷ Γ) Δ (Ω' ++ A ∷ B ∷ Δ₁) f refl)))) refl)) , cutaxA-right _) refl)
            -- alternative proof
            -- (↝∷ (ax , (⊗L⇒R {Γ ++ (MIP.D (mip (A' ∷ Γ) Δ (Ω' ++ A ∷ B ∷ Δ₁) f refl)) ∷ Ω' }
            --   ∘ ⇒R (~ cutaxA-left (A' ∷ Γ) (⊗L (MIP.g (mip (A' ∷ Γ) Δ (Ω' ++ A ∷ B ∷ Δ₁) f refl))) refl)) , cutaxA-right _) refl)
