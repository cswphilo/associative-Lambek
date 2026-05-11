{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module IntrpWellDefCases.ImpLImpLComm where

open import IntrpWellDefCases.Base
open import Data.Sum

mip≗⇒L⇒L-comm : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ Ξ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ⊢ A} {f' : Δ₁ ⊢ A'} {g : Γ₁ ++ B ∷ Λ₁ ++ B' ∷ Ξ ⊢ C}
  → (eq : Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⇒L f (⇒L {Γ₁ ++ B ∷ Λ₁} f' g)) eq)
      (mip Γ Δ Λ (⇒L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁} f' (⇒L f g)) eq)
mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} eq with ++? (Γ ++ Δ) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Λ (Δ₁ ++ A' ⇒ B' ∷ Ξ) eq
... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω Ξ Λ (sym eq₁)
mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} eq | inj₁ (Ω , refl , eq₂) | inj₁ (Ω₀ , refl , refl) with ++? (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Γ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) Δ eq₂
mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} {f = f} {f'} {g} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ ([] , refl , refl) 
  rewrite cases++-inj₂ Δ₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₀ (A' ⇒ B') |
          ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ₁ |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ (B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Λ₁) Λ |
          cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
          cases++-inj₂ Δ₁ (Γ₁ ++ B ∷ Λ₁) Ω₀ (A' ⇒ B') |
          ++?-inj₁ [] (Γ₁ ++ B ∷ Λ₁) Δ₁ 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , 
              -- (⇒L⇒L-comm 
              -- ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (⇒L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁} (MIP.h (mip [] [] Δ₁ f' refl))
              -- (⇒L f (MIP.g (mip (Γ₁ ++ B ∷ Λ₁) (B' ∷ Ω₀) Λ g refl)))) refl)) , 
              -- refl) refl)

... | inj₁ (E ∷ Ω₁ , refl , eq₄) with cases++ Γ (Γ₁ ++ Δ₀) Ω₁ (A ⇒ B ∷ Λ₁) eq₄
... | inj₁ (Ω₂ , eq₅ , refl) with cases++ Γ Γ₁ Ω₂ Δ₀ eq₅
mip≗⇒L⇒L-comm Γ ._ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ ._ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) 
  rewrite cases++-inj₂ (E ∷ Ω₃ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) Γ Ω₀ (A' ⇒ B') |
          ++?-inj₂ Γ (Ω₃ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) (Γ ++ E ∷ Ω₃) Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₃ ++ Δ₀) Γ (Λ₁ ++ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₂ Γ Ω₃ Δ₀ E |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₃) Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₃ ++ Δ₀) Γ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₂ Γ Ω₃ Δ₀ E |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₃ ++ B ∷ Λ₁) Λ |
          cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') | 
          cases++-inj₂ (E ∷ Ω₃ ++ B ∷ Λ₁ ++ Δ₁) Γ Ω₀ (A' ⇒ B') |
          ++?-inj₂ Γ (Ω₃ ++ B ∷ Λ₁) Δ₁ E = intrp≗ (↝∷ (ax , (~ cutaxA-left Γ _ refl) , ⇒L⇒L-comm) refl)
  
mip≗⇒L⇒L-comm Γ ._ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ ._ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) 
  rewrite cases++-inj₂ (E ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (Γ₁ ++ Ω₃) Ω₀ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Ω₃) (Ω₂ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
          ++?-inj₁ (Ω₃ ++ E ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) Γ₁ Λ  |
          cases++-inj₁ (Ω₃ ++ E ∷ Ω₂) (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₂) (Γ₁ ++ Ω₃) (Λ₁ ++ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ Ω₃ Γ₁ (E ∷ Ω₂) |
          ++?-inj₁ (Ω₃ ++ E ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ (Ω₃ ++ E ∷ Ω₂) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₂) (Γ₁ ++ Ω₃) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ Ω₃ Γ₁ (E ∷ Ω₂) |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Λ₁) Λ |
          cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
          cases++-inj₂ (B ∷ Λ₁ ++ Δ₁) Γ₁ Ω₀ (A' ⇒ B') |
          ++?-inj₂ Γ₁ Λ₁ Δ₁ B 
            = intrp≗ (h~ (⇒R ⇒L⇒L-comm ∘ (~ ⇒L⇒R)))
            -- intrp≗ (↝∷ (ax , (~ cutaxA-left (Γ₁ ++ Ω₃) _ refl) , (⇒R ⇒L⇒L-comm ∘ (~ ⇒L⇒R))) refl)
mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} {f = f} {f'} {g} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ Ω₁ , refl , refl) | inj₂ ([] , refl , refl) 
  rewrite cases++-inj₂ (A ⇒ B ∷ Λ₁ ++ Δ₁) (Γ₁ ++ Δ₀) Ω₀ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Δ₀) Ω₁ Δ₁ (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Ω₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₂ [] (Γ₁ ++ Δ₀) (Ω₁ ++ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ Δ₀ Γ₁ [] |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₂ [] (Γ₁ ++ Δ₀) (Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ Δ₀ Γ₁ [] |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Ω₁) Λ |
          cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
          cases++-inj₂ (B ∷ Ω₁ ++ Δ₁) Γ₁ Ω₀ (A' ⇒ B') |
          ++?-inj₂ Γ₁ Ω₁ Δ₁ B 
            = intrp≗ (h~ (⇒R ⇒L⇒L-comm ∘ (~ ⇒L⇒R)))
            --  intrp≗ (↝∷ (ax , (~ cutaxA-left (Γ₁ ++ Δ₀) (⇒L (MIP.h (mip [] Δ₀ [] f refl))
        -- (MIP.g (mip Γ₁ (B ∷ Ω₁ ++ B' ∷ Ω₀) Λ g refl))) refl) , (⇒R ⇒L⇒L-comm ∘ (~ ⇒L⇒R))) refl) 

            -- intrp≗ (↝∷ (ax , 
            --   (((⇒L (~ cutaxA-right _) (~ cutaxA-left Γ₁ _ refl) 
            --   ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
            --   ∘ (~ cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ ax ax (MIP.g (mip Γ₁ (B ∷ Ω₁ ++ B' ∷ Ω₀) Λ g refl)) refl))) 
            --   ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ Δ₀)))) , 
            --   (⇒R (cutaxA-left [] (cut [] (⇒L (MIP.g (mip [] Δ₀ [] f refl)) (⇒L f' (MIP.h (mip Γ₁ (B ∷ Ω₁ ++ B' ∷ Ω₀) Λ g refl)))) ax refl) refl 
            --   ∘ (cutaxA-right _ 
            --   ∘ ⇒L⇒L-comm)) 
            --   ∘ (~ ⇒L⇒R)))
            --    refl)

mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ Ω₁ , refl , refl) | inj₂ (E₁ ∷ Ω₂ , refl , refl) 
  rewrite cases++-inj₂ (E ∷ Ω₁ ++ Δ₁) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₂) Ω₀ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₂) Ω₁ Δ₁ E |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₂ ++ E ∷ Ω₁ ++ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Ω₂ ++ E ∷ Ω₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₂ (E ∷ Ω₁ ++ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₂ ++ E ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Ω₂ ++ E ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₂ (E ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Ω₂ ++ E ∷ Ω₁) Λ |
          cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
          cases++-inj₂ (E ∷ Ω₁ ++ Δ₁) (Γ₁ ++ B ∷ Ω₂) Ω₀ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ B ∷ Ω₂) Ω₁ Δ₁ E 
            = intrp≗ refl
            -- intrp≗ (↝∷ (ax , (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₂) _ refl) , cutaxA-right _) refl)
          -- intrp context is in Γ ++ B ∷ Λ ++ B' ∷ Ξ ⊢ C and does not split Δ₀ nor Δ₁.

mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} eq | inj₁ (Ω , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , eq₄) with cases++ Δ₁ (E ∷ Ω₁) Ω₀ Δ (sym eq₄)
mip≗⇒L⇒L-comm ._ Δ Λ {Γ₁} {Δ₀} {[]} {Λ₁} {._} {A = A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₁ Δ (A' ⇒ B') |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ A' ⇒ B' ∷ Ω₁ ++ Δ) Γ₁ Λ |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₁ ++ Δ) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₁ ++ Δ) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ B' ∷ Ω₁) Δ (A ⇒ B) |
          cases++-inj₁ Δ₀ (Λ₁ ++ A' ⇒ B' ∷ Ω₁ ++ Δ) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ A' ⇒ B' ∷ Ω₁) Δ (A ⇒ B) |
          ++?-inj₁ (A' ⇒ B' ∷ Ω₁ ++ Δ) (Γ₁ ++ B ∷ Λ₁) Λ |
          cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Ω₁ Δ (A' ⇒ B') 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ A' ⇒ B' ∷ Ω₁) _ refl)) , refl) refl)
mip≗⇒L⇒L-comm ._ Δ Λ {Γ₁} {Δ₀} {E ∷ Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
  rewrite cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Δ₁) Ω₂ Δ (A' ⇒ B') |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₂ ++ Δ) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₂ ++ Δ) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ B' ∷ Ω₂) Δ (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂) Δ (A ⇒ B) |
          ++?-inj₁ (E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) (Γ₁ ++ B ∷ Λ₁) Λ |
          cases++-inj₁ Δ₁ (Ω₂ ++ Δ) Λ (A' ⇒ B') |
          cases++-inj₁ (Γ₁ ++ B ∷ Λ₁ ++ E ∷ Δ₁) Ω₂ Δ (A' ⇒ B') 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂) _ refl)) , refl) refl)

mip≗⇒L⇒L-comm ._ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) 
  rewrite cases++-inj₂ Ω₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₁) Ω₀ (A' ⇒ B') |
          ++?-inj₁ (E ∷ Ω₁) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₂ |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ (B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₁ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
          cases++-inj₁ Δ₀ (Λ₁ ++ E ∷ Ω₁ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ E ∷ Ω₁) (Ω₂ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₁ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Λ₁) Λ |
          cases++-inj₁ (Ω₁ ++ Ω₂) Ω₀ Λ (A' ⇒ B') |
          cases++-inj₂ Ω₂ (Γ₁ ++ B ∷ Λ₁ ++ E ∷ Ω₁) Ω₀ (A' ⇒ B') |
          ++?-inj₁ (E ∷ Ω₁) (Γ₁ ++ B ∷ Λ₁) Ω₂ 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₁) _ refl)) , refl) refl)

mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} eq | inj₁ (Ω , refl , eq₂) | inj₂ (Ω₀ , refl , refl) with cases++ (Γ₁ ++ Δ₀) Γ (Λ₁ ++ Ω) Δ eq₂
... | inj₁ (Ω₁ , refl , eq₄) with  ++? Ω₁ Λ₁ Δ Ω eq₄
mip≗⇒L⇒L-comm ._ Δ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ ([] , refl , refl) 
  rewrite ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ (B' ∷ Ξ) |
          cases++-inj₁ Δ₀ Ω₁ (B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ [] (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Ω) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ (Ω₁ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ Ω (A ⇒ B) |
          ++?-inj₁ Ω (Γ₁ ++ B ∷ Ω₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
          ++?-inj₁ [] (Γ₁ ++ B ∷ Ω₁) Ω 
            = intrp≗ (g~ ((~ ⊗L⇒L-comm₂) ∘ ⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁} ⇒L⇒L-comm))
            -- intrp≗ (↝∷ (ax , 
              -- (((~ ⊗L⇒L-comm₂) ∘ ⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁} ⇒L⇒L-comm) ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) _ refl)) , 
              -- refl) refl)
mip≗⇒L⇒L-comm ._ Δ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (E ∷ Ω₂ , refl , refl) 
  rewrite ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₂ Δ E |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₂ ++ Δ) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ (Λ₁ ++ E ∷ Ω₂ ++ Δ) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ E ∷ Ω₂) Δ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₂ ++ Δ) (Γ₁ ++ B ∷ Λ₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ Ω₀ (Ω₂ ++ Δ) Ξ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ B ∷ Λ₁) Ω₂ Δ E 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₂) _ refl)) , refl) refl)
mip≗⇒L⇒L-comm ._ Δ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (E ∷ Ω₂) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) Ω |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ E ∷ Ω₂) Γ₁ (B' ∷ Ξ) |
          cases++-inj₁ Δ₀ (Ω₁ ++ E ∷ Ω₂) (B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ (E ∷ Ω₂) (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ E ∷ Ω₂ ++ Ω) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ (Ω₁ ++ E ∷ Ω₂ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ (E ∷ Ω₂ ++ Ω) (A ⇒ B) |
          ++?-inj₁ Ω (Γ₁ ++ B ∷ Ω₁ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
          ++?-inj₁ (E ∷ Ω₂) (Γ₁ ++ B ∷ Ω₁) Ω 
            = intrp≗ (g~ ((~ ⊗L⇒L-comm₂) ∘ ⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁} ⇒L⇒L-comm))
            -- intrp≗ (↝∷ (ax , 
            --   (((~ ⊗L⇒L-comm₂) ∘ ⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁} ⇒L⇒L-comm) ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) _ refl)) , 
            --   refl) refl)
mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} eq | inj₁ (Ω , refl , eq₂) | inj₂ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , eq₄) with ++? Γ Γ₁ Ω₁ Δ₀ eq₄
mip≗⇒L⇒L-comm Γ ._ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) (Γ₁ ++ Ω₂) Ω |
          ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Λ₁) Γ₁ (B' ∷ Ξ) |
          cases++-inj₁ (Ω₂ ++ Ω₁) Λ₁ (B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) Λ₁ (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ₁ Ω₁ |
          ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Λ₁ ++ Ω) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ (Ω₂ ++ Ω₁) (Λ₁ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) (Λ₁ ++ Ω) (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ₁ Ω₁ |
          ++?-inj₁ Ω (Γ₁ ++ B ∷ Λ₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
          ++?-inj₁ (B ∷ Λ₁) Γ₁ Ω 
            = intrp≗ (↜∷ (⇒R ((⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))) , 
              (((⊗L {Γ₁ ++ Ω₂} (((~ ⇒L⇒L-comm) 
              ∘ ⇒L refl (((~ cutaxA-left (Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []) (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))) refl) 
              ∘ (~ cutaxA-left Γ₁ (cut (Γ₁ ++ _ ∷ []) ax (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))) refl) refl)) ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) {f = ax} {ax}))) 
              ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) ∘ ≡to≗ (cut⊗L-cases++₂ Γ₁ [] (Ω₀ ++ A' ⇒ B' ∷ Ξ))) 
              ∘ (~ cut-cong₂ Γ₁ refl (cut⊗L≗ Γ₁ (_ ∷ []) [] (⇒L {[]} ax (⊗R ax ax)) (⊗L (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))) refl 
              ∘ ⊗L {Γ₁ ++ _ ∷ []} (cut⇒L≗ Γ₁ ax (⊗R ax ax) (⊗L (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))) refl))))
              ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) Ω₂)))) , 
              ⇒R ((~ ⇒L⊗R₁) ∘ ⇒L (cutaxA-left [] _ refl) refl)) refl) 
-- critical case, where the interpolant formula is
-- (D ⇒ F) ⊗ E ⊢ D ⇒ (F ⊗ E)

--  (MIP.D (mip [] Ω₂ Ω₁ f refl) ⇒
--        MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))
--       ⊗ MIP.D (mip [] Ω Ω₀ f' refl)

mip≗⇒L⇒L-comm Γ ._ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (E ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Γ Ω |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁) (Γ ++ E ∷ Ω₂) (B' ∷ Ξ) |
          cases++-inj₁ Δ₀ Λ₁ (B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ Ω₂ Δ₀ E |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω) (Γ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ (Λ₁ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ (Λ₁ ++ Ω) (A ⇒ B) |
          ++?-inj₂ Γ Ω₂ Δ₀ E |
          ++?-inj₁ Ω (Γ ++ E ∷ Ω₂ ++ B ∷ Λ₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
          ++?-inj₁ (E ∷ Ω₂ ++ B ∷ Λ₁) Γ Ω 
            = intrp≗ (h~ ⇒L⊗R₁)
            -- intrp≗ (↝∷ (ax , (~ cutaxA-left Γ _ refl) , ⇒L⊗R₁) refl)
mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} eq | inj₂ (E , Ω , eq₁ , refl) with cases++ (Γ₁ ++ Δ₀) (Γ ++ Δ) Λ₁ (E ∷ Ω) (sym eq₁)
... | inj₁ (Ω₀ , eq₂ , refl) with cases++ (Γ₁ ++ Δ₀) Γ Ω₀ Δ eq₂
mip≗⇒L⇒L-comm Γ Δ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) 
  rewrite ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ (Ω₁ ++ Δ) (E ∷ Ω ++ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ Δ (A ⇒ B) |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ (Ω₁ ++ Δ) (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ Δ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ B ∷ Ω₁ ++ Δ) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) E 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) _ refl)) , refl) refl)
          
... | inj₂ (Ω₁ , refl , eq₄) with ++? Γ Γ₁ Ω₁ Δ₀ eq₄
mip≗⇒L⇒L-comm Γ ._ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g} refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Ω₀) Γ₁ (E ∷ Ω ++ B' ∷ Ξ) |
          cases++-inj₁ (Ω₂ ++ Ω₁) Ω₀ (E ∷ Ω ++ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) Ω₀ (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ₁ Ω₁ |
          ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Ω₀) Γ₁ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ (Ω₂ ++ Ω₁) Ω₀ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) Ω₀ (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ₁ Ω₁ |
          ++?-inj₂ (Γ₁ ++ B ∷ Ω₀) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) E 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Ω₂) _ refl)) , refl) refl)
            
            -- intrp≗ (↝∷ (ax , 
            --   {!  cut⇒R⇒Lcases++   !} , 
            --   ⇒R (cutaxA-left [] (cut [] (⇒L {[]} (MIP.g (mip [] Ω₂ Ω₁ f refl)) (MIP.h (mip Γ₁ (B ∷ Ω₀) (E ∷ Ω ++ B' ∷ Ξ) g refl))) ax refl) refl 
            --   ∘ (cutaxA-right _))) refl)

mip≗⇒L⇒L-comm Γ ._ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f' = f'} {g} refl | inj₂ (E₁ , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₀) (Γ ++ E ∷ Ω₂) (E₁ ∷ Ω ++ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ Ω₀ (E₁ ∷ Ω ++ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ Ω₀ (A ⇒ B) |
          ++?-inj₂ Γ Ω₂ Δ₀ E |
          ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₀) (Γ ++ E ∷ Ω₂) (E₁ ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₁ Δ₀ Ω₀ (E₁ ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ Ω₀ (A ⇒ B) |
          ++?-inj₂ Γ Ω₂ Δ₀ E |
          ++?-inj₂ (Γ ++ E ∷ Ω₂ ++ B ∷ Ω₀) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) E₁ 
            = intrp≗ refl
            -- intrp≗ (↝∷ (ax , (~ cutaxA-left Γ (⇒L {Γ ++ _ ∷ E₁ ∷ Ω} f' (MIP.g (mip Γ (E ∷ Ω₂ ++ B ∷ Ω₀) (E₁ ∷ Ω ++ B' ∷ Ξ) g refl))) refl) , cutaxA-right _) refl)

mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} eq | inj₂ (E , Ω , eq₁ , refl) | inj₂ (Ω₀ , eq₂ , eq₃) with ++? (Γ ++ Δ) Γ₁ Ω₀ Δ₀ eq₃
... | inj₁ (Ω₁ , refl , eq₅) with ++? Γ₁ Γ Ω₁ Δ eq₅
mip≗⇒L⇒L-comm Γ Δ ._ {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g} refl | inj₂ (E , Ω , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
  rewrite ++?-inj₁ Ω₁ (Γ ++ Ω₂) (A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
          ++?-inj₁ Ω₁ (Γ ++ Ω₂) (A ⇒ B ∷ Ω ++ B' ∷ Ξ) |
          cases++-inj₂ [] Ω₁ (Ω ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ Ω₁ |
          cases++-inj₂ [] Ω₁ (Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ Ω₁ |
          ++?-inj₂ (Γ ++ Ω₂) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) B 
            = intrp≗ (g~ (⊗L ⇒L⇒L-comm ∘ ⊗L⇒L-comm₁))
            -- intrp≗ (↝∷ (ax , (⊗L ⇒L⇒L-comm ∘ ⊗L⇒L-comm₁) ∘ (~ cutaxA-left Γ _ refl) , refl) refl)
            
            -- intrp≗ (↝∷ (ax , 
            --   (⊗L ((⇒L⇒L-comm ∘ ⇒L refl (((~ cutaxA-left (Γ ++ MIP.D (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl) ∷ []) _ refl) 
            --   ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl) ∷ []) ax (⇒L {Γ ++ _ ∷ []} (MIP.g (mip [] Ω₁ [] f refl)) (MIP.g (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl))) refl) refl)) 
            --   ∘ (≡to≗ (cut⊗R⊗Lcases++ Γ (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) 
            --     {f = ax} {ax} {(⇒L {Γ ++ _ ∷ []} (MIP.g (mip [] Ω₁ [] f refl)) (MIP.g (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl)))})))) 
            --   ∘ (~ (≡to≗ (cut⇒L-cases++-comm₂ Γ (A ⇒ B ∷ Λ₁))))) 
            --   ∘ (~ cut⊗L≗ Γ [] [] (⊗R ax ax) 
            --     (⇒L {Γ ++ _ ∷ A ⇒ B ∷ Λ₁} f' (⊗L (⇒L {Γ ++ _ ∷ []} (MIP.g (mip [] Ω₁ [] f refl)) (MIP.g (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl))))) refl)) , 
            --   ⊗R (cutaxA-right _) (cutaxA-right _)) refl)

mip≗⇒L⇒L-comm Γ Δ ._ {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g} refl | inj₂ (E , Ω , refl , refl) | inj₂ (F ∷ Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
  rewrite ++?-inj₁ Ω₁ (Γ ++ Ω₂) (F ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) |
          cases++-inj₂ (F ∷ Ω₀) Ω₁ (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ Ω₁ |
          ++?-inj₁ Ω₁ (Γ ++ Ω₂) (F ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ (F ∷ Ω₀) Ω₁ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Γ Ω₁ |
          ++?-inj₂ (Γ ++ Ω₂) Λ₁ (Δ₁ ++ A' ⇒ B' ∷ Ξ) B
            = intrp≗ (g~ (⊗L ⇒L⇒L-comm ∘ ⊗L⇒L-comm₁))
            -- intrp≗ (↝∷ (ax , (⊗L ⇒L⇒L-comm ∘ ⊗L⇒L-comm₁) ∘ (~ cutaxA-left Γ _ refl) , refl) refl)
            
mip≗⇒L⇒L-comm Γ Δ ._  {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₂ (E₁ , Λ₁ , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) |
          cases++-inj₂ [] (Ω₂ ++ Δ) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₂ Γ₁ Ω₂ Δ E | 
          ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ [] (Ω₂ ++ Δ) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₂ Γ₁ Ω₂ Δ E 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ E ∷ Ω₂) _ refl)) , cutaxA-right _) refl)
          -- intrp context in f : E ∷ Ω₂ ++ Δ ⊢ A 

mip≗⇒L⇒L-comm Γ Δ ._ {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₂ (E₀ , Ω , refl , refl) | inj₂ (E₁ ∷ Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (E₁ ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) |
          cases++-inj₂ (E₁ ∷ Ω₀) (Ω₂ ++ Δ) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₂ Γ₁ Ω₂ Δ E |
          ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (E₁ ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
          cases++-inj₂ (E₁ ∷ Ω₀) (Ω₂ ++ Δ) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₂ Γ₁ Ω₂ Δ E 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ E ∷ Ω₂) _ refl)) , cutaxA-right _) refl)
  --         -- same as the case above, not yet know if this can be optimized. 
  --         -- We need another with function if we don't pattern-match on Ω₀

mip≗⇒L⇒L-comm Γ Δ ._ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} refl | inj₂ (E₁ , Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) 
  rewrite ++?-inj₂ (Γ ++ Δ) Ω₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          ++?-inj₂ (Γ ++ Δ) Ω₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) E |
          ++?-inj₂ (Γ ++ Δ) (Ω₁ ++ B ∷ Λ₁) (Δ₁ ++ A' ⇒ B' ∷ Ξ) E 
            = intrp≗ (g~ ⇒L⇒L-comm)
            -- intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left Γ _ refl))  , cutaxA-right _) refl)
            -- intrp context in g : Γ ++ Δ ++ E ∷ Ω₁ ++ B ∷ Λ₁ ++ B' ∷ Ξ ⊢ C, where its Γ splits
 