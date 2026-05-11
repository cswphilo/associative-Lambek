{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLImpLAssoc where

open import IntrpWellDefCases.Base
open import Data.Sum
-- open import Data.Product using (_,_)
-- open import Utilities

-- In princiapl 15 cases. The additionbal cases come from addtional pattern-matching to use the helper function ++?-injᵢ correctly.
mip≗⇒L⇒L-assoc : ∀ Γ Δ Λ
  {Γ₀ Γ₁ Δ₀ Λ₀ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ⊢ A'} {g : Γ₀ ++ B' ∷ Λ₀ ⊢ A} {h : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⇒L {Γ₁ ++ Γ₀} f (⇒L g h)) eq)
      (mip Γ Δ Λ (⇒L (⇒L f g) h) eq)
mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq with ++? (Γ ++ Δ) (Γ₁ ++ Γ₀) Λ (Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω (Λ₀ ++ A ⇒ B ∷ Λ₁) Λ (sym eq₁)
... | inj₁ (Ω₀ , refl , eq₄) with cases++ Λ₀ Ω₀ Λ₁ Λ (sym eq₄)
mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) with cases++ (Γ₁ ++ Γ₀ ++ Δ₁) Γ (Λ₀ ++ A ⇒ B ∷ Ω₁) Δ eq₂
... | inj₁ (Ω₂ , refl , eq₄) with cases++ Λ₀ Ω₂ Ω₁ Δ (sym eq₄)
mip≗⇒L⇒L-assoc ._ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₃ ++ Δ) Γ₁ Λ |
  --         cases++-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) (Ω₃ ++ Δ) Λ (A ⇒ B) |
  --         cases++-inj₁ (Γ₁ ++ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Ω₃ Δ (A ⇒ B) |
  --         ++?-inj₁ (Γ₀ ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₃ ++ Δ) Γ₁ Λ |
  --         cases++-inj₁ (Γ₀ ++ B' ∷ Λ₀) (Ω₃ ++ Δ) Λ (A ⇒ B) |
  --         cases++-inj₁ (Γ₁ ++ Γ₀ ++ B' ∷ Λ₀) Ω₃ Δ (A ⇒ B)
  --           = intrp≗ (g~ ⇒L⇒L-assoc)

mip≗⇒L⇒L-assoc ._ Δ Λ {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) 
  rewrite ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Ω₃ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
          cases++-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Ω₃) Ω₁ Λ (A ⇒ B) |
          cases++-inj₂ Ω₃ (Γ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) Ω₁ (A ⇒ B) |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₂) Γ₁ Ω₃ |
          cases++-inj₁ Δ₁ Ω₂ Ω₃ (A' ⇒ B') |
          ++?-inj₁ (B' ∷ Ω₂ ++ Ω₃ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
          cases++-inj₁ (Ω₂ ++ Ω₃) Ω₁ Λ (A ⇒ B) |
          cases++-inj₂ Ω₃ (Γ₁ ++ B' ∷ Ω₂) Ω₁ (A ⇒ B) |
          ++?-inj₁ (B' ∷ Ω₂) Γ₁ Ω₃ 
            = intrp≗ {!   !}
  --         -- The interpolant context for the first premise f is empty, for the interpolant formula, it adds a dummy unit I.
  --         -- The shape of the proof will be exactly the same as the one below.
  --         -- This case arises due to ++-injᵢ cannot handle ++? [] Γ₀ (Γ₀ ++ Δ₁) Δ₁ refl
  --         -- The interpolant context is Δ  = Ω₃ ++ A ⇒ B ∷ Ω₁, which has nothing to do with f.
mip≗⇒L⇒L-assoc ._ Δ Λ {E ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (E ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Ω₃ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |  
  --         cases++-inj₁ (E ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Ω₃) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ Ω₃ (Γ₁ ++ E ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂)  Ω₁ (A ⇒ B) |
  --         ++?-inj₁ (E ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) Γ₁ Ω₃ |
  --         ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₂) (E ∷ Γ₀) Ω₃ |
  --         cases++-inj₁ Δ₁ Ω₂ Ω₃ (A' ⇒ B') |
  --         ++?-inj₁ (E ∷ Γ₀ ++ B' ∷ Ω₂ ++ Ω₃ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁ (Γ₀ ++ B' ∷ Ω₂ ++ Ω₃) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ Ω₃ (Γ₁ ++ E ∷ Γ₀ ++ B' ∷ Ω₂) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ (E ∷ Γ₀ ++ B' ∷ Ω₂) Γ₁ Ω₃ 
  --           = intrp≗ (g~ ⇒L⇒L-assoc)

mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) with ++? Γ (Γ₁ ++ Γ₀) Ω₂ Δ₁ eq₄
mip≗⇒L⇒L-assoc Γ ._ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (Γ₀ ++ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁ (Γ₀ ++ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (Ω₂ ++ A' ⇒ B' ∷ Λ₀) (Γ₁ ++ Γ₀ ++ Ω₃) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ (Γ₀ ++ Ω₃) Γ₁ (Ω₂ ++ A' ⇒ B' ∷ Λ₀) |
  --         ++?-inj₁ Ω₃ Γ₀ (Ω₂ ++ A' ⇒ B' ∷ Λ₀) |
  --         cases++-inj₂ Ω₂ Ω₃ Λ₀ (A' ⇒ B') |
  --         ++?-inj₁ (Γ₀ ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁ (Γ₀ ++ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (B' ∷ Λ₀) (Γ₁ ++ Γ₀) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ Γ₀ Γ₁ (B' ∷ Λ₀) 
  --           = intrp≗ (↜∷ (⇒R (⇒R (⇒L {[]} (⊗R ax ax) ax)) , 
  --             (((⇒L (≡to≗ (cut⊗Rcases++₂ [] [] Γ₀)) (~ cutaxA-left Γ₁ _ refl) 
  --             ∘ (~ (≡to≗ (cut⇒L-cases++-assoc Γ₀ Γ₁)))) 
  --             ∘ cut-cong₂ (Γ₁ ++ Γ₀) {g' = (cut (Γ₁ ++ Γ₀) (⇒R (⇒L {[]} (⊗R ax ax) ax))
  --                   (⇒L (MIP.h (mip [] Γ₀ (B' ∷ Λ₀) g refl))
  --                 (MIP.g (mip Γ₁ (B ∷ Ω₁) Λ h refl))) refl)} refl ((~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁))) 
  --             ∘ (cut-cong₂ Γ₁ refl (~ cut⇒L≗ Γ₁ (⊗R ax ax) ax (MIP.g (mip Γ₁ (B ∷ Ω₁) Λ h refl)) refl) 
  --             ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ Γ₀)))))) -- ≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ Γ₀)
  --             ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ (Γ₁ ++ Γ₀) Λ Ω₃))) , 
  --             ⇒R (⇒R ((~ ⇒L⇒L-assoc) ∘ ⇒L (cutaxA-left [] _ refl) (⇒L (cutaxA-left [] _ refl) refl)) ∘ (~ ⇒L⇒R {[]}))) refl)
  --         -- currying and uncurrying, we show the direction (E ⊗ D) ⇒ F ⊢ D ⇒ (E ⇒ F)

mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) | inj₂ (E , Ω₃ , eq₅ , refl) with cases++ Γ Γ₁ Ω₃ Γ₀ eq₅
mip≗⇒L⇒L-assoc Γ ._ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) (Γ ++ E ∷ Ω₄) Λ |
  --         cases++-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₄ ++ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Γ Ω₁ (A ⇒ B) |
  --         ++?-inj₂ Γ Ω₄ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) E |
  --         ++?-inj₁ (Γ₀ ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) (Γ ++ E ∷ Ω₄) Λ |
  --         cases++-inj₁ (Γ₀ ++ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₄ ++ Γ₀ ++ B' ∷ Λ₀) Γ Ω₁ (A ⇒ B) |
  --         ++?-inj₂ Γ Ω₄ (Γ₀ ++ B' ∷ Λ₀) E 
  --           = intrp≗ (h~ ⇒L⇒L-assoc)

mip≗⇒L⇒L-assoc Γ ._ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₂ (Ω₄ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) (Γ₁ ++ Ω₄) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ Ω₄ Γ₁ (E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) |
  --         ++?-inj₂ Ω₄ Ω₃ (Δ₁ ++ A' ⇒ B' ∷ Λ₀) E |
  --         ++?-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁  (Ω₄ ++ E ∷ Ω₃ ++ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₃ ++ B' ∷ Λ₀) (Γ₁ ++ Ω₄) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ Ω₄ Γ₁ (E ∷ Ω₃ ++ B' ∷ Λ₀) 
  --           = intrp≗ (h~ (⇒L⇒R ∘ ⇒R ⇒L⇒L-assoc))

mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) with cases++ (Γ₁ ++ Γ₀ ++ Δ₁) Γ Ω₀ Δ eq₂

mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ ) Λ₁ (A ⇒ B) = {!   !}
          -- interpolant context is in g, so this is fine.

mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) with ++? Γ (Γ₁ ++ Γ₀) Ω₂ Δ₁ eq₄


mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) | inj₂ (E , Ω₃ , eq₅ , refl) with cases++ Γ Γ₁ Ω₃ Γ₀ eq₅

mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₂ (Ω₄ , refl , refl) 
  rewrite ++?-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) 
          = {! ++?-inj₂ Γ₁ Ω₄ (Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) E  !}
          -- Δ  = E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀ where g : Ω₄ ++ E ∷ Ω₃ ++ B' ∷ Ω₀ ++ Ω₁ ⊢ A 

-- These two are morally the same.

mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl)
  rewrite ++?-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₄) (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₄) Γ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₀ Ω₁ |
          cases++-inj₁ Δ₁ Ω₀ Ω₁ (A' ⇒ B') = {! ++?-inj₁ [] Γ₀ Δ₁  !} -- problematic ++?-inj₁ call
-- mip≗⇒L⇒L-assoc Γ Δ ._ {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl) 
--   rewrite ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₄) (Ω₁ ++ A ⇒ B ∷ Λ₁) |
--           cases++-inj₂ Ω₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
--           ++?-inj₁ (E ∷ Ω₄) Γ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) = {!   !}
--           -- ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₀ Ω₁ |
--           -- cases++-inj₁ Δ₁ Ω₀ Ω₁ (A' ⇒ B') = {! ++?-inj !}
-- mip≗⇒L⇒L-assoc Γ Δ ._ {E₁ ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl) = {!   !}
--   -- rewrite ++?-inj₁ (E₁ ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₄) (Ω₁ ++ A ⇒ B ∷ Λ₁) |
--   --         cases++-inj₂ Ω₁ (E₁ ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
--   --         ++?-inj₁ (E ∷ Ω₄) Γ (E₁ ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) |
--   --         ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (E₁ ∷ Γ₀) Ω₁ |
--   --         cases++-inj₁ Δ₁ Ω₀ Ω₁ (A' ⇒ B') |
--   --         ++?-inj₁ (E₁ ∷ Γ₀ ++ B' ∷ Ω₀) (Γ ++ E ∷ Ω₄) (Ω₁ ++ A ⇒ B ∷ Λ₁) |
--   --         cases++-inj₂ Ω₁ (Γ₀ ++ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
--   --         ++?-inj₁ (E ∷ Ω₄) Γ (E₁ ∷ Γ₀ ++ B' ∷ Ω₀) 
--   --           = intrp≗ (h~ ⇒L⊗R₂)

-- These two are morally the same.

-- These three are morally the same. The additional cases come from the beauracracy of ++?.
mip≗⇒L⇒L-assoc Γ Δ ._ {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ ([] , refl , refl) 
   rewrite ++?-inj₁ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Γ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) |
          cases++-inj₁ Ω₂ Ω₀ Ω₁ (A' ⇒ B') |
          ++?-inj₁ (B' ∷ Ω₀) Γ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ Ω₀ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Γ (B' ∷ Ω₀) 
            = intrp≗ (↜∷ ({!   !} , {!   !}) refl)
          -- (↜∷ (⇒R (⊗L {_ ∷ []} {!   !}) , {!   !} , {!   !}) refl)
        
mip≗⇒L⇒L-assoc Γ Δ ._ {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ (E ∷ Ω₃ , refl , refl) = {!   !}
  --  rewrite ++?-inj₁ (E ∷ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ (E ∷ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ Ω₃ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) E |
  --         cases++-inj₁ (Ω₃ ++ Ω₂) Ω₀ Ω₁ (A' ⇒ B') |
  --         cases++-inj₂ Ω₂ Ω₃ Ω₀ (A' ⇒ B') |
  --         ++?-inj₁ (B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ Ω₀ Λ₁ (A ⇒ B) |
  --         ++?-inj₁ [] Γ₁ (B' ∷ Ω₀) 
  --           = intrp≗ (↜∷ (⇒R (⊗R (mip Γ₁ [] (B ∷ Λ₁) h refl .MIP.h) (⇒L {[]} ax ax)) , 
  --            (((((⇒L (⇒L refl (~ (cutaxA-left [] _ refl)) 
  --            ∘ (~ (cut-cong₂ [] refl (cut⇒L≗ [] ax ax (mip [] (B' ∷ Ω₀) Ω₁ g refl .MIP.g) refl)))) {! cut-intrp  !} 
  --            ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
  --            ∘ (~ (cut-cong₂ Γ₁ refl (≡to≗ (cut⇒L-cases++-comm₂ Γ₁ []))))) 
  --            ∘ (~ (cut-cong₂ Γ₁ refl (cut-cong₂ Γ₁ refl (≡to≗ (cut⇒L-cases++₁ [] (Γ₁ ++ mip Γ₁ [] (B ∷ Λ₁) h refl .MIP.D ∷ []))))))) 
  --            ∘ cut-cong₂ Γ₁ refl (≡to≗ (cut⊗R⊗Lcases++ Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁)))) 
  --            ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) (E ∷ Ω₃))))) , 
  --             ⇒R ((~ ⇒L⊗R₂) ∘ ⇒L (cutaxA-left [] _ refl) refl)) refl)

          -- There is a redundant interpolantion mip Γ₁ [] (B ∷ Λ₁) h refl, otherwise this case is just a simple ⇒L⇒L-assoc where the interpolant formula is D ⇒ D'.
          -- cases++-inj₂ [] (Γ₁ ++ E ∷ Ω₃) (Ω₁ ++ A ⇒ B ∷ Λ₁) (mip [] (E ∷ Ω₃) Ω₂ f refl .MIP.D ⇒ (mip Γ₁ [] (B ∷ Λ₁) h refl .MIP.D ⊗ mip [] (B' ∷ Ω₀) Ω₁ g refl .MIP.D))

mip≗⇒L⇒L-assoc Γ Δ ._ {E ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (E ∷ Γ₀ ++ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ (E ∷ Γ₀ ++ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ (Γ₀ ++ Ω₃) (Ω₂ ++ A' ⇒ B' ∷ Ω₀) E |
  --         ++?-inj₁ (Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₀ Ω₁ |
  --         cases++-inj₁ (Ω₃ ++ Ω₂) Ω₀ Ω₁ (A' ⇒ B') |
  --         cases++-inj₂ Ω₂ (Γ₀ ++ Ω₃) Ω₀ (A' ⇒ B') |
  --         ++?-inj₁ Ω₃ Γ₀ Ω₂ |
  --         ++?-inj₁ (E ∷ Γ₀ ++ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ (Γ₀ ++ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ Γ₀ (B' ∷ Ω₀) E 
  --           = intrp≗ (g~ ⇒L⇒L-assoc)

-- These three are morally the same. The additional cases come from the beauracracy of ++?.

mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , refl , eq₂) | inj₂ (Ω₀ , refl , refl) with ++? (Γ₁ ++ Γ₀) Γ Ω Δ eq₂
... | inj₁ (Ω₁ , refl , eq₄) with ++? Γ Γ₁ Ω₁ Γ₀ eq₄
mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) = {!   !}

-- These two are the same and the interpolant formulae are (D'' ⊗ D') ⊗ D and D'' ⊗ (D' ⊗ D).
mip≗⇒L⇒L-assoc Γ Δ ._ {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ Ω (Γ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ (Ω₀ ++ A' ⇒ B' ∷ Λ₀) Ω Λ₁ (A ⇒ B) |
  --         ++?-inj₁ (E ∷ Ω₂) Γ Ω = {!   !}
mip≗⇒L⇒L-assoc Γ Δ ._ {E₀ ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) = {!   !}
--   rewrite ++?-inj₁ (E₀ ∷ Γ₀ ++ Ω) (Γ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
--           cases++-inj₂ (Ω₀ ++ A' ⇒ B' ∷ Λ₀) (E₀ ∷ Γ₀ ++ Ω) Λ₁ (A ⇒ B) |
--           ++?-inj₁ (E ∷ Ω₂) Γ (E₀ ∷ Γ₀ ++ Ω) |
--           ++?-inj₁ Ω Γ₀ (Ω₀ ++ A' ⇒ B' ∷ Λ₀) |
--           cases++-inj₂ Ω₀ Ω Λ₀ (A' ⇒ B') |
--           ++?-inj₁ (E₀ ∷ Γ₀) (Γ ++ E ∷ Ω₂) (B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
--           cases++-inj₂ (B' ∷ Λ₀) Γ₀ Λ₁ (A ⇒ B) |
--           ++?-inj₁ (E ∷ Ω₂) Γ (E₀ ∷ Γ₀) 
--             = intrp≗ (↝∷ (⊗L {[]} (⊗L {[]} (⊗R ax (⊗R ax ax))) , 
--               (⊗L ((~ ⊗L⇒L-comm₁) ∘ (⊗L (((((⇒L⇒L-assoc ∘ ⇒L (⇒L (~ cutaxA-left [] _ refl) (~ cutaxA-left [] _ refl)) refl)) 
--               ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] (Γ ++ _ ∷ []) {Ω₀ ++ A' ⇒ B' ∷ Λ₀} {f = ⊗R ax ax} {⊗L {[]}
--          (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
--           (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl)))} {MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl)})))) 
--           ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl) ∷ []) (⊗R ax ax)
--         (⇒L {Γ ++ _ ∷ []}
--         (⊗L
--          (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
--           (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl))))
--         (MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl))) refl) refl)) 
--               ∘ (≡to≗ (cut⊗R⊗Lcases++ Γ (Ω₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) {f = ax} {⊗R ax ax})))
--               ∘ (~ cut⊗L≗ Γ [] (_ ∷ []) (⊗R ax (⊗R ax ax)) (⊗L {Γ} (⇒L {Γ ++ _ ∷ []}
--          (⊗L {[]}
--           (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
--            (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl))))
--          (MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl)))) refl))) 
--               ∘ (~ cut⊗L≗ Γ [] [] (⊗L {[]} (⊗R ax (⊗R ax ax))) (⊗L
--         (⇒L {Γ ++ _ ∷ []}
--          (⊗L {[]}
--           (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
--            (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl))))
--          (MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl)))) refl)) , 
--               refl) refl)
-- -- These two are the same and the interpolant formulae are (D'' ⊗ D') ⊗ D and D'' ⊗ (D' ⊗ D).
mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) = {!   !} 

mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (E , Ω , eq₁ , refl) with cases++ (Γ ++ Δ) Γ₁ Ω Γ₀ eq₁
mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) = {!   !}
mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (E , Ω , eq₁ , refl) | inj₂ (Ω₀ , refl , eq₃) with ++? Γ₁ Γ Ω₀ Δ eq₃
mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E , Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) = {!   !}
mip≗⇒L⇒L-assoc Γ Δ ._ {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E , Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (E₁ , Ω₁ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (E₁ ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) (Ω₁ ++ Δ) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ Ω₁ Δ E₁ |
  --         ++?-inj₂ (Ω₁ ++ Δ) Ω (Δ₁ ++ A' ⇒ B' ∷ Λ₀) E |
  --         ++?-inj₁ (E₁ ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ (E ∷ Ω ++ B' ∷ Λ₀) (Ω₁ ++ Δ) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ Ω₁ Δ E₁ 
  --           = intrp≗ (g~ ⇒L⇒L-assoc)