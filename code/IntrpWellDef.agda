{-# OPTIONS --rewriting #-}

module IntrpWellDef where

open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Data.Product
-- open import Fma
open import SeqCalc
open import Cut
open import Utilities
open import Mip
open import IntrpTriples
{-
Maehara interpolation procedure is well-defined wrt. ≗
-}

{-
We have dealt with the most complicated cases,
⇒L⇒L-assoc and ⇒L⇒L-comm.
Other cases are similar.
Most of the proofs are commented out due to type-checking efficiency.
-}
          
record MIP≗ (Γ Δ Λ : Cxt) (C : Fma) (n n' : MIP Γ Δ Λ C) : Set where
  constructor intrp≗
  field
    eq : n ~ n'

mip≗ : ∀ Γ Δ Λ {Ω} {C}
  → {f f' : Ω ⊢ C}
  → (eq : Ω ≡ Γ ++ Δ ++ Λ)
  → (p : f ≗ f')
  → MIP≗ Γ Δ Λ C (mip Γ Δ Λ f eq) (mip Γ Δ Λ f' eq)

mip≗ Γ Δ Λ eq ⇒L⇒R = {!   !} 
mip≗ Γ Δ Λ eq ⇒L⊗R₁ = {!   !}
mip≗ Γ Δ Λ eq ⇒L⊗R₂ = {!   !}
mip≗ Γ Δ Λ eq ⊗L⊗R₁ = {!   !}
mip≗ Γ Δ Λ eq ⊗L⊗R₂ = {!   !}
mip≗ Γ Δ Λ eq ⊗L⊗L = {!   !}
mip≗ Γ Δ Λ eq ⊗L⇒L-assoc = {!   !}
mip≗ Γ Δ Λ eq ⊗L⇒L-comm₁ = {!   !}
mip≗ Γ Δ Λ eq ⊗L⇒L-comm₂ = {!      !}

-- In princiapl 15 cases. The additionbal cases come from addtional pattern-matching to use the helper function ++?-injᵢ correctly.
mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) with ++? (Γ ++ Δ) (Γ₁ ++ Γ₀) Λ (Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω (Λ₀ ++ A ⇒ B ∷ Λ₁) Λ (sym eq₁)
... | inj₁ (Ω₀ , refl , eq₄) with cases++ Λ₀ Ω₀ Λ₁ Λ (sym eq₄)
mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) with cases++ (Γ₁ ++ Γ₀ ++ Δ₁) Γ (Λ₀ ++ A ⇒ B ∷ Ω₁) Δ eq₂
... | inj₁ (Ω₂ , refl , eq₄) with cases++ Λ₀ Ω₂ Ω₁ Δ (sym eq₄)
mip≗ ._ Δ Λ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₃ ++ Δ) Γ₁ Λ |
  --         cases++-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) (Ω₃ ++ Δ) Λ (A ⇒ B) |
  --         cases++-inj₁ (Γ₁ ++ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Ω₃ Δ (A ⇒ B) |
  --         ++?-inj₁ (Γ₀ ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₃ ++ Δ) Γ₁ Λ |
  --         cases++-inj₁ (Γ₀ ++ B' ∷ Λ₀) (Ω₃ ++ Δ) Λ (A ⇒ B) |
  --         cases++-inj₁ (Γ₁ ++ Γ₀ ++ B' ∷ Λ₀) Ω₃ Δ (A ⇒ B)
  --           = intrp≗ (↝∷ (ax , (⇒L⇒L-assoc ∘ (~ cutaxA-left (Γ₁ ++ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₃) _ refl)) , refl) refl)

mip≗ ._ Δ Λ refl (⇒L⇒L-assoc {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h}) | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Ω₃ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Ω₃) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ Ω₃ (Γ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₂) Γ₁ Ω₃ |
  --         cases++-inj₁ Δ₁ Ω₂ Ω₃ (A' ⇒ B') |
  --         ++?-inj₁ (B' ∷ Ω₂ ++ Ω₃ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁ (Ω₂ ++ Ω₃) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ Ω₃ (Γ₁ ++ B' ∷ Ω₂) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ (B' ∷ Ω₂) Γ₁ Ω₃ 
  --           = intrp≗ {!   !}
  --         -- The interpolant context for the first premise f is empty, for the interpolant formula, it adds a dummy unit I.
  --         -- The shape of the proof will be exactly the same as the one below.
  --         -- This case arises due to ++-injᵢ cannot handle ++? [] Γ₀ (Γ₀ ++ Δ₁) Δ₁ refl
  --         -- The interpolant context is Δ  = Ω₃ ++ A ⇒ B ∷ Ω₁, which has nothing to do with f.
mip≗ ._ Δ Λ refl (⇒L⇒L-assoc {E ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) = {!   !}
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
  --           = intrp≗ (↝∷ (ax , ⇒L⇒L-assoc {E ∷ Γ₀} ∘ (~ cutaxA-left (Γ₁ ++ E ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂) _ refl) , refl) refl)

mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) with ++? Γ (Γ₁ ++ Γ₀) Ω₂ Δ₁ eq₄
mip≗ Γ ._ Λ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h}) | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) = {!   !}
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

mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) | inj₂ (E , Ω₃ , eq₅ , refl) with cases++ Γ Γ₁ Ω₃ Γ₀ eq₅
mip≗ Γ ._ Λ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) (Γ ++ E ∷ Ω₄) Λ |
  --         cases++-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₄ ++ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Γ Ω₁ (A ⇒ B) |
  --         ++?-inj₂ Γ Ω₄ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) E |
  --         ++?-inj₁ (Γ₀ ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) (Γ ++ E ∷ Ω₄) Λ |
  --         cases++-inj₁ (Γ₀ ++ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₄ ++ Γ₀ ++ B' ∷ Λ₀) Γ Ω₁ (A ⇒ B) |
  --         ++?-inj₂ Γ Ω₄ (Γ₀ ++ B' ∷ Λ₀) E 
  --           = intrp≗ (↝∷ (ax , (~ cutaxA-left _ _ refl) , ⇒L⇒L-assoc) refl)

mip≗ Γ ._ Λ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (._ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₂ (Ω₄ , refl , refl) = {!   !} 
  -- rewrite ++?-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) (Γ₁ ++ Ω₄) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ Ω₄ Γ₁ (E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) |
  --         ++?-inj₂ Ω₄ Ω₃ (Δ₁ ++ A' ⇒ B' ∷ Λ₀) E |
  --         ++?-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ Λ |
  --         cases++-inj₁  (Ω₄ ++ E ∷ Ω₃ ++ B' ∷ Λ₀) Ω₁ Λ (A ⇒ B) |
  --         cases++-inj₂ (E ∷ Ω₃ ++ B' ∷ Λ₀) (Γ₁ ++ Ω₄) Ω₁ (A ⇒ B) |
  --         ++?-inj₁ Ω₄ Γ₁ (E ∷ Ω₃ ++ B' ∷ Λ₀) 
  --           = intrp≗ (↝∷ (ax , (~ cutaxA-left (Γ₁ ++ Ω₄) _ refl) , (⇒L⇒R ∘ ⇒R ⇒L⇒L-assoc)) refl)

mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) with cases++ (Γ₁ ++ Γ₀ ++ Δ₁) Γ Ω₀ Δ eq₂

mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ ) Λ₁ (A ⇒ B) = {!   !}
          -- interpolant context is in g, so this is fine.

mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) with ++? Γ (Γ₁ ++ Γ₀) Ω₂ Δ₁ eq₄


mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , eq₄) | inj₂ (E , Ω₃ , eq₅ , refl) with cases++ Γ Γ₁ Ω₃ Γ₀ eq₅

mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₂ (Ω₄ , refl , refl) 
  rewrite ++?-inj₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Ω₄ ++ E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) 
          = {! ++?-inj₂ Γ₁ Ω₄ (Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) E  !}
          -- Δ  = E ∷ Ω₃ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀ where g : Ω₄ ++ E ∷ Ω₃ ++ B' ∷ Ω₀ ++ Ω₁ ⊢ A 

-- These two are morally the same.
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl) 
  rewrite ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₄) (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₄) Γ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) = {!   !}
          -- ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₀ Ω₁ |
          -- cases++-inj₁ Δ₁ Ω₀ Ω₁ (A' ⇒ B') = {! ++?-inj !}
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {E₁ ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (._ , refl , refl) | inj₂ (E , Ω₃ , refl , refl) | inj₁ (Ω₄ , refl , refl) 
  rewrite ++?-inj₁ (E₁ ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₄) (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (E₁ ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₄) Γ (E₁ ∷ Γ₀ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) |
          ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (E₁ ∷ Γ₀) Ω₁ |
          cases++-inj₁ Δ₁ Ω₀ Ω₁ (A' ⇒ B') |
          ++?-inj₁ (E₁ ∷ Γ₀ ++ B' ∷ Ω₀) (Γ ++ E ∷ Ω₄) (Ω₁ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ Ω₁ (Γ₀ ++ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₄) Γ (E₁ ∷ Γ₀ ++ B' ∷ Ω₀) = intrp≗ (↝∷ (ax , (~ cutaxA-left Γ _ refl) , ⇒L⊗R₂) refl)
          -- ++? [] Γ₀ (E₁ ∷ Γ₀ ++ Δ₁) Δ₁ refl
-- These two are morally the same.

-- These three are morally the same. The additional cases come from the beauracracy of ++?.
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ ([] , refl , refl) = {!   !} 
  --  rewrite ++?-inj₁ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
  --         ++?-inj₁ [] Γ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) |
  --         cases++-inj₁ Ω₂ Ω₀ Ω₁ (A' ⇒ B') |
  --         ++?-inj₁ (B' ∷ Ω₀) Γ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ Ω₀ Λ₁ (A ⇒ B) |
  --         ++?-inj₁ [] Γ (B' ∷ Ω₀) = intrp≗ (↜∷ (⇒R (⊗L {_ ∷ []} {! ⇒L {_ ∷ []}   !}) , {!   !} , {!   !}) refl)
  --         -- The two interpolant formulae of mip [] [] Ω₂ f refl and mip Γ [] (B ∷ Λ₁) h refl) are I, which are redundant interpolations.
  --         -- But in this formalization, we don't consider the interpolation for empty context. We have the rules of the unit I just for convenience to not bother with List⁺.
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ (E ∷ Ω₃ , refl , refl) = {!   !}
  --  rewrite ++?-inj₁ (E ∷ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ (E ∷ Ω₃ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ Ω₃ (Ω₂ ++ A' ⇒ B' ∷ Ω₀) E |
  --         cases++-inj₁ (Ω₃ ++ Ω₂) Ω₀ Ω₁ (A' ⇒ B') |
  --         cases++-inj₂ Ω₂ Ω₃ Ω₀ (A' ⇒ B') |
  --         ++?-inj₁ (B' ∷ Ω₀) Γ₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ Ω₁ Ω₀ Λ₁ (A ⇒ B) |
  --         ++?-inj₁ [] Γ₁ (B' ∷ Ω₀) = intrp≗ (↝∷ ({!   !} , {!   !} , {!   !}) refl)
  --         -- There is a redundant interpolantion mip Γ₁ [] (B ∷ Λ₁) h refl, otherwise this case is just a simple ⇒L⇒L-assoc where the interpolant formula is D ⇒ D'.
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {E ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) = {!   !}
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
  --           = intrp≗ (↝∷ (ax , 
  --             (⇒L⇒L-assoc 
  --             ∘ (~ cutaxA-left (Γ₁ ++ E ∷ Γ₀ ++ Ω₃) (⇒L (⇒L {E ∷ Γ₀} (MIP.h (mip [] Ω₃ Ω₂ f refl)) (MIP.g (mip (E ∷ Γ₀) (B' ∷ Ω₀) Ω₁ g refl))) h) refl)) , 
  --             refl) refl)

-- These three are morally the same. The additional cases come from the beauracracy of ++?.

mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (Ω , refl , eq₂) | inj₂ (Ω₀ , refl , refl) with ++? (Γ₁ ++ Γ₀) Γ Ω Δ eq₂
... | inj₁ (Ω₁ , refl , eq₄) with ++? Γ Γ₁ Ω₁ Γ₀ eq₄
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) = {!   !}

-- These two are the same and the interpolant formulae are (D'' ⊗ D') ⊗ D and D'' ⊗ (D' ⊗ D).
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {[]} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
  rewrite ++?-inj₁ Ω (Γ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ (Ω₀ ++ A' ⇒ B' ∷ Λ₀) Ω Λ₁ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₂) Γ Ω = {!   !}
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {E₀ ∷ Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
  rewrite ++?-inj₁ (E₀ ∷ Γ₀ ++ Ω) (Γ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ (Ω₀ ++ A' ⇒ B' ∷ Λ₀) (E₀ ∷ Γ₀ ++ Ω) Λ₁ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₂) Γ (E₀ ∷ Γ₀ ++ Ω) |
          ++?-inj₁ Ω Γ₀ (Ω₀ ++ A' ⇒ B' ∷ Λ₀) |
          cases++-inj₂ Ω₀ Ω Λ₀ (A' ⇒ B') |
          ++?-inj₁ (E₀ ∷ Γ₀) (Γ ++ E ∷ Ω₂) (B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
          cases++-inj₂ (B' ∷ Λ₀) Γ₀ Λ₁ (A ⇒ B) |
          ++?-inj₁ (E ∷ Ω₂) Γ (E₀ ∷ Γ₀) 
            = intrp≗ (↝∷ (⊗L {[]} (⊗L {[]} (⊗R ax (⊗R ax ax))) , 
              (⊗L ((~ ⊗L⇒L-comm₁) ∘ (⊗L (((((⇒L⇒L-assoc ∘ ⇒L (⇒L (~ cutaxA-left [] _ refl) (~ cutaxA-left [] _ refl)) refl)) 
              ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] (Γ ++ _ ∷ []) {Ω₀ ++ A' ⇒ B' ∷ Λ₀} {f = ⊗R ax ax} {⊗L {[]}
         (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
          (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl)))} {MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl)})))) 
          ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl) ∷ []) (⊗R ax ax)
        (⇒L {Γ ++ _ ∷ []}
        (⊗L
         (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
          (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl))))
        (MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl))) refl) refl)) 
              ∘ (≡to≗ (cut⊗R⊗Lcases++ Γ (Ω₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) {f = ax} {⊗R ax ax})))
              ∘ (~ cut⊗L≗ Γ [] (_ ∷ []) (⊗R ax (⊗R ax ax)) (⊗L {Γ} (⇒L {Γ ++ _ ∷ []}
         (⊗L {[]}
          (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
           (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl))))
         (MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl)))) refl))) 
              ∘ (~ cut⊗L≗ Γ [] [] (⊗L {[]} (⊗R ax (⊗R ax ax))) (⊗L
        (⇒L {Γ ++ _ ∷ []}
         (⊗L {[]}
          (⇒L {_ ∷ []} (MIP.g (mip [] Ω Ω₀ f refl))
           (MIP.g (mip [] (E₀ ∷ Γ₀) (B' ∷ Λ₀) g refl))))
         (MIP.g (mip Γ (E ∷ Ω₂) (B ∷ Λ₁) h refl)))) refl)) , 
              refl) refl)
-- These two are the same and the interpolant formulae are (D'' ⊗ D') ⊗ D and D'' ⊗ (D' ⊗ D).
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) = {!   !} 

mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₂ (E , Ω , eq₁ , refl) with cases++ (Γ ++ Δ) Γ₁ Ω Γ₀ eq₁
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₂ (E , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) = {!   !}
mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₂ (E , Ω , eq₁ , refl) | inj₂ (Ω₀ , refl , eq₃) with ++? Γ₁ Γ Ω₀ Δ eq₃
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₂ (E , Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) = {!   !}
mip≗ Γ Δ ._ refl (⇒L⇒L-assoc {Γ₀} {Γ₁} {Δ₁} {Λ₀} {Λ₁} {A} {B} {A'} {B'}) | inj₂ (E , Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (E₁ , Ω₁ , refl , refl) = {!   !}
  -- rewrite ++?-inj₁ (E₁ ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Λ₀) (Ω₁ ++ Δ) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ Ω₁ Δ E₁ |
  --         ++?-inj₂ (Ω₁ ++ Δ) Ω (Δ₁ ++ A' ⇒ B' ∷ Λ₀) E |
  --         ++?-inj₁ (E₁ ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) |
  --         cases++-inj₂ (E ∷ Ω ++ B' ∷ Λ₀) (Ω₁ ++ Δ) Λ₁ (A ⇒ B) |
  --         ++?-inj₂ Γ₁ Ω₁ Δ E₁ 
  --           = intrp≗ (↝∷ (ax , (⇒L⇒L-assoc {E₁ ∷ Ω₁ ++ _ ∷ E ∷ Ω} ∘ (~ cutaxA-left (Γ₁ ++ E₁ ∷ Ω₁) _ refl)) , refl) refl)

-- 21 cases
mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) = {!   !}
-- with ++? (Γ ++ Δ) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Λ (Δ₁ ++ A' ⇒ B' ∷ Ξ) eq
-- ... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω Ξ Λ (sym eq₁)
-- mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (Ω , refl , eq₂) | inj₁ (Ω₀ , refl , refl) with ++? (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Γ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) Δ eq₂
-- mip≗ Γ Δ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} {f = f} {f'} {g}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ ([] , refl , refl) 
--   rewrite cases++-inj₂ Δ₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₀ (A' ⇒ B') |
--           ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ₁ |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ (B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Λ₁) Λ |
--           cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
--           cases++-inj₂ Δ₁ (Γ₁ ++ B ∷ Λ₁) Ω₀ (A' ⇒ B') |
--           ++?-inj₁ [] (Γ₁ ++ B ∷ Λ₁) Δ₁ 
--             = intrp≗ (↝∷ (ax , 
--               (⇒L⇒L-comm 
--               ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (⇒L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁} (MIP.h (mip [] [] Δ₁ f' refl))
--               (⇒L f (MIP.g (mip (Γ₁ ++ B ∷ Λ₁) (B' ∷ Ω₀) Λ g refl)))) refl)) , 
--               refl) refl)

-- ... | inj₁ (E ∷ Ω₁ , refl , eq₄) with cases++ Γ (Γ₁ ++ Δ₀) Ω₁ (A ⇒ B ∷ Λ₁) eq₄
-- ... | inj₁ (Ω₂ , eq₅ , refl) with cases++ Γ Γ₁ Ω₂ Δ₀ eq₅
-- mip≗ Γ ._ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ ._ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₁ (Ω₃ , refl , refl) 
--   rewrite cases++-inj₂ (E ∷ Ω₃ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) Γ Ω₀ (A' ⇒ B') |
--           ++?-inj₂ Γ (Ω₃ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) (Γ ++ E ∷ Ω₃) Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₃ ++ Δ₀) Γ (Λ₁ ++ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₂ Γ Ω₃ Δ₀ E |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₃) Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₃ ++ Δ₀) Γ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₂ Γ Ω₃ Δ₀ E |
--           ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ ++ E ∷ Ω₃ ++ B ∷ Λ₁) Λ |
--           cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') | 
--           cases++-inj₂ (E ∷ Ω₃ ++ B ∷ Λ₁ ++ Δ₁) Γ Ω₀ (A' ⇒ B') |
--           ++?-inj₂ Γ (Ω₃ ++ B ∷ Λ₁) Δ₁ E = intrp≗ (↝∷ (ax , (~ cutaxA-left Γ _ refl) , ⇒L⇒L-comm) refl)
  
-- mip≗ Γ ._ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ ._ , refl , refl) | inj₁ (Ω₂ , refl , refl) | inj₂ (Ω₃ , refl , refl) 
--   rewrite cases++-inj₂ (E ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ Δ₁) (Γ₁ ++ Ω₃) Ω₀ (A' ⇒ B') |
--           ++?-inj₂ (Γ₁ ++ Ω₃) (Ω₂ ++ A ⇒ B ∷ Λ₁) Δ₁ E |
--           ++?-inj₁ (Ω₃ ++ E ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) Γ₁ Λ  |
--           cases++-inj₁ (Ω₃ ++ E ∷ Ω₂) (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₂) (Γ₁ ++ Ω₃) (Λ₁ ++ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ Ω₃ Γ₁ (E ∷ Ω₂) |
--           ++?-inj₁ (Ω₃ ++ E ∷ Ω₂ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ (Ω₃ ++ E ∷ Ω₂) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₂) (Γ₁ ++ Ω₃) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ Ω₃ Γ₁ (E ∷ Ω₂) |
--           ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Λ₁) Λ |
--           cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
--           cases++-inj₂ (B ∷ Λ₁ ++ Δ₁) Γ₁ Ω₀ (A' ⇒ B') |
--           ++?-inj₂ Γ₁ Λ₁ Δ₁ B 
--             = intrp≗ (↝∷ (ax , (~ cutaxA-left (Γ₁ ++ Ω₃) _ refl) , (⇒R ⇒L⇒L-comm ∘ (~ ⇒L⇒R))) refl)
-- mip≗ Γ Δ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'} {f = f} {f'} {g}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ Ω₁ , refl , refl) | inj₂ ([] , refl , refl) 
--   rewrite cases++-inj₂ (A ⇒ B ∷ Λ₁ ++ Δ₁) (Γ₁ ++ Δ₀) Ω₀ (A' ⇒ B') |
--           ++?-inj₂ (Γ₁ ++ Δ₀) Ω₁ Δ₁ (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Ω₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₂ [] (Γ₁ ++ Δ₀) (Ω₁ ++ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ Δ₀ Γ₁ [] |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₂ [] (Γ₁ ++ Δ₀) (Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ Δ₀ Γ₁ [] |
--           ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Ω₁) Λ |
--           cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
--           cases++-inj₂ (B ∷ Ω₁ ++ Δ₁) Γ₁ Ω₀ (A' ⇒ B') |
--           ++?-inj₂ Γ₁ Ω₁ Δ₁ B 
--             = intrp≗ (↝∷ (ax , (~ cutaxA-left (Γ₁ ++ Δ₀) (⇒L (MIP.h (mip [] Δ₀ [] f refl))
--         (MIP.g (mip Γ₁ (B ∷ Ω₁ ++ B' ∷ Ω₀) Λ g refl))) refl) , (⇒R ⇒L⇒L-comm ∘ (~ ⇒L⇒R))) refl) 

--             -- intrp≗ (↝∷ (ax , 
--             --   (((⇒L (~ cutaxA-right _) (~ cutaxA-left Γ₁ _ refl) 
--             --   ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
--             --   ∘ (~ cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ ax ax (MIP.g (mip Γ₁ (B ∷ Ω₁ ++ B' ∷ Ω₀) Λ g refl)) refl))) 
--             --   ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ Δ₀)))) , 
--             --   (⇒R (cutaxA-left [] (cut [] (⇒L (MIP.g (mip [] Δ₀ [] f refl)) (⇒L f' (MIP.h (mip Γ₁ (B ∷ Ω₁ ++ B' ∷ Ω₀) Λ g refl)))) ax refl) refl 
--             --   ∘ (cutaxA-right _ 
--             --   ∘ ⇒L⇒L-comm)) 
--             --   ∘ (~ ⇒L⇒R)))
--             --    refl)

-- mip≗ Γ Δ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (E ∷ Ω₁ , refl , refl) | inj₂ (E₁ ∷ Ω₂ , refl , refl) 
--   rewrite cases++-inj₂ (E ∷ Ω₁ ++ Δ₁) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₂) Ω₀ (A' ⇒ B') |
--           ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₂) Ω₁ Δ₁ E |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₂ ++ E ∷ Ω₁ ++ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Ω₂ ++ E ∷ Ω₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₂ (E ∷ Ω₁ ++ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₂ ++ E ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Ω₂ ++ E ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₂ (E ∷ Ω₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ (Δ₁ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Ω₂ ++ E ∷ Ω₁) Λ |
--           cases++-inj₁ Δ₁ Ω₀ Λ (A' ⇒ B') |
--           cases++-inj₂ (E ∷ Ω₁ ++ Δ₁) (Γ₁ ++ B ∷ Ω₂) Ω₀ (A' ⇒ B') |
--           ++?-inj₂ (Γ₁ ++ B ∷ Ω₂) Ω₁ Δ₁ E = intrp≗ (↝∷ (ax , (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₂) _ refl) , cutaxA-right _) refl)
--           -- intrp context is in Γ ++ B ∷ Λ ++ B' ∷ Ξ ⊢ C and does not split Δ₀ nor Δ₁.

-- mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (Ω , refl , eq₂) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , eq₄) with cases++ Δ₁ (E ∷ Ω₁) Ω₀ Δ (sym eq₄)
-- mip≗ ._ Δ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {[]} {Λ₁} {._} {A = A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl)
--   rewrite cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₁ Δ (A' ⇒ B') |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ A' ⇒ B' ∷ Ω₁ ++ Δ) Γ₁ Λ |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₁ ++ Δ) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₁ ++ Δ) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ B' ∷ Ω₁) Δ (A ⇒ B) |
--           cases++-inj₁ Δ₀ (Λ₁ ++ A' ⇒ B' ∷ Ω₁ ++ Δ) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ A' ⇒ B' ∷ Ω₁) Δ (A ⇒ B) |
--           ++?-inj₁ (A' ⇒ B' ∷ Ω₁ ++ Δ) (Γ₁ ++ B ∷ Λ₁) Λ |
--           cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Ω₁ Δ (A' ⇒ B') 
--             = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ A' ⇒ B' ∷ Ω₁) _ refl)) , refl) refl)
-- mip≗ ._ Δ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {E ∷ Δ₁} {Λ₁} {._} {A = A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
--   rewrite cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Δ₁) Ω₂ Δ (A' ⇒ B') |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₂ ++ Δ) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₂ ++ Δ) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ B' ∷ Ω₂) Δ (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂) Δ (A ⇒ B) |
--           ++?-inj₁ (E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂ ++ Δ) (Γ₁ ++ B ∷ Λ₁) Λ |
--           cases++-inj₁ Δ₁ (Ω₂ ++ Δ) Λ (A' ⇒ B') |
--           cases++-inj₁ (Γ₁ ++ B ∷ Λ₁ ++ E ∷ Δ₁) Ω₂ Δ (A' ⇒ B') 
--             = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Δ₁ ++ A' ⇒ B' ∷ Ω₂) _ refl)) , refl) refl)

-- mip≗ ._ Δ Λ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (._ , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) | inj₂ (Ω₂ , refl , refl) 
--   rewrite cases++-inj₂ Ω₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₁) Ω₀ (A' ⇒ B') |
--           ++?-inj₁ (E ∷ Ω₁) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₂ |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Λ₁ (B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₁ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Γ₁ Λ |
--           cases++-inj₁ Δ₀ (Λ₁ ++ E ∷ Ω₁ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) Λ (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ E ∷ Ω₁) (Ω₂ ++ A' ⇒ B' ∷ Ω₀) (A ⇒ B) |
--           ++?-inj₁ (E ∷ Ω₁ ++ Ω₂ ++ A' ⇒ B' ∷ Ω₀) (Γ₁ ++ B ∷ Λ₁) Λ |
--           cases++-inj₁ (Ω₁ ++ Ω₂) Ω₀ Λ (A' ⇒ B') |
--           cases++-inj₂ Ω₂ (Γ₁ ++ B ∷ Λ₁ ++ E ∷ Ω₁) Ω₀ (A' ⇒ B') |
--           ++?-inj₁ (E ∷ Ω₁) (Γ₁ ++ B ∷ Λ₁) Ω₂ 
--             = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₁) _ refl)) , refl) refl)

-- mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (Ω , refl , eq₂) | inj₂ (Ω₀ , refl , refl) with cases++ (Γ₁ ++ Δ₀) Γ (Λ₁ ++ Ω) Δ eq₂
-- ... | inj₁ (Ω₁ , refl , eq₄) with  ++? Ω₁ Λ₁ Δ Ω eq₄
-- mip≗ ._ Δ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ ([] , refl , refl) 
--   rewrite ++?-inj₁ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁) Γ₁ (B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ Ω₁ (B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ [] (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Ω) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ (Ω₁ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ Ω (A ⇒ B) |
--           ++?-inj₁ Ω (Γ₁ ++ B ∷ Ω₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
--           ++?-inj₁ [] (Γ₁ ++ B ∷ Ω₁) Ω 
--             = intrp≗ (↝∷ (ax , 
--               (((~ ⊗L⇒L-comm₂) ∘ ⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁} ⇒L⇒L-comm) ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) _ refl)) , 
--               refl) refl)
-- mip≗ ._ Δ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (E ∷ Ω₂ , refl , refl) 
--   rewrite ++?-inj₂ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₂ Δ E |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₂ ++ Δ) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ (Λ₁ ++ E ∷ Ω₂ ++ Δ) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) (Λ₁ ++ E ∷ Ω₂) Δ (A ⇒ B) |
--           ++?-inj₁ (E ∷ Ω₂ ++ Δ) (Γ₁ ++ B ∷ Λ₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ Ω₀ (Ω₂ ++ Δ) Ξ (A' ⇒ B') |
--           ++?-inj₂ (Γ₁ ++ B ∷ Λ₁) Ω₂ Δ E 
--             = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ E ∷ Ω₂) _ refl)) , refl) refl)
-- mip≗ ._ Δ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ (E ∷ Ω₂) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) Ω |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ E ∷ Ω₂) Γ₁ (B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ (Ω₁ ++ E ∷ Ω₂) (B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ (E ∷ Ω₂) (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ E ∷ Ω₂ ++ Ω) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ (Ω₁ ++ E ∷ Ω₂ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ (E ∷ Ω₂ ++ Ω) (A ⇒ B) |
--           ++?-inj₁ Ω (Γ₁ ++ B ∷ Ω₁ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
--           ++?-inj₁ (E ∷ Ω₂) (Γ₁ ++ B ∷ Ω₁) Ω 
--             = intrp≗ (↝∷ (ax , 
--               (((~ ⊗L⇒L-comm₂) ∘ ⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁} ⇒L⇒L-comm) ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) _ refl)) , 
--               refl) refl)
-- mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₁ (Ω , refl , eq₂) | inj₂ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , eq₄) with ++? Γ Γ₁ Ω₁ Δ₀ eq₄
-- mip≗ Γ ._ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ (Ω₁ ++ A ⇒ B ∷ Λ₁) (Γ₁ ++ Ω₂) Ω |
--           ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Λ₁) Γ₁ (B' ∷ Ξ) |
--           cases++-inj₁ (Ω₂ ++ Ω₁) Λ₁ (B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) Λ₁ (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ₁ Ω₁ |
--           ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Λ₁ ++ Ω) Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ (Ω₂ ++ Ω₁) (Λ₁ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) (Λ₁ ++ Ω) (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ₁ Ω₁ |
--           ++?-inj₁ Ω (Γ₁ ++ B ∷ Λ₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
--           ++?-inj₁ (B ∷ Λ₁) Γ₁ Ω 
--             = intrp≗ (↜∷ (⇒R ((⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))) , 
--               (((⊗L {Γ₁ ++ Ω₂} (((~ ⇒L⇒L-comm) 
--               ∘ ⇒L refl (((~ cutaxA-left (Γ₁ ++ MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl) ∷ []) (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))) refl) 
--               ∘ (~ cutaxA-left Γ₁ (cut (Γ₁ ++ _ ∷ []) ax (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))) refl) refl)) ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) {f = ax} {ax}))) 
--               ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) ∘ ≡to≗ (cut⊗L-cases++₂ Γ₁ [] (Ω₀ ++ A' ⇒ B' ∷ Ξ))) 
--               ∘ (~ cut-cong₂ Γ₁ refl (cut⊗L≗ Γ₁ (_ ∷ []) [] (⇒L {[]} ax (⊗R ax ax)) (⊗L (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))) refl 
--               ∘ ⊗L {Γ₁ ++ _ ∷ []} (cut⇒L≗ Γ₁ ax (⊗R ax ax) (⊗L (⇒L {Γ₁ ++ _ ∷ []} (MIP.g (mip [] Ω Ω₀ f' refl)) (MIP.g (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl)))) refl))))
--               ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (Ω₀ ++ A' ⇒ B' ∷ Ξ) Ω₂)))) , 
--               ⇒R ((~ ⇒L⊗R₁) ∘ ⇒L (cutaxA-left [] _ refl) refl)) refl) 
-- -- critical case, where the interpolant formula is
-- -- (D ⇒ F) ⊗ E ⊢ D ⇒ (F ⊗ E)

-- --  (MIP.D (mip [] Ω₂ Ω₁ f refl) ⇒
-- --        MIP.D (mip Γ₁ (B ∷ Λ₁) (B' ∷ Ξ) g refl))
-- --       ⊗ MIP.D (mip [] Ω Ω₀ f' refl)

-- mip≗ Γ ._ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g}) | inj₁ (Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ (E ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Γ Ω |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁) (Γ ++ E ∷ Ω₂) (B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ Λ₁ (B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ Λ₁ (A ⇒ B) |
--           ++?-inj₂ Γ Ω₂ Δ₀ E |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Ω) (Γ ++ E ∷ Ω₂) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ (Λ₁ ++ Ω) (Ω₀ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ (Λ₁ ++ Ω) (A ⇒ B) |
--           ++?-inj₂ Γ Ω₂ Δ₀ E |
--           ++?-inj₁ Ω (Γ ++ E ∷ Ω₂ ++ B ∷ Λ₁) (Ω₀ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ Ω₀ Ω Ξ (A' ⇒ B') |
--           ++?-inj₁ (E ∷ Ω₂ ++ B ∷ Λ₁) Γ Ω 
--             = intrp≗ (↝∷ (ax , (~ cutaxA-left Γ _ refl) , ⇒L⊗R₁) refl)
-- mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₂ (E , Ω , eq₁ , refl) with cases++ (Γ₁ ++ Δ₀) (Γ ++ Δ) Λ₁ (E ∷ Ω) (sym eq₁)
-- ... | inj₁ (Ω₀ , eq₂ , refl) with cases++ (Γ₁ ++ Δ₀) Γ Ω₀ Δ eq₂
-- mip≗ Γ Δ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₂ (E , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) 
--   rewrite ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ (Ω₁ ++ Δ) (E ∷ Ω ++ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ Δ (A ⇒ B) |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₁ ++ Δ) Γ₁ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ (Ω₁ ++ Δ) (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₁ (Γ₁ ++ Δ₀) Ω₁ Δ (A ⇒ B) |
--           ++?-inj₂ (Γ₁ ++ B ∷ Ω₁ ++ Δ) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) E 
--             = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) _ refl)) , refl) refl)
          
-- ... | inj₂ (Ω₁ , refl , eq₄) with ++? Γ Γ₁ Ω₁ Δ₀ eq₄
-- mip≗ Γ ._ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g}) | inj₂ (E , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Ω₀) Γ₁ (E ∷ Ω ++ B' ∷ Ξ) |
--           cases++-inj₁ (Ω₂ ++ Ω₁) Ω₀ (E ∷ Ω ++ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) Ω₀ (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ₁ Ω₁ |
--           ++?-inj₁ (Ω₂ ++ Ω₁ ++ A ⇒ B ∷ Ω₀) Γ₁ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ (Ω₂ ++ Ω₁) Ω₀ (E ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ Ω₁ (Γ₁ ++ Ω₂) Ω₀ (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ₁ Ω₁ |
--           ++?-inj₂ (Γ₁ ++ B ∷ Ω₀) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) E 
--             = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ Ω₂) _ refl)) , refl) refl)
            
--             -- intrp≗ (↝∷ (ax , 
--             --   {!  cut⇒R⇒Lcases++   !} , 
--             --   ⇒R (cutaxA-left [] (cut [] (⇒L {[]} (MIP.g (mip [] Ω₂ Ω₁ f refl)) (MIP.h (mip Γ₁ (B ∷ Ω₀) (E ∷ Ω ++ B' ∷ Ξ) g refl))) ax refl) refl 
--             --   ∘ (cutaxA-right _))) refl)

-- mip≗ Γ ._ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f' = f'} {g}) | inj₂ (E₁ , Ω , refl , refl) | inj₁ (Ω₀ , refl , refl) | inj₂ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₀) (Γ ++ E ∷ Ω₂) (E₁ ∷ Ω ++ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ Ω₀ (E₁ ∷ Ω ++ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ Ω₀ (A ⇒ B) |
--           ++?-inj₂ Γ Ω₂ Δ₀ E |
--           ++?-inj₁ (Δ₀ ++ A ⇒ B ∷ Ω₀) (Γ ++ E ∷ Ω₂) (E₁ ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₁ Δ₀ Ω₀ (E₁ ∷ Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           cases++-inj₂ (E ∷ Ω₂ ++ Δ₀) Γ Ω₀ (A ⇒ B) |
--           ++?-inj₂ Γ Ω₂ Δ₀ E |
--           ++?-inj₂ (Γ ++ E ∷ Ω₂ ++ B ∷ Ω₀) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) E₁ 
--             = intrp≗ (↝∷ (ax , (~ cutaxA-left Γ (⇒L {Γ ++ _ ∷ E₁ ∷ Ω} f' (MIP.g (mip Γ (E ∷ Ω₂ ++ B ∷ Ω₀) (E₁ ∷ Ω ++ B' ∷ Ξ) g refl))) refl) , cutaxA-right _) refl)

-- mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₂ (E , Ω , eq₁ , refl) | inj₂ (Ω₀ , eq₂ , eq₃) with ++? (Γ ++ Δ) Γ₁ Ω₀ Δ₀ eq₃
-- ... | inj₁ (Ω₁ , refl , eq₅) with ++? Γ₁ Γ Ω₁ Δ eq₅
-- mip≗ Γ Δ ._ refl (⇒L⇒L-comm {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g}) | inj₂ (E , Ω , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ Ω₁ (Γ ++ Ω₂) (A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
--           ++?-inj₁ Ω₁ (Γ ++ Ω₂) (A ⇒ B ∷ Ω ++ B' ∷ Ξ) |
--           cases++-inj₂ [] Ω₁ (Ω ++ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ Ω₁ |
--           cases++-inj₂ [] Ω₁ (Ω ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ Ω₁ |
--           ++?-inj₂ (Γ ++ Ω₂) Ω (Δ₁ ++ A' ⇒ B' ∷ Ξ) B 
--             = intrp≗ (↝∷ (ax , (⊗L ⇒L⇒L-comm ∘ ⊗L⇒L-comm₁) ∘ (~ cutaxA-left Γ _ refl) , refl) refl)
            
--             -- intrp≗ (↝∷ (ax , 
--             --   (⊗L ((⇒L⇒L-comm ∘ ⇒L refl (((~ cutaxA-left (Γ ++ MIP.D (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl) ∷ []) _ refl) 
--             --   ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl) ∷ []) ax (⇒L {Γ ++ _ ∷ []} (MIP.g (mip [] Ω₁ [] f refl)) (MIP.g (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl))) refl) refl)) 
--             --   ∘ (≡to≗ (cut⊗R⊗Lcases++ Γ (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) 
--             --     {f = ax} {ax} {(⇒L {Γ ++ _ ∷ []} (MIP.g (mip [] Ω₁ [] f refl)) (MIP.g (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl)))})))) 
--             --   ∘ (~ (≡to≗ (cut⇒L-cases++-comm₂ Γ (A ⇒ B ∷ Λ₁))))) 
--             --   ∘ (~ cut⊗L≗ Γ [] [] (⊗R ax ax) 
--             --     (⇒L {Γ ++ _ ∷ A ⇒ B ∷ Λ₁} f' (⊗L (⇒L {Γ ++ _ ∷ []} (MIP.g (mip [] Ω₁ [] f refl)) (MIP.g (mip Γ Ω₂ (B ∷ Λ₁ ++ B' ∷ Ξ) g refl))))) refl)) , 
--             --   ⊗R (cutaxA-right _) (cutaxA-right _)) refl)

-- mip≗ Γ Δ ._ refl (⇒L⇒L-comm {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'} {f = f} {f'} {g}) | inj₂ (E , Ω , refl , refl) | inj₂ (F ∷ Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₁ (Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ Ω₁ (Γ ++ Ω₂) (F ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) |
--           cases++-inj₂ (F ∷ Ω₀) Ω₁ (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ Ω₁ |
--           ++?-inj₁ Ω₁ (Γ ++ Ω₂) (F ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ (F ∷ Ω₀) Ω₁ (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₁ Ω₂ Γ Ω₁ |
--           ++?-inj₂ (Γ ++ Ω₂) Λ₁ (Δ₁ ++ A' ⇒ B' ∷ Ξ) B
--             = intrp≗ (↝∷ (ax , (⊗L ⇒L⇒L-comm ∘ ⊗L⇒L-comm₁) ∘ (~ cutaxA-left Γ _ refl) , refl) refl)
            
-- mip≗ Γ Δ ._ refl (⇒L⇒L-comm {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₂ (E₁ , Λ₁ , refl , refl) | inj₂ ([] , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) |
--           cases++-inj₂ [] (Ω₂ ++ Δ) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₂ Γ₁ Ω₂ Δ E | 
--           ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ [] (Ω₂ ++ Δ) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₂ Γ₁ Ω₂ Δ E = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ E ∷ Ω₂) _ refl)) , cutaxA-right _) refl)
--           -- intrp context in f : E ∷ Ω₂ ++ Δ ⊢ A 

-- mip≗ Γ Δ ._ refl (⇒L⇒L-comm {Γ₁} {._} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₂ (E₀ , Ω , refl , refl) | inj₂ (E₁ ∷ Ω₀ , refl , refl) | inj₁ (Ω₁ , refl , refl) | inj₂ (E , Ω₂ , refl , refl) 
--   rewrite ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (E₁ ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) |
--           cases++-inj₂ (E₁ ∷ Ω₀) (Ω₂ ++ Δ) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₂ Γ₁ Ω₂ Δ E |
--           ++?-inj₁ (E ∷ Ω₂ ++ Δ) Γ₁ (E₁ ∷ Ω₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) |
--           cases++-inj₂ (E₁ ∷ Ω₀) (Ω₂ ++ Δ) (Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) (A ⇒ B) |
--           ++?-inj₂ Γ₁ Ω₂ Δ E = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left (Γ₁ ++ E ∷ Ω₂) _ refl)) , cutaxA-right _) refl)
--   --         -- same as the case above, not yet know if this can be optimized. 
--   --         -- We need another with function if we don't pattern-match on Ω₀

-- mip≗ Γ Δ ._ refl (⇒L⇒L-comm {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A = A} {B} {A'} {B'}) | inj₂ (E₁ , Ω , refl , refl) | inj₂ (Ω₀ , refl , refl) | inj₂ (E , Ω₁ , refl , refl) 
--   rewrite ++?-inj₂ (Γ ++ Δ) Ω₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
--           ++?-inj₂ (Γ ++ Δ) Ω₁ (Δ₀ ++ A ⇒ B ∷ Λ₁ ++ Δ₁ ++ A' ⇒ B' ∷ Ξ) E |
--           ++?-inj₂ (Γ ++ Δ) (Ω₁ ++ B ∷ Λ₁) (Δ₁ ++ A' ⇒ B' ∷ Ξ) E 
--             = intrp≗ (↝∷ (ax , (⇒L⇒L-comm ∘ (~ cutaxA-left Γ _ refl))  , cutaxA-right _) refl)
--             -- intrp context in g : Γ ++ Δ ++ E ∷ Ω₁ ++ B ∷ Λ₁ ++ B' ∷ Ξ ⊢ C, where its Γ splits

mip≗ Γ Δ Λ eq (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} p p₁) = {!   !}
-- with ++? (Γ ++ Δ) Γ₁ Λ (Δ₁ ++ A ⇒ B ∷ Λ₁) eq
-- ... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω Λ₁ Λ (sym eq₁)
-- mip≗ Γ Δ Λ eq (⇒L {Γ₁} {Δ₁} p p₁) | inj₁ (Ω , refl , eq₂) | inj₁ (Ω' , refl , refl) with cases++ (Γ₁ ++ Δ₁) Γ Ω' Δ eq₂
-- mip≗ Γ Δ Λ refl (⇒L {Γ₁} {_} {._} {A} {B} p p₁) | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) with mip≗ (Γ₁ ++ B ∷ Ω'') Δ Λ refl p₁
-- ... | intrp≗ eq = intrp≗ (⇒L~Γ eq p) -- B in Γ
-- mip≗ Γ Δ Λ eq (⇒L {Γ₁} {Δ₁} p p₁) | inj₁ (Ω , refl , eq₂) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq₄) with ++? Γ Γ₁ Ω'' Δ₁ eq₄
-- mip≗ Γ ._ Λ refl (⇒L {Γ₁} {_} {._} {A} {B} p p₁) | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) with mip≗ [] Ω''' Ω'' refl p | mip≗ Γ₁ (B ∷ Ω') Λ refl p₁
-- ... | intrp≗ eq | intrp≗ eq₁ = intrp≗ (⇒L~⇒ eq eq₁) -- principal ⇒ 
-- mip≗ Γ ._ Λ refl (⇒L {B = B} p p₁) | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₂ (E , Ω''' , refl , refl) with mip≗ Γ (E ∷ Ω''' ++ B ∷ Ω') Λ refl p₁ 
-- ... | intrp≗ eq = intrp≗ (⇒L~ΓΛ eq p) -- both Γ₁ and Λ₁ split
-- mip≗ Γ Δ Λ eq (⇒L {Γ₁} p p₁) | inj₁ (Ω , refl , eq₂) | inj₂ (Ω' , refl , refl) with ++? Γ₁ Γ Ω Δ eq₂
-- mip≗ Γ Δ ._ refl (⇒L {_} {._} {Λ₁} {A} {B} p p₁) | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) with mip≗ [] Ω Ω' refl p | mip≗ Γ Ω'' (B ∷ Λ₁) refl p₁
-- ... | intrp≗ eq | intrp≗ eq₁ = intrp≗ (⇒L~⊗ eq eq₁) -- principal ⊗
-- mip≗ Γ Δ ._ refl (⇒L p p₁) | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) | inj₂ (E , Ω'' , refl , refl) with mip≗ (E ∷ Ω'') Δ Ω' refl p
-- ... | intrp≗ eq = intrp≗ (⇒L~Δ eq p₁)
-- mip≗ Γ Δ Λ refl (⇒L {Λ = Λ₁} {A} {B} p p₁) | inj₂ (E , Ω , refl , refl) with mip≗ Γ Δ (E ∷ Ω ++ B ∷ Λ₁) refl p₁
-- ... | intrp≗ eq = intrp≗ (⇒L~Λ eq p) 

mip≗ Γ Δ Λ eq (⊗R {Γ₁} {Δ₁} p p₁) = {!   !}
-- with ++? (Γ ++ Δ) Γ₁ Λ Δ₁ eq
-- ... | inj₁ (Ω , refl , eq₂) with ++? Γ₁ Γ Ω Δ eq₂
-- mip≗ Γ Δ Λ refl (⊗R {_} {._} p p₁) | inj₁ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) with mip≗ Γ Ω' [] refl p | mip≗ [] Ω Λ refl p₁
-- ... | intrp≗ eq | intrp≗ eq₁ = intrp≗ (⊗R~ eq eq₁)
-- mip≗ Γ Δ Λ refl (⊗R {Γ₁} {._} p p₁) | inj₁ (Ω , refl , refl) | inj₂ (E , Ω' , refl , refl) with mip≗ (E ∷ Ω') Δ Λ refl p₁
-- ... | intrp≗ eq = intrp≗ (⊗R~₂ eq p)
-- mip≗ Γ Δ Λ refl (⊗R {Γ₁} {Δ₁} p p₁) | inj₂ (E , Ω , refl , refl) with mip≗ Γ Δ (E ∷ Ω) refl p
-- ... | intrp≗ eq = intrp≗ (⊗R~₁ eq p₁) 

mip≗ Γ Δ Λ eq (⊗L {Γ₁} {Δ₁} p) = {!   !}
-- with cases++ Γ₁ Γ Δ₁ (Δ ++ Λ) (sym eq)
-- mip≗ Γ Δ Λ refl (⊗L {Γ₁} {Δ₁} p) | inj₁ (Ω , refl , refl) with mip≗ (Γ₁ ++ _ ∷ _ ∷ Ω) Δ Λ refl p
-- ... | intrp≗ eq = intrp≗ (⊗L~Γ eq)
-- mip≗ Γ Δ Λ eq (⊗L {Γ₁} {Δ₁} p) | inj₂ (Ω , eq₁ , refl) with cases++ Ω Δ Δ₁ Λ eq₁
-- mip≗ Γ Δ Λ refl (⊗L {.(Γ ++ Ω)} {_} p) | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) with mip≗ Γ (Ω ++ _ ∷ _ ∷ Ω') Λ refl p
-- ... | intrp≗ eq = intrp≗ (⊗L~Δ eq)
-- mip≗ Γ Δ Λ refl (⊗L {._} {Δ₁} {f = f} {f'} p) | inj₂ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) with mip≗ Γ Δ (Ω' ++ _ ∷ _ ∷ Δ₁) refl p
-- ... | intrp≗ eq = intrp≗ (⊗L~Λ eq)

mip≗ Γ Δ Λ eq (⊗L⇒R {Γ₁} {Δ₁} ) = {!   !}
-- with cases++ Γ₁ Γ Δ₁ (Δ ++ Λ) (sym eq)
-- mip≗ Γ Δ Λ refl (⊗L⇒R {Γ₁} {A = A} {B} {A'} {f = f}) | inj₁ (Ω , refl , refl) 
--   rewrite cases++-inj₁ Γ₁ Ω (Δ ++ Λ) (A ⊗ B) 
--             = intrp≗ (↜∷ (ax , ((~ ⊗L⇒R) 
--               ∘ (~ cutaxA-left (Γ₁ ++ A ⊗ B ∷ Ω) (⊗L (⇒R (MIP.g (mip (A' ∷ Γ₁ ++ A ∷ B ∷ Ω) Δ Λ f refl)))) refl)) , cutaxA-right _) refl)
-- ... | inj₂ (Ω , eq₁ , refl) with cases++ Ω Δ Δ₁ Λ eq₁
-- mip≗ Γ Δ Λ refl (⊗L⇒R {._} {_} {A} {B} {A'} {f = f}) | inj₂ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) 
--   rewrite cases++-inj₂ Ω Γ (Ω' ++ Λ) (A ⊗ B) |
--           cases++-inj₁ Ω Ω' Λ (A ⊗ B) 
--             = intrp≗ (↜∷ (ax , ⇒R (~ cutaxA-left (_ ∷ Γ) (MIP.g (mip (A' ∷ Γ) (Ω ++ A ∷ B ∷ Ω') Λ f refl)) refl) , cutaxA-right _) refl)
-- mip≗ Γ Δ Λ refl (⊗L⇒R {._} {Δ₁} {A} {B} {A'} {f = f}) | inj₂ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) 
--   rewrite cases++-inj₂ (Δ ++ Ω') Γ Δ₁ (A ⊗ B) |
--           cases++-inj₂ Ω' Δ Δ₁ (A ⊗ B) 
--             = intrp≗ (↜∷ (ax , ((~ ⊗L⇒R {Γ ++ _ ∷ Ω' }) 
--               ∘ (~ cutaxA-left Γ (⊗L {Γ ++ _ ∷ Ω'} (⇒R (MIP.g (mip (A' ∷ Γ) Δ (Ω' ++ A ∷ B ∷ Δ₁) f refl)))) refl)) , cutaxA-right _) refl)
            -- -- alternative proof
            -- -- (↝∷ (ax , (⊗L⇒R {Γ ++ (MIP.D (mip (A' ∷ Γ) Δ (Ω' ++ A ∷ B ∷ Δ₁) f refl)) ∷ Ω' }
            -- --   ∘ ⇒R (~ cutaxA-left (A' ∷ Γ) (⊗L (MIP.g (mip (A' ∷ Γ) Δ (Ω' ++ A ∷ B ∷ Δ₁) f refl))) refl)) , cutaxA-right _) refl)

mip≗ Γ Δ Λ refl refl = intrp≗ refl
mip≗ Γ Δ Λ refl (~ p) with mip≗ Γ Δ Λ refl p 
... | intrp≗ eq = intrp≗ (~-sym eq)  
mip≗ Γ Δ Λ refl (p ∘ p₁) with mip≗ Γ Δ Λ refl p | mip≗ Γ Δ Λ refl p₁
... | intrp≗ eq | intrp≗ eq₁ = intrp≗ (~-trans eq eq₁)
mip≗ Γ Δ Λ refl (⇒R {f = f} {f'} p) with mip (_ ∷ Γ) Δ Λ f refl | mip (_ ∷ Γ) Δ Λ f' refl | mip≗ (_ ∷ Γ) Δ Λ refl p
... | intrp D g h | intrp D' g' h' | intrp≗ eq = intrp≗ (⇒R~ eq)

                 