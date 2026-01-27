{-# OPTIONS --rewriting #-}

module Mip where

open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Data.Product
-- open import Fma
open import SeqCalc
open import Utilities

record MIP (Γ Δ Λ : Cxt) (C : Fma) : Set where
  constructor intrp
  field
    D : Fma
    g : Γ ++ D ∷ Λ ⊢ C
    h : Δ ⊢ D

mip : ∀ Γ Δ Λ {Ω} {C : Fma} (f : Ω ⊢ C) 
  → (eq : Ω ≡ Γ ++ Δ ++ Λ)
  → MIP Γ Δ Λ C
mip Γ Δ Λ (IL {Γ₁} {Δ₁} f) eq with cases++ Γ₁ Γ Δ₁ (Δ ++ Λ) (sym eq)
mip Γ Δ Λ (IL {Γ₁} {Δ₁} f) refl | inj₁ (Ω , refl , refl) = 
  let intrp D g h = mip (Γ₁ ++ Ω) Δ Λ f refl
  in intrp D (IL g) h
... | inj₂ (Ω , eq₁ , refl) with cases++ Ω Δ Δ₁ Λ eq₁
mip Γ Δ Λ (IL {._} {Δ₁} f) refl | inj₂ (Ω , refl , refl) | inj₁ (Θ , refl , refl) = 
  let intrp D g h = mip Γ (Ω ++ Θ) Λ f refl
  in intrp D g (IL h)
mip Γ Δ Λ (IL {._} {Δ₁} f) refl | inj₂ (Ω , refl , refl) | inj₂ (Θ , refl , refl) = 
  let intrp D g h = mip Γ Δ (Θ ++ Δ₁) f refl 
  in intrp D (IL {Γ ++ D ∷ Θ} g) h
mip Γ Δ Λ (⊗R {Γ₁} {Δ₁} f g) eq with ++? (Γ ++ Δ) Γ₁ Λ Δ₁ eq
... | inj₁ (Ω , refl , eq₂) with ++? Γ₁ Γ Ω Δ eq₂
mip Γ Δ Λ (⊗R {._} {._} f g) refl | inj₁ (Ω , refl , refl) | inj₁ (Θ , refl , refl) = 
  let intrp D g' h' = mip Γ Θ [] f refl
      intrp E g'' h'' = mip [] Ω Λ g refl
  in intrp (D ⊗ E) (⊗L (⊗R g' g'')) (⊗R h' h'')
mip Γ Δ Λ (⊗R {Γ₁} {._} f g) refl | inj₁ (Ω , refl , refl) | inj₂ (E , Θ , refl , refl) =
  let intrp D g' h' = mip (E ∷ Θ) Δ Λ g refl
  in intrp D (⊗R f g') h' 
mip Γ Δ Λ (⊗R {Γ₁} {Δ₁} f g) refl | inj₂ (E , Ω , refl , refl) =
  let intrp D g' h' = mip Γ Δ (E ∷ Ω) f refl
  in intrp D (⊗R g' g) h'
mip Γ Δ Λ (⊗L {Γ₁} {Δ₁} f) eq with cases++ Γ₁ Γ Δ₁ (Δ ++ Λ) (sym eq)
mip Γ Δ Λ (⊗L {Γ₁} {Δ₁} f) refl | inj₁ (Ω , refl , refl) =
  let intrp D g h = mip (Γ₁ ++ _ ∷ _ ∷ Ω) Δ Λ f refl
  in intrp D (⊗L g) h
... | inj₂ (Ω , eq₁ , refl) with cases++ Ω Δ Δ₁ Λ eq₁
mip Γ Δ Λ (⊗L {._} {Δ₁} f) refl | inj₂ (Ω , refl , refl) | inj₁ (Θ , refl , refl) = 
  let intrp D g h = mip Γ (Ω ++ _ ∷ _ ∷ Θ) Λ f refl
  in intrp D g (⊗L h)
mip Γ Δ Λ (⊗L {._} {Δ₁} f) refl | inj₂ (Ω , refl , refl) | inj₂ (Θ , refl , refl) =
  let intrp D g h = mip Γ Δ (Θ ++ _ ∷ _ ∷ Δ₁) f refl 
  in intrp D (⊗L {Γ ++ D ∷ Θ} g) h
mip Γ Δ Λ (⇒R f) refl = 
  let intrp D g h = mip (_ ∷ Γ) Δ Λ f refl
  in intrp D (⇒R g) h

mip Γ Δ Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} f g) eq with ++? (Γ ++ Δ) Γ₁ Λ (Δ₁ ++ A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω Λ₁ Λ (sym eq₁)
... | inj₁ (Ω' , refl , refl) with cases++ (Γ₁ ++ Δ₁) Γ Ω' Δ eq₂
mip Γ Δ Λ (⇒L {Γ₁} {Δ₁} {._} {A} {B} f g) refl | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
  let intrp D g' h' = mip (Γ₁ ++ B ∷ Ω'') Δ Λ g refl -- right in g
  in intrp D (⇒L f g') h'
... | inj₂ (Ω'' , refl , eq₄) with ++? Γ Γ₁ Ω'' Δ₁ eq₄
mip Γ ._ Λ (⇒L {Γ₁} {Δ₁} {._} {A} {B} f g) refl | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) = 
  let intrp D g' h' = mip [] Ω''' Ω'' f refl -- principal but ⇒
      intrp E g'' h'' = mip Γ₁ (B ∷ Ω') Λ g refl
  in intrp (D ⇒ E) (⇒L h' g'') (⇒R (⇒L {[]} g' h''))
mip Γ ._ Λ (⇒L {Γ₁} {Δ₁} {._} {A} {B} f g) refl | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₂ (E , Ω''' , refl , refl) = 
  let intrp D g' h' = mip Γ (E ∷ Ω''' ++ B ∷ Ω') Λ g refl -- middle in g
  in intrp D g' (⇒L {E ∷ Ω'''} f h')
mip Γ Δ Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} f g) eq | inj₁ (Ω , eq₁ , eq₂) | inj₂ (Ω' , refl , refl) with ++? Γ₁ Γ Ω Δ eq₂
mip Γ Δ ._ (⇒L {Γ₁} {._} {Λ₁} {A} {B} f g) refl | inj₁ (Ω , eq₁ , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) = 
  let intrp D g' h' = mip [] Ω Ω' f refl -- principal but ⊗
      intrp E g'' h'' = mip Γ Ω'' (B ∷ Λ₁) g refl
  in intrp (E ⊗ D) (⊗L {Γ} (⇒L {Γ ++ E ∷ []} g' g'')) (⊗R h'' h')
mip Γ Δ ._ (⇒L {Γ₁} {._} {Λ₁} {A} {B} f g) refl | inj₁ (Ω , eq₁ , refl) | inj₂ (Ω' , refl , refl) | inj₂ (E , Ω'' , refl , refl) = 
  let intrp D g' h' = mip (E ∷ Ω'') Δ Ω' f refl -- in f
  in intrp D (⇒L g' g) h' 
mip Γ Δ Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} f g) refl | inj₂ (E , Ω , refl , refl) =
  let intrp D g' h' = mip Γ Δ (E ∷ Ω ++ B ∷ Λ₁) g refl -- left in g
  in intrp D (⇒L {Γ ++ mip Γ Δ (E ∷ Ω ++ B ∷ Λ₁) g refl .MIP.D ∷ E ∷ Ω} f g') h'

mip [] [] Λ ax refl = intrp I (IL {[]} ax) IR
mip [] (x ∷ Δ) [] ax refl = intrp x ax ax
mip [] (x ∷ Δ) (x₁ ∷ Λ) ax eq = ⊥-elim ([]disj∷ Δ (inj∷ eq .proj₂))
mip (x ∷ Γ) [] [] ax refl = intrp I (IL {x ∷ []} ax) IR
mip (x ∷ Γ) [] (x₁ ∷ Λ) ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))
mip (x ∷ Γ) (x₁ ∷ Δ) Λ ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))
mip [] [] [] IR refl = intrp I (IL {[]} IR) IR

-- module test {Γ₀ Γ₁ Δ' Δ'' Λ₀ Λ'₁ Λ''₂ : Cxt} {A B A' B' C : Fma} {f : Δ' ++ Δ'' ⊢ A} {f' : Γ₀ ++ B ∷ Λ₀ ⊢ A'} {f'' : Γ₁ ++ B' ∷ Λ'₁ ++ Λ''₂ ⊢ C} where
--   test' : ∀ P → P ≡ mip (Γ₁ ++ Γ₀ ++ Δ') (Δ'' ++ A ⇒ B ∷ Λ₀ ++ A' ⇒ B' ∷ Λ'₁) Λ''₂ (⇒L (⇒L f f') f'') refl
--   test' P 
--     rewrite  ++?-inj₁ (Γ₀ ++ Δ' ++ Δ'' ++ A ⇒ B ∷ Λ₀ ++ A' ⇒ B' ∷ Λ'₁) Γ₁ Λ''₂ |
--              cases++-inj₁ (Γ₀ ++ Δ' ++ Δ'' ++ A ⇒ B ∷ Λ₀) Λ'₁ Λ''₂ (A' ⇒ B') |
--              cases++-inj₂ (Δ'' ++ A ⇒ B ∷ Λ₀) (Γ₁ ++ Γ₀ ++ Δ') Λ'₁  (A' ⇒ B') |
--              ++?-inj₁ (Γ₀ ++ Δ') Γ₁ (Δ'' ++ A ⇒ B ∷ Λ₀) |
--              ++?-inj₁ Δ' Γ₀ (Δ'' ++ A ⇒ B ∷ Λ₀) |
--              cases++-inj₂ Δ'' Δ' Λ₀ (A ⇒ B) = {!   !}

{-
f : Δ ⊢ A 
f' : Γ₀ ++ B ∷ Λ₀ ⊢ A'
f'' : Γ₁ ++ B' ∷ Λ₁ ⊢ C
In general, the critial cases for ⇒L⇒L-assoc can be analyzed as following:
We first check the scope of the interpolant context and we focus on what pattern does the split fit for A' ⇒ B'.
If it is an invariant case, then it is fine, everything goes through.
If it is not, then we check if it is ⊗-case or ⇒-case.
For the ⊗-case, we further check if it contains A ⇒ B or not.
If it does, then the interpolant woulbe be just a ⊗ of f' and f'' and we don't need to induct on f.
If it doesn't, then we know it must be the ⊗-case for f and f' as well, so in the end, the interpolants are 
just assoc-formulae.

For the ⇒-case, we further check if it contains A ⇒ B or not.
If it does, then the interpolant formula is (D' ⊗ D) ⇒ D'' for (⇒L (⇒L f f') f'')
and D ⇒ (D' ⇒ D'') for (⇒L f (⇒L f' f'')), which are equivalent.
If it doesn't, then it must be the ⇒ for f' and f'' and we don't need to induct on f. 

Given Γ , Δ , A ⇒ B , Λ ⊢ C,
⊗-case means that the interpolant context splits Γ and does not contain A ⇒ B, while
⇒-case means that the interpolant context splits Λ and contains A ⇒ B.
For ⇒-case, notice that the interpolant context may split Δ to Δ₀ and Δ₁ and Δ₁ will be in the interpolant context.
However, we will instead apply induction on Δ₀ as the interpolant context, which is the correct case. 
-}

  -- ((mip [] Γ₀ (B ∷ Λ₀) f' refl .MIP.D ⊗ mip [] Δ' Δ'' f refl .MIP.D) ⇒ mip Γ₁ (B' ∷ Λ'₁) Λ''₂ f'' refl .MIP.D)

  -- test'' : ∀ P → P ≡ mip (Γ₁ ++ Γ₀ ++ Δ') (Δ'' ++ A ⇒ B ∷ Λ₀ ++ A' ⇒ B' ∷ Λ'₁) Λ''₂ (⇒L {Γ₁ ++ Γ₀} f (⇒L f' f'')) refl
  -- test'' P
  --   rewrite ++?-inj₁ (Δ' ++ Δ'' ++ A ⇒ B ∷ Λ₀ ++ A' ⇒ B' ∷ Λ'₁) (Γ₁ ++ Γ₀) Λ''₂ |
  --           cases++-inj₁ (Δ' ++ Δ'') (Λ₀ ++ A' ⇒ B' ∷ Λ'₁) Λ''₂ (A ⇒ B) |
  --           cases++-inj₂ Δ'' (Γ₁ ++ Γ₀ ++ Δ') (Λ₀ ++ A' ⇒ B' ∷ Λ'₁) (A ⇒ B) |
  --           ++?-inj₁ Δ' (Γ₁ ++ Γ₀) Δ'' |
  --           ++?-inj₁ (Γ₀ ++ B ∷ Λ₀ ++ A' ⇒ B' ∷ Λ'₁) Γ₁ Λ''₂ |
  --           cases++-inj₁ (Γ₀ ++ B ∷ Λ₀) Λ'₁ Λ''₂ (A' ⇒ B') |
  --           cases++-inj₂ (B ∷ Λ₀) (Γ₁ ++ Γ₀) Λ'₁ (A' ⇒ B') |
  --           ++?-inj₁ Γ₀ Γ₁ (B ∷ Λ₀) = {!   !}

-- (mip [] Δ' Δ'' f refl .MIP.D ⇒(mip [] Γ₀ (B ∷ Λ₀) f' refl .MIP.D ⇒ mip Γ₁ (B' ∷ Λ'₁) Λ''₂ f'' refl .MIP.D))