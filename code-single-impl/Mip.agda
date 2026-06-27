{-# OPTIONS --rewriting #-}

module Mip where

open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Data.Product
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

-- IL.
mip Γ (A ∷ Δ) Λ (IL {Γ₁} {Δ₁} f) eq 
  with ++? Γ Γ₁ (A ∷ Δ ++ Λ) (I ∷ Δ₁) eq
... | inj₁ ([] , refl , refl) = 
  let intrp D g h = mip Γ Δ Λ f refl
  in intrp D g (IL {[]} h)
... | inj₁ (B ∷ Ω , refl , refl) = 
  let intrp D g h = mip (Γ₁ ++ Ω) (A ∷ Δ) Λ f refl
  in intrp D (IL g) h
... | inj₂ (E , Ω , refl , eq2) 
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip Γ (A ∷ Δ) Λ (IL {._} {Δ₁} f) refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) = 
  let intrp D g h = mip Γ (A ∷ Ω ++ Ω') Λ f refl
  in intrp D g (IL {_ ∷ Ω} h)
mip Γ (A ∷ Δ) Λ (IL {._} {Δ₁} f) refl | inj₂ (E , Ω , refl , refl) | inj₂ (Ω' , refl , refl) = 
  let intrp D g h = mip Γ (A ∷ Δ) (Ω' ++ Δ₁) f refl
  in intrp D (IL {Γ ++ _ ∷ Ω'} g) h

-- ⊗R.
mip Γ (A ∷ Δ) Λ (⊗R {Γ₁} {Δ₁} f f₁) eq
  with ++? Γ Γ₁ (A ∷ Δ ++ Λ) Δ₁ eq
... | inj₁ (Ω , refl , refl) =
  let intrp D g h = mip Ω (A ∷ Δ) Λ f₁ refl
  in intrp D (⊗R f g) h
... | inj₂ (E , Ω , refl , eq2)
  with ++? Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip Γ (A ∷ Δ) Λ (⊗R {._} {Δ₁} f f₁) refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) =
  let intrp D g h = mip Γ (A ∷ Δ) Ω' f refl
  in intrp D (⊗R g f₁) h
mip Γ (A ∷ Δ) Λ (⊗R {._} {._} f f₁) refl | inj₂ (E , Ω , refl , refl) | inj₂ (E' , Ω' , refl , refl) =
  let intrp D g h = mip Γ (A ∷ Ω) [] f refl
      intrp E₁ g' h' = mip [] (E' ∷ Ω') Λ f₁ refl
  in intrp (D ⊗ E₁) (⊗L {Γ} (⊗R g g')) (⊗R h h')

-- ⊗L.
mip Γ (A ∷ Δ) Λ (⊗L {Γ₁} {Δ₁} {A₀} {B₀} f) eq
  with ++? Γ Γ₁ (A ∷ Δ ++ Λ) (A₀ ⊗ B₀ ∷ Δ₁) eq
... | inj₁ ([] , refl , refl) =
  let intrp D g h = mip Γ (A₀ ∷ B₀ ∷ Δ) Λ f refl
  in intrp D g (⊗L {[]} h)
... | inj₁ (B ∷ Ω , refl , refl) =
  let intrp D g h = mip (Γ₁ ++ A₀ ∷ B₀ ∷ Ω) (A ∷ Δ) Λ f refl
  in intrp D (⊗L g) h
... | inj₂ (E , Ω , refl , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip Γ (A ∷ Δ) Λ (⊗L {._} {Δ₁} {A₀} {B₀} f) refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) =
  let intrp D g h = mip Γ (A ∷ Ω ++ A₀ ∷ B₀ ∷ Ω') Λ f refl
  in intrp D g (⊗L {_ ∷ Ω} h)
mip Γ (A ∷ Δ) Λ (⊗L {._} {Δ₁} {A₀} {B₀} f) refl | inj₂ (E , Ω , refl , refl) | inj₂ (Ω' , refl , refl) =
  let intrp D g h = mip Γ (A ∷ Δ) (Ω' ++ A₀ ∷ B₀ ∷ Δ₁) f refl
  in intrp D (⊗L {Γ ++ _ ∷ Ω'} g) h

-- ⇒R.
mip Γ (A ∷ Δ) Λ (⇒R f) refl =
  let intrp D g h = mip (_ ∷ Γ) (A ∷ Δ) Λ f refl
  in intrp D (⇒R g) h

-- ⇒L.
mip Γ (A ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq 
  with ++? Γ (Γ₁ ++ Δ₁) (A ∷ Δ ++ Λ) (A₀ ⇒ B₀ ∷ Λ₁) eq
... | inj₁ ([] , refl , refl) = 
  let intrp D g h = mip [] Δ₁ [] f refl
      intrp D' g' h' = mip Γ₁ (B₀ ∷ Δ) Λ f₁ refl 
  in intrp (D ⇒ D') (⇒L h g') (⇒R (⇒L {[]} g h'))
... | inj₁ (B ∷ Ω , refl , refl) = 
  let intrp D g h = mip (Γ₁ ++ B₀ ∷ Ω) (A ∷ Δ) Λ f₁ refl
  in intrp D (⇒L f g) h
... | inj₂ (E , Ω , eq1 , eq2) 
  with cases++ Γ Γ₁ Ω Δ₁ eq1
... | inj₁ (Ω' , refl , refl) 
  with cases++ (Ω' ++ Δ₁) Δ Λ₁ Λ (inj∷ eq2 .proj₂)
mip Γ (A ∷ Δ) Λ (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) = 
  let intrp D g h = mip Γ (E ∷ Ω' ++ B₀ ∷ Ω'') Λ f₁ refl
  in intrp D g (⇒L f h)
... | inj₂ (Ω'' , refl , eq4) 
  with ++? Δ Ω' Ω'' Δ₁ eq4
mip Γ (A ∷ Δ) ._ (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq4) | inj₁ (Ω''' , refl , refl) = 
  let intrp D g h = mip [] Ω''' Ω'' f refl
      intrp D' g' h' = mip Γ (E ∷ Ω') (B₀ ∷ Λ₁) f₁ refl
  in intrp (D' ⊗ D) (⊗L (⇒L {_ ++ _ ∷ []} g g')) (⊗R h' h)
mip Γ (A ∷ Δ) ._ (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq4) | inj₂ (F , Ω''' , refl , refl) = 
  let intrp D g h = mip Γ (E ∷ Δ) (F ∷ Ω''' ++ B₀ ∷ Λ₁) f₁ refl
  in intrp D (⇒L {Γ ++ _ ∷ _ ∷ _} f g) h
mip Γ (A ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq | inj₂ (E , Ω , eq1 , eq2) | inj₂ (Ω' , refl , refl) 
  with cases++ Ω Δ Λ₁ Λ (inj∷ eq2 .proj₂)
mip .(Γ₁ ++ Ω') (A ∷ Δ) Λ (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} f f₁) eq | inj₂ (E , Ω , eq1 , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) = 
  let intrp D g h = mip [] Ω' (E ∷ Ω) f refl
      intrp D' g' h' = mip Γ₁ (B₀ ∷ Ω'') Λ f₁ refl
  in intrp (D ⇒ D') (⇒L h g') (⇒R (⇒L {[]} g h'))
mip .(Γ₁ ++ Ω') (A ∷ Δ) Λ (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} f f₁) eq | inj₂ (E , Ω , eq1 , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) = 
  let intrp D g h = mip Ω' (E ∷ Δ) Ω'' f refl
  in intrp D (⇒L g f₁) h

-- Empty and base cases.
mip Γ [] Λ f refl = intrp I (IL f) IR
mip [] (A ∷ []) [] ax refl = intrp A ax ax
mip (B ∷ Γ) (A ∷ Δ) Λ ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))
mip Γ (A ∷ Δ) Λ IR eq = ⊥-elim ([]disj∷ Γ eq)

-- Archived old branch notes and alternatives.
-- Principal implication cases build D ⇒ D'.
-- The cross-premise principal tensor case builds D' ⊗ D.
-- The final ⇒L branch leaves the whole active middle in the left premise.
--   with ++? (Γ ++ A ∷ Δ) Γ₁ Λ (Δ₁ ++ A₀ ⇒ B₀ ∷ Λ₁) eq
-- ... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω Λ₁ Λ (sym eq₁)
-- ... | inj₁ (Ω' , refl , refl) with cases++ (Γ₁ ++ Δ₁) Γ Ω' (A ∷ Δ) eq₂
-- mip Γ (A ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {._} {A₀} {B₀} f f₁) refl | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
--   let intrp D g' h' = mip (Γ₁ ++ B₀ ∷ Ω'') (A ∷ Δ) Λ f₁ refl
--   in intrp D (⇒L f g')
-- ... | inj₂ (Ω'' , eqΔ , eq₄) with ++? Γ Γ₁ Ω'' Δ₁ eq₄
-- mip Γ ._ Λ (⇒L {Γ₁} {Δ₁} {._} {A₀} {B₀} f f₁) eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , eqΔ , eq₄) | inj₁ (Ω''' , refl , refl) =
--   let intrp D g' h' = mip [] Ω''' Ω'' f refl
--       intrp E g'' h'' = mip Γ₁ (B₀ ∷ Ω') Λ f₁ refl
--   in intrp (D ⇒ E) (⇒L h' g'') (subst-cxt (sym eqΔ) (⇒R (⇒L {[]} g' h'')))
-- mip Γ ._ Λ (⇒L {Γ₁} {Δ₁} {._} {A₀} {B₀} f f₁) eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , eqΔ , eq₄) | inj₂ (E , Ω''' , refl , refl) =
--   let intrp D g' h' = mip Γ (E ∷ Ω''' ++ B₀ ∷ Ω') Λ f₁ refl
--   in intrp D g' (subst-cxt (sym eqΔ) (⇒L {E ∷ Ω'''} f h'))
-- mip Γ (A ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq | inj₁ (Ω , eq₁ , eq₂) | inj₂ (Ω' , refl , refl) with ++? Γ₁ Γ Ω (A ∷ Δ) eq₂
-- mip Γ (A ∷ Δ) ._ (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} f f₁) eq | inj₁ (Ω , eq₁ , eq₂) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , eqΔ , refl) =
--   let intrp D g' h' = mip [] Ω Ω' f refl
--       intrp E g'' h'' = mip Γ Ω'' (B₀ ∷ Λ₁) f₁ refl
--   in intrp (E ⊗ D) (⊗L {Γ} (⇒L {Γ ++ E ∷ []} g' g'')) (subst-cxt (sym eqΔ) (⊗R h'' h'))
-- mip Γ (A ∷ Δ) ._ (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} f f₁) refl | inj₁ (Ω , eq₁ , refl) | inj₂ (Ω' , refl , refl) | inj₂ (E , Ω'' , refl , refl) =
--   let intrp D g' h' = mip (E ∷ Ω'') (A ∷ Δ) Ω' f refl
--   in intrp D (⇒L g' f₁)
-- mip Γ (A ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) refl | inj₂ (E , Ω , refl , refl) =
--   let intrp D g' h' = mip Γ (A ∷ Δ) (E ∷ Ω ++ B₀ ∷ Λ₁) f₁ refl
--   in intrp D (⇒L {Γ ++ D ∷ E ∷ Ω} f g') h'
-- mip Γ [] Λ f eq = intrp I (IL {Γ} {Λ} (subst-cxt eq f)) IR
-- mip Γ (x ∷ Δ) Λ (IL {Γ₁} {Δ₁} f) eq with cases++ Γ₁ Γ Δ₁ (x ∷ Δ ++ Λ) (sym eq)
-- mip Γ (x ∷ Δ) Λ (IL {Γ₁} {Δ₁} f) refl | inj₁ (Ω , refl , refl) = 
--   let intrp D g h = mip (Γ₁ ++ Ω) (x ∷ Δ) Λ f refl
--   in intrp D (IL g) h
-- ... | inj₂ (Ω , eq₁ , refl) with cases++ Ω (x ∷ Δ) Δ₁ Λ eq₁
-- mip Γ (x ∷ Δ) Λ (IL {._} {Δ₁} f) eq | inj₂ (Ω , eq₁ , refl) | inj₁ (Θ , eqΔ , refl) = {!   !}
--   -- let intrp D g h = mip Γ (Ω ++ Θ) Λ f refl
--   -- in intrp D g (subst-cxt (sym eqΔ) (IL h))
-- mip Γ (x ∷ Δ) Λ (IL {._} {Δ₁} f) eq | inj₂ (Ω , eq₁ , refl) | inj₂ (Θ , refl , refl) = 
--   let intrp D g h = mip Γ (x ∷ Δ) (Θ ++ Δ₁) f refl 
--   in intrp D (IL {Γ ++ D ∷ Θ} g) h
-- mip Γ (x ∷ Δ) Λ (⊗R {Γ₁} {Δ₁} f g) eq with ++? (Γ ++ x ∷ Δ) Γ₁ Λ Δ₁ eq
-- ... | inj₁ (Ω , refl , eq₂) with ++? Γ₁ Γ Ω (x ∷ Δ) eq₂
-- mip Γ (x ∷ Δ) Λ (⊗R {._} {._} f g) eq | inj₁ (Ω , refl , eq₂) | inj₁ (Θ , eqΔ , refl) = 
--   let intrp D g' h' = mip Γ Θ [] f refl
--       intrp E g'' h'' = mip [] Ω Λ g refl
--   in intrp (D ⊗ E) (⊗L (⊗R g' g'')) (subst-cxt (sym eqΔ) (⊗R h' h''))
-- mip Γ (x ∷ Δ) Λ (⊗R {Γ₁} {._} f g) refl | inj₁ (Ω , refl , refl) | inj₂ (E , Θ , refl , refl) =
--   let intrp D g' h' = mip (E ∷ Θ) (x ∷ Δ) Λ g refl
--   in intrp D (⊗R f g') h' 
-- mip Γ (x ∷ Δ) Λ (⊗R {Γ₁} {Δ₁} f g) refl | inj₂ (E , Ω , refl , refl) =
--   let intrp D g' h' = mip Γ (x ∷ Δ) (E ∷ Ω) f refl
--   in intrp D (⊗R g' g) h'
-- mip Γ (x ∷ Δ) Λ (⊗L {Γ₁} {Δ₁} f) eq with cases++ Γ₁ Γ Δ₁ (x ∷ Δ ++ Λ) (sym eq)
-- mip Γ (x ∷ Δ) Λ (⊗L {Γ₁} {Δ₁} f) refl | inj₁ (Ω , refl , refl) =
--   let intrp D g h = mip (Γ₁ ++ _ ∷ _ ∷ Ω) (x ∷ Δ) Λ f refl
--   in intrp D (⊗L g) h
-- ... | inj₂ (Ω , eq₁ , refl) with cases++ Ω (x ∷ Δ) Δ₁ Λ eq₁
-- mip Γ (x ∷ Δ) Λ (⊗L {._} {Δ₁} f) eq | inj₂ (Ω , eq₁ , refl) | inj₁ (Θ , eqΔ , refl) = 
--   let intrp D g h = mip Γ (Ω ++ _ ∷ _ ∷ Θ) Λ f refl
--   in intrp D g (subst-cxt (sym eqΔ) (⊗L h))
-- mip Γ (x ∷ Δ) Λ (⊗L {._} {Δ₁} f) eq | inj₂ (Ω , eq₁ , refl) | inj₂ (Θ , refl , refl) =
--   let intrp D g h = mip Γ (x ∷ Δ) (Θ ++ _ ∷ _ ∷ Δ₁) f refl 
--   in intrp D (⊗L {Γ ++ D ∷ Θ} g) h
-- mip Γ (x ∷ Δ) Λ (⇒R f) refl = 
--   let intrp D g h = mip (_ ∷ Γ) (x ∷ Δ) Λ f refl
--   in intrp D (⇒R g) h

-- mip Γ (x ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} f g) eq with ++? (Γ ++ x ∷ Δ) Γ₁ Λ (Δ₁ ++ A ⇒ B ∷ Λ₁) eq
-- ... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω Λ₁ Λ (sym eq₁)
-- ... | inj₁ (Ω' , refl , refl) with cases++ (Γ₁ ++ Δ₁) Γ Ω' (x ∷ Δ) eq₂
-- mip Γ (x ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {._} {A} {B} f g) refl | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
--   let intrp D g' h' = mip (Γ₁ ++ B ∷ Ω'') (x ∷ Δ) Λ g refl -- right in g
--   in intrp D (⇒L f g') h'
-- ... | inj₂ (Ω'' , eqΔ , eq₄) with ++? Γ Γ₁ Ω'' Δ₁ eq₄
-- mip Γ ._ Λ (⇒L {Γ₁} {Δ₁} {._} {A} {B} f g) eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , eqΔ , eq₄) | inj₁ (Ω''' , refl , refl) = 
--   let intrp D g' h' = mip [] Ω''' Ω'' f refl -- principal but ⇒
--       intrp E g'' h'' = mip Γ₁ (B ∷ Ω') Λ g refl
--   in intrp (D ⇒ E) (⇒L h' g'') (subst-cxt (sym eqΔ) (⇒R (⇒L {[]} g' h'')))
-- mip Γ ._ Λ (⇒L {Γ₁} {Δ₁} {._} {A} {B} f g) eq | inj₁ (._ , refl , eq₂) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , eqΔ , eq₄) | inj₂ (E , Ω''' , refl , refl) = 
--   let intrp D g' h' = mip Γ (E ∷ Ω''' ++ B ∷ Ω') Λ g refl -- middle in g
--   in intrp D g' (subst-cxt (sym eqΔ) (⇒L {E ∷ Ω'''} f h'))
-- mip Γ (x ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} f g) eq | inj₁ (Ω , eq₁ , eq₂) | inj₂ (Ω' , refl , refl) with ++? Γ₁ Γ Ω (x ∷ Δ) eq₂
-- mip Γ (x ∷ Δ) ._ (⇒L {Γ₁} {._} {Λ₁} {A} {B} f g) eq | inj₁ (Ω , eq₁ , eq₂) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , eqΔ , refl) = 
--   let intrp D g' h' = mip [] Ω Ω' f refl -- principal but ⊗
--       intrp E g'' h'' = mip Γ Ω'' (B ∷ Λ₁) g refl
--   in intrp (E ⊗ D) (⊗L {Γ} (⇒L {Γ ++ E ∷ []} g' g'')) (subst-cxt (sym eqΔ) (⊗R h'' h'))
-- mip Γ (x ∷ Δ) ._ (⇒L {Γ₁} {._} {Λ₁} {A} {B} f g) refl | inj₁ (Ω , eq₁ , refl) | inj₂ (Ω' , refl , refl) | inj₂ (E , Ω'' , refl , refl) = 
--   let intrp D g' h' = mip (E ∷ Ω'') (x ∷ Δ) Ω' f refl -- in f
--   in intrp D (⇒L g' g) h' 
-- mip Γ (x ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} f g) refl | inj₂ (E , Ω , refl , refl) =
--   let intrp D g' h' = mip Γ (x ∷ Δ) (E ∷ Ω ++ B ∷ Λ₁) g refl -- left in g
--   in intrp D (⇒L {Γ ++ mip Γ (x ∷ Δ) (E ∷ Ω ++ B ∷ Λ₁) g refl .MIP.D ∷ E ∷ Ω} f g') h'

-- mip [] (x ∷ Δ) [] ax refl = intrp x ax ax
-- mip [] (x ∷ Δ) (x₁ ∷ Λ) ax eq = ⊥-elim ([]disj∷ Δ (inj∷ eq .proj₂))
-- mip (x ∷ Γ) (x₁ ∷ Δ) Λ ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))
-- mip Γ (x ∷ Δ) Λ IR eq = ⊥-elim ([]disj∷ Γ eq)
