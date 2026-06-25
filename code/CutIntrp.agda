{-# OPTIONS --rewriting #-}

module CutIntrp where

open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Data.Product

open import SeqCalc
open import Cut
open import CutProperties using
  ( cutIL≗
  ; cut⊗L≗
  ; cut⇒L≗
  ; cut-cong₂
  ; cut⇒L-cases++₁
  ; cut⇒L-cases++-comm₂
  )
open import Mip
open import Utilities

-- cut is the left inverse of mip
cut-intrp : ∀ Γ Δ Λ {Ω} {C : Fma} 
  → (f : Ω ⊢ C) 
  → (eq : Ω ≡ Γ ++ Δ ++ Λ)
  → cut Γ (MIP.h (mip Γ Δ Λ f eq)) (MIP.g (mip Γ Δ Λ f eq)) refl ≗ subst-cxt eq f 

-- Empty middle.
cut-intrp Γ [] Λ f refl 
  rewrite cases++-inj₂ [] Γ Λ I = refl

-- IL.
cut-intrp Γ (A ∷ Δ) Λ (IL {Γ₁} {Δ₁} f) eq
  with ++? Γ Γ₁ (A ∷ Δ ++ Λ) (I ∷ Δ₁) eq

cut-intrp Γ (I ∷ Δ) Λ (IL {Γ} {.(Δ ++ Λ)} f) refl | inj₁ ([] , refl , refl) =
  cutIL≗ Γ [] Δ (MIP.h (mip Γ Δ Λ f refl)) (MIP.g (mip Γ Δ Λ f refl)) refl
  ∘ IL (cut-intrp Γ Δ Λ f refl)

cut-intrp .(Γ₁ ++ I ∷ Ω) (A ∷ Δ) Λ (IL {Γ₁} {.(Ω ++ A ∷ Δ ++ Λ)} f) refl
  | inj₁ (I ∷ Ω , refl , refl)
  rewrite cases++-inj₂ (I ∷ Ω) Γ₁ Λ (MIP.D (mip (Γ₁ ++ Ω) (A ∷ Δ) Λ f refl)) =
  IL (cut-intrp (Γ₁ ++ Ω) (A ∷ Δ) Λ f refl)

... | inj₂ (E , Ω , refl , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)

cut-intrp Γ (A ∷ Δ) Λ (IL {._} {Δ₁} f) refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) =
  cutIL≗ Γ (A ∷ Ω) Ω'
    (MIP.h (mip Γ (A ∷ Ω ++ Ω') Λ f refl))
    (MIP.g (mip Γ (A ∷ Ω ++ Ω') Λ f refl)) refl
  ∘ IL {Γ ++ A ∷ Ω} {Ω' ++ Λ} (cut-intrp Γ (A ∷ Ω ++ Ω') Λ f refl)

cut-intrp Γ (A ∷ Δ) Λ (IL {._} {Δ₁} f) refl | inj₂ (E , Ω , refl , refl) | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₁ Γ Ω' (I ∷ Δ₁) (MIP.D (mip Γ (A ∷ Δ) (Ω' ++ Δ₁) f refl)) =
  IL {Γ ++ A ∷ Δ ++ Ω'} {Δ₁} (cut-intrp Γ (A ∷ Δ) (Ω' ++ Δ₁) f refl)

-- ⊗R.
cut-intrp Γ (A ∷ Δ) Λ (⊗R {Γ₁} {Δ₁} f f₁) eq
  with ++? Γ Γ₁ (A ∷ Δ ++ Λ) Δ₁ eq

cut-intrp .(Γ₁ ++ Ω) (A ∷ Δ) Λ (⊗R {Γ₁} {.(Ω ++ A ∷ Δ ++ Λ)} f f₁) refl
  | inj₁ (Ω , refl , refl)
  rewrite cases++-inj₂ Ω Γ₁ Λ (MIP.D (mip Ω (A ∷ Δ) Λ f₁ refl)) =
  ⊗R refl (cut-intrp Ω (A ∷ Δ) Λ f₁ refl)

... | inj₂ (E , Ω , refl , eq2)
  with ++? Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)

cut-intrp Γ (A ∷ Δ) Λ (⊗R {._} {Δ₁} f f₁) refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl)
  rewrite cases++-inj₁ Γ Ω' Δ₁ (MIP.D (mip Γ (A ∷ Δ) Ω' f refl)) =
  ⊗R (cut-intrp Γ (A ∷ Δ) Ω' f refl) refl

cut-intrp Γ (A ∷ Δ) Λ (⊗R {._} {._} f f₁) refl | inj₂ (E , Ω , refl , refl) | inj₂ (E' , Ω' , refl , refl)
  rewrite cases++-inj₂ [] Γ Λ (MIP.D (mip Γ (A ∷ Ω) [] f refl) ⊗ MIP.D (mip [] (E' ∷ Ω') Λ f₁ refl))
        | cases++-inj₂ [] (Γ ++ MIP.D (mip Γ (A ∷ Ω) [] f refl) ∷ []) Λ (MIP.D (mip [] (E' ∷ Ω') Λ f₁ refl))
        | cases++-inj₁ Γ [] (E' ∷ Ω' ++ Λ) (MIP.D (mip Γ (A ∷ Ω) [] f refl)) =
  ⊗R (cut-intrp Γ (A ∷ Ω) [] f refl) (cut-intrp [] (E' ∷ Ω') Λ f₁ refl)

-- ⊗L.
cut-intrp Γ (A ∷ Δ) Λ (⊗L {Γ₁} {Δ₁} {A₀} {B₀} f) eq
  with ++? Γ Γ₁ (A ∷ Δ ++ Λ) (A₀ ⊗ B₀ ∷ Δ₁) eq

cut-intrp Γ (.(A₀ ⊗ B₀) ∷ Δ) Λ (⊗L {Γ} {.(Δ ++ Λ)} {A₀} {B₀} f) refl
  | inj₁ ([] , refl , refl) =
  cut⊗L≗ Γ [] Δ
    (MIP.h (mip Γ (A₀ ∷ B₀ ∷ Δ) Λ f refl))
    (MIP.g (mip Γ (A₀ ∷ B₀ ∷ Δ) Λ f refl)) refl
  ∘ ⊗L {Γ} {Δ ++ Λ} (cut-intrp Γ (A₀ ∷ B₀ ∷ Δ) Λ f refl)

cut-intrp .(Γ₁ ++ A₀ ⊗ B₀ ∷ Ω) (A ∷ Δ) Λ (⊗L {Γ₁} {.(Ω ++ A ∷ Δ ++ Λ)} {A₀} {B₀} f) refl
  | inj₁ (.(A₀ ⊗ B₀) ∷ Ω , refl , refl)
  rewrite cases++-inj₂ (A₀ ⊗ B₀ ∷ Ω) Γ₁ Λ (MIP.D (mip (Γ₁ ++ A₀ ∷ B₀ ∷ Ω) (A ∷ Δ) Λ f refl)) =
  ⊗L {Γ₁} {Ω ++ A ∷ Δ ++ Λ} (cut-intrp (Γ₁ ++ A₀ ∷ B₀ ∷ Ω) (A ∷ Δ) Λ f refl)

... | inj₂ (E , Ω , refl , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)

cut-intrp Γ (A ∷ Δ) Λ (⊗L {._} {Δ₁} {A₀} {B₀} f) refl | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) =
  cut⊗L≗ Γ (A ∷ Ω) Ω'
    (MIP.h (mip Γ (A ∷ Ω ++ A₀ ∷ B₀ ∷ Ω') Λ f refl))
    (MIP.g (mip Γ (A ∷ Ω ++ A₀ ∷ B₀ ∷ Ω') Λ f refl)) refl
  ∘ ⊗L {Γ ++ A ∷ Ω} {Ω' ++ Λ} (cut-intrp Γ (A ∷ Ω ++ A₀ ∷ B₀ ∷ Ω') Λ f refl)

cut-intrp Γ (A ∷ Δ) Λ (⊗L {._} {Δ₁} {A₀} {B₀} f) refl | inj₂ (E , Ω , refl , refl) | inj₂ (Ω' , refl , refl)
  rewrite cases++-inj₁ Γ Ω' (A₀ ⊗ B₀ ∷ Δ₁) (MIP.D (mip Γ (A ∷ Δ) (Ω' ++ A₀ ∷ B₀ ∷ Δ₁) f refl)) =
  ⊗L {Γ ++ A ∷ Δ ++ Ω'} {Δ₁} (cut-intrp Γ (A ∷ Δ) (Ω' ++ A₀ ∷ B₀ ∷ Δ₁) f refl)

-- ⇒R.
cut-intrp Γ (A ∷ Δ) Λ (⇒R {A = A₀} f) refl =
  ⇒R (cut-intrp (A₀ ∷ Γ) (A ∷ Δ) Λ f refl)

-- ⇒L.
cut-intrp Γ (A ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq
  with ++? Γ (Γ₁ ++ Δ₁) (A ∷ Δ ++ Λ) (A₀ ⇒ B₀ ∷ Λ₁) eq

-- The active formula is the displayed implication.
cut-intrp .(Γ₁ ++ Δ₁) (.(A₀ ⇒ B₀) ∷ Δ) Λ
  (⇒L {Γ₁} {Δ₁} {.(Δ ++ Λ)} {A₀} {B₀} f f₁) refl
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ [] (Γ₁ ++ Δ₁) Λ
    (MIP.D (mip [] Δ₁ [] f refl) ⇒ MIP.D (mip Γ₁ (B₀ ∷ Δ) Λ f₁ refl)) =
  (cut-cong₂ Γ₁ refl
    (cut⇒L≗ Γ₁
      (MIP.g (mip [] Δ₁ [] f refl))
      (MIP.h (mip Γ₁ (B₀ ∷ Δ) Λ f₁ refl))
      (MIP.g (mip Γ₁ (B₀ ∷ Δ) Λ f₁ refl)) refl)
  ∘ ≡to≗ (cut⇒L-cases++₁ [] Γ₁))
  ∘ ⇒L (cut-intrp [] Δ₁ [] f refl) (cut-intrp Γ₁ (B₀ ∷ Δ) Λ f₁ refl)

-- The active formula is to the right of the displayed implication.
cut-intrp .(Γ₁ ++ Δ₁ ++ A₀ ⇒ B₀ ∷ Ω) (A ∷ Δ) Λ
  (⇒L {Γ₁} {Δ₁} {.(Ω ++ A ∷ Δ ++ Λ)} {A₀} {B₀} f f₁) refl
  | inj₁ (.(A₀ ⇒ B₀) ∷ Ω , refl , refl)
  rewrite cases++-inj₂ (A₀ ⇒ B₀ ∷ Ω) (Γ₁ ++ Δ₁) Λ
    (MIP.D (mip (Γ₁ ++ B₀ ∷ Ω) (A ∷ Δ) Λ f₁ refl)) =
  ⇒L refl (cut-intrp (Γ₁ ++ B₀ ∷ Ω) (A ∷ Δ) Λ f₁ refl)

... | inj₂ (E , Ω , eq1 , eq2)
  with cases++ Γ Γ₁ Ω Δ₁ eq1

-- The active formula is in the right premise.
... | inj₁ (Ω' , refl , refl)
  with cases++ (Ω' ++ Δ₁) Δ Λ₁ Λ (inj∷ eq2 .proj₂)

cut-intrp Γ (A ∷ Δ) Λ (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) refl
  | inj₂ (E , .(Ω' ++ Δ₁) , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
  cut⇒L≗ Γ f
    (MIP.h (mip Γ (E ∷ Ω' ++ B₀ ∷ Ω'') Λ f₁ refl))
    (MIP.g (mip Γ (E ∷ Ω' ++ B₀ ∷ Ω'') Λ f₁ refl)) refl
  ∘ ⇒L refl (cut-intrp Γ (E ∷ Ω' ++ B₀ ∷ Ω'') Λ f₁ refl)

... | inj₂ (Ω'' , refl , eq4)
  with ++? Δ Ω' Ω'' Δ₁ eq4

-- Principal tensor case crossing the two premises.
cut-intrp Γ (A ∷ Δ) ._ (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) refl
  | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq4) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₂ [] Γ (Ω'' ++ (A₀ ⇒ B₀) ∷ Λ₁)
    (MIP.D (mip Γ (E ∷ Ω') (B₀ ∷ Λ₁) f₁ refl) ⊗ MIP.D (mip [] Ω''' Ω'' f refl)) =
  (cut-cong₂ Γ refl
    (≡to≗ (cut⇒L-cases++₁ [] (Γ ++ MIP.D (mip Γ (E ∷ Ω') (B₀ ∷ Λ₁) f₁ refl) ∷ [])))
  ∘ ≡to≗ (cut⇒L-cases++-comm₂ Γ []
      {Δ = Ω''' ++ Ω''} {Λ₁ = Λ₁} {Ω = E ∷ Ω'} {A = A₀} {B = B₀}
      {D = MIP.D (mip Γ (E ∷ Ω') (B₀ ∷ Λ₁) f₁ refl)}
      {f = MIP.h (mip Γ (E ∷ Ω') (B₀ ∷ Λ₁) f₁ refl)}
      {g = cut [] (MIP.h (mip [] Ω''' Ω'' f refl)) (MIP.g (mip [] Ω''' Ω'' f refl)) refl}
      {h = MIP.g (mip Γ (E ∷ Ω') (B₀ ∷ Λ₁) f₁ refl)}))
  ∘ ⇒L (cut-intrp [] Ω''' Ω'' f refl) (cut-intrp Γ (E ∷ Ω') (B₀ ∷ Λ₁) f₁ refl)

-- The active formula stays in the right premise.
cut-intrp Γ (A ∷ Δ) ._ (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) refl
  | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq4) | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₁ Γ (F ∷ Ω''' ++ Δ₁) ((A₀ ⇒ B₀) ∷ Λ₁)
            (MIP.D (mip Γ (E ∷ Δ) (F ∷ Ω''' ++ B₀ ∷ Λ₁) f₁ refl))
        | cases++-inj₁ Γ (F ∷ Ω''') Δ₁
            (MIP.D (mip Γ (E ∷ Δ) (F ∷ Ω''' ++ B₀ ∷ Λ₁) f₁ refl)) =
  ⇒L refl (cut-intrp Γ (E ∷ Δ) (F ∷ Ω''' ++ B₀ ∷ Λ₁) f₁ refl)

-- The active formula starts in the left premise.
cut-intrp Γ (A ∷ Δ) Λ (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} f f₁) eq
  | inj₂ (E , Ω , eq1 , eq2) | inj₂ (Ω' , refl , refl)
  with cases++ Ω Δ Λ₁ Λ (inj∷ eq2 .proj₂)

-- Principal implication case from the left premise.
cut-intrp .(Γ₁ ++ Ω') (A ∷ Δ) Λ (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} f f₁) refl
  | inj₂ (E , Ω , eq1 , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl)
  rewrite cases++-inj₂ [] (Γ₁ ++ Ω') Λ
    (MIP.D (mip [] Ω' (E ∷ Ω) f refl) ⇒ MIP.D (mip Γ₁ (B₀ ∷ Ω'') Λ f₁ refl)) =
  (cut-cong₂ Γ₁ refl
    (cut⇒L≗ Γ₁
      (MIP.g (mip [] Ω' (E ∷ Ω) f refl))
      (MIP.h (mip Γ₁ (B₀ ∷ Ω'') Λ f₁ refl))
      (MIP.g (mip Γ₁ (B₀ ∷ Ω'') Λ f₁ refl)) refl)
  ∘ ≡to≗ (cut⇒L-cases++₁ [] Γ₁))
  ∘ ⇒L (cut-intrp [] Ω' (E ∷ Ω) f refl) (cut-intrp Γ₁ (B₀ ∷ Ω'') Λ f₁ refl)

-- All of the active middle is in the left premise.
cut-intrp .(Γ₁ ++ Ω') (A ∷ Δ) Λ (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} f f₁) refl
  | inj₂ (E , Ω , eq1 , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Ω') Ω'' ((A₀ ⇒ B₀) ∷ Λ₁)
            (MIP.D (mip Ω' (E ∷ Δ) Ω'' f refl))
        | cases++-inj₂ Ω' Γ₁ Ω''
            (MIP.D (mip Ω' (E ∷ Δ) Ω'' f refl)) =
  ⇒L (cut-intrp Ω' (E ∷ Δ) Ω'' f refl) refl

-- base cases.
cut-intrp [] (A ∷ []) [] ax refl = refl
cut-intrp (B ∷ Γ) (A ∷ Δ) Λ ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))
cut-intrp Γ (A ∷ Δ) Λ IR eq = ⊥-elim ([]disj∷ Γ eq)
