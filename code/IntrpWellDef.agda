{-# OPTIONS --rewriting --allow-unsolved-metas #-}

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
open import IntrpWellDefCases.Base using (MIP≗; intrp≗)
open import IntrpWellDefCases
{-
Maehara interpolation procedure is well-defined wrt. ≗
-}

mip≗ : ∀ Γ Δ Λ {Ω} {C}
  → {f f' : Ω ⊢ C}
  → (eq : Ω ≡ Γ ++ Δ ++ Λ)
  → (p : f ≗ f')
  → MIP≗ Γ Δ Λ C (mip Γ Δ Λ f eq) (mip Γ Δ Λ f' eq)

mip≗ Γ [] Λ refl p = intrp≗ (g~ (IL {Γ} {Λ} p))
mip≗ Γ (x ∷ Δ) Λ eq refl = intrp≗ refl
mip≗ Γ (x ∷ Δ) Λ eq (~ p) = intrp≗ (~-sym (MIP≗.eq (mip≗ Γ (x ∷ Δ) Λ eq p)))
mip≗ Γ (x ∷ Δ) Λ eq (p ∘ p') =
  intrp≗ (~-trans (MIP≗.eq (mip≗ Γ (x ∷ Δ) Λ eq p)) (MIP≗.eq (mip≗ Γ (x ∷ Δ) Λ eq p')))

-- IL
mip≗ Γ (x ∷ Δ) Λ eq (IL {Γ₁} {Δ₁} p)
  with ++? Γ Γ₁ (x ∷ Δ ++ Λ) (I ∷ Δ₁) eq
... | inj₁ ([] , refl , refl) =
  intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (MIP≗.eq (mip≗ Γ Δ Λ refl p)))
... | inj₁ (y ∷ Ω , refl , refl) =
  intrp≗ (IL~Γ {Γ₀ = Γ₁} {Γ₁ = Ω} (MIP≗.eq (mip≗ (Γ₁ ++ Ω) (x ∷ Δ) Λ refl p)))
... | inj₂ (E , Ω , refl , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip≗ Γ (x ∷ Δ) Λ refl (IL {._} {Δ₁} p) | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) =
  intrp≗ (IL~Δ {Δ₀ = x ∷ Ω} {Δ₁ = Ω'} (MIP≗.eq (mip≗ Γ (x ∷ Ω ++ Ω') Λ refl p)))
mip≗ Γ (x ∷ Δ) Λ refl (IL {._} {Δ₁} p) | inj₂ (E , Ω , refl , refl) | inj₂ (Ω' , refl , refl) =
  intrp≗ (IL~Λ {Λ₀ = Ω'} {Λ₁ = Δ₁} (MIP≗.eq (mip≗ Γ (x ∷ Δ) (Ω' ++ Δ₁) refl p)))

-- ⇒R
mip≗ Γ (x ∷ Δ) Λ refl (⇒R p) =
  intrp≗ (⇒R~ (MIP≗.eq (mip≗ (_ ∷ Γ) (x ∷ Δ) Λ refl p)))

-- ⇒L
mip≗ Γ (x ∷ Δ) Λ eq (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} p q)
  with ++? Γ (Γ₁ ++ Δ₁) (x ∷ Δ ++ Λ) (A₀ ⇒ B₀ ∷ Λ₁) eq
... | inj₁ ([] , refl , refl) =
  intrp≗ (⇒L~⇒ {Γ = Γ₁} {Δ₀ = Δ₁} {Δ₁ = []} {Λ₀ = Δ} {Λ₁ = Λ}
    (MIP≗.eq (mip≗ [] Δ₁ [] refl p))
    (MIP≗.eq (mip≗ Γ₁ (B₀ ∷ Δ) Λ refl q)))
... | inj₁ (y ∷ Ω , refl , refl) =
  intrp≗ (⇒L~Γ {Γ₀ = Γ₁} {Γ₁ = Ω} (MIP≗.eq (mip≗ (Γ₁ ++ B₀ ∷ Ω) (x ∷ Δ) Λ refl q)) p)
... | inj₂ (E , Ω , eq1 , eq2)
  with cases++ Γ Γ₁ Ω Δ₁ eq1
... | inj₁ (Ω' , refl , refl)
  with cases++ (Ω' ++ Δ₁) Δ Λ₁ Λ (inj∷ eq2 .proj₂)
mip≗ Γ (x ∷ Δ) Λ eq (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} p q) | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
  intrp≗ (⇒L~ΓΛ {Γ₀ = Γ} {Γ₁ = E ∷ Ω'} {Λ₀ = Ω''} {Λ₁ = Λ}
    (MIP≗.eq (mip≗ Γ (E ∷ Ω' ++ B₀ ∷ Ω'') Λ refl q)) p)
... | inj₂ (Ω'' , refl , eq4)
  with ++? Δ Ω' Ω'' Δ₁ eq4
mip≗ Γ (x ∷ Δ) ._ eq (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} p q) | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq4) | inj₁ (Ω''' , refl , refl) =
  intrp≗ (⇒L~⊗ {Γ₀ = Γ} {Γ₁ = E ∷ Ω'} {Δ₀ = Ω'''} {Δ₁ = Ω''} {Λ = Λ₁}
    (MIP≗.eq (mip≗ [] Ω''' Ω'' refl p))
    (MIP≗.eq (mip≗ Γ (E ∷ Ω') (B₀ ∷ Λ₁) refl q)))
mip≗ Γ (x ∷ Δ) ._ eq (⇒L {._} {Δ₁} {Λ₁} {A₀} {B₀} p q) | inj₂ (E , ._ , eq1 , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , eq4) | inj₂ (F , Ω''' , refl , refl) =
  intrp≗ (⇒L~Λ {Γ = Γ} {Λ₀ = F ∷ Ω'''} {Λ₁ = Λ₁}
    (MIP≗.eq (mip≗ Γ (E ∷ Δ) (F ∷ Ω''' ++ B₀ ∷ Λ₁) refl q)) p)
mip≗ Γ (x ∷ Δ) Λ eq (⇒L {Γ₁} {Δ₁} {Λ₁} {A₀} {B₀} p q) | inj₂ (E , Ω , eq1 , eq2) | inj₂ (Ω' , refl , refl)
  with cases++ Ω Δ Λ₁ Λ (inj∷ eq2 .proj₂)
mip≗ .(Γ₁ ++ Ω') (x ∷ Δ) Λ eq (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} p q) | inj₂ (E , Ω , eq1 , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
  intrp≗ (⇒L~⇒ {Γ = Γ₁} {Δ₀ = Ω'} {Δ₁ = E ∷ Ω} {Λ₀ = Ω''} {Λ₁ = Λ}
    (MIP≗.eq (mip≗ [] Ω' (E ∷ Ω) refl p))
    (MIP≗.eq (mip≗ Γ₁ (B₀ ∷ Ω'') Λ refl q)))
mip≗ .(Γ₁ ++ Ω') (x ∷ Δ) Λ eq (⇒L {Γ₁} {._} {Λ₁} {A₀} {B₀} p q) | inj₂ (E , Ω , eq1 , refl) | inj₂ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) =
  intrp≗ (⇒L~Δ {Γ = Ω'} {Γ₁ = Γ₁} (MIP≗.eq (mip≗ Ω' (E ∷ Δ) Ω'' refl p)) q)

-- ⊗R
mip≗ Γ (x ∷ Δ) Λ eq (⊗R {Γ₁} {Δ₁} p q)
  with ++? Γ Γ₁ (x ∷ Δ ++ Λ) Δ₁ eq
... | inj₁ (Ω , refl , refl) =
  intrp≗ (⊗R~₂ {Γ = Ω} {Ω = Γ₁} (MIP≗.eq (mip≗ Ω (x ∷ Δ) Λ refl q)) p)
... | inj₂ (E , Ω , refl , eq2)
  with ++? Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip≗ Γ (x ∷ Δ) Λ refl (⊗R {._} {Δ₁} p q) | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) =
  intrp≗ (⊗R~₁ {Γ = Γ} {Λ = Ω'} (MIP≗.eq (mip≗ Γ (x ∷ Δ) Ω' refl p)) q)
mip≗ Γ (x ∷ Δ) Λ refl (⊗R {._} {._} p q) | inj₂ (E , Ω , refl , refl) | inj₂ (E' , Ω' , refl , refl) =
  intrp≗ (⊗R~ (MIP≗.eq (mip≗ Γ (x ∷ Ω) [] refl p)) (MIP≗.eq (mip≗ [] (E' ∷ Ω') Λ refl q)))

-- ⊗L
mip≗ Γ (x ∷ Δ) Λ eq (⊗L {Γ₁} {Δ₁} {A₀} {B₀} p)
  with ++? Γ Γ₁ (x ∷ Δ ++ Λ) (A₀ ⊗ B₀ ∷ Δ₁) eq
... | inj₁ ([] , refl , refl) =
  intrp≗ (⊗L~Δ {Δ₀ = []} {Δ₁ = Δ} (MIP≗.eq (mip≗ Γ (A₀ ∷ B₀ ∷ Δ) Λ refl p)))
... | inj₁ (y ∷ Ω , refl , refl) =
  intrp≗ (⊗L~Γ {Γ₀ = Γ₁} {Γ₁ = Ω} (MIP≗.eq (mip≗ (Γ₁ ++ A₀ ∷ B₀ ∷ Ω) (x ∷ Δ) Λ refl p)))
... | inj₂ (E , Ω , refl , eq2)
  with cases++ Ω Δ Δ₁ Λ (inj∷ eq2 .proj₂)
mip≗ Γ (x ∷ Δ) Λ refl (⊗L {._} {Δ₁} {A₀} {B₀} p) | inj₂ (E , Ω , refl , refl) | inj₁ (Ω' , refl , refl) =
  intrp≗ (⊗L~Δ {Δ₀ = x ∷ Ω} {Δ₁ = Ω'} (MIP≗.eq (mip≗ Γ (x ∷ Ω ++ A₀ ∷ B₀ ∷ Ω') Λ refl p)))
mip≗ Γ (x ∷ Δ) Λ refl (⊗L {._} {Δ₁} {A₀} {B₀} p) | inj₂ (E , Ω , refl , refl) | inj₂ (Ω' , refl , refl) =
  intrp≗ (⊗L~Λ {Λ₀ = Ω'} {Λ₁ = Δ₁} (MIP≗.eq (mip≗ Γ (x ∷ Δ) (Ω' ++ A₀ ∷ B₀ ∷ Δ₁) refl p)))

-- permutative conversions
mip≗ Γ (E ∷ Δ) Λ eq (⇒L⇒R {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {f = f} {g = g}) =
  mip≗⇒L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (⊗L⇒R {Γ = Γ₁} {Δ = Δ₁} {A} {B} {A'} {B'} {f = f}) =
  mip≗⊗L⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {A'} {B'} {f} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⇒R {Γ = Γ₁} {Δ₁} {A} {B} {f}) =
  mip≗IL⇒R Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {A} {B} {f} eq
mip≗ Γ (E ∷ Δ) Λ eq (⇒L⊗R₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h}) =
  mip≗⇒L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f} {g} {h} eq
mip≗ Γ (E ∷ Δ) Λ eq (⇒L⊗R₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h}) =
  mip≗⇒L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f} {g} {h} eq
mip≗ Γ (E ∷ Δ) Λ eq (⊗L⊗R₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {f = f} {g = g}) =
  mip≗⊗L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (⊗L⊗R₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {f = f} {g = g}) =
  mip≗⊗L⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⊗R₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {f = f} {g = g}) =
  mip≗IL⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {f = f} {g = g} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⊗R₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {f = f} {g = g}) =
  mip≗IL⊗R₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {f = f} {g = g} eq
mip≗ Γ (E ∷ Δ) Λ eq (⊗L⊗L {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {C} {f = f}) =
  mip≗⊗L⊗L Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} eq
mip≗ Γ (E ∷ Δ) Λ eq (ILIL {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {C} {f = f}) =
  mip≗ILIL Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {C} {f} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⊗L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {C} {f = f}) =
  mip≗IL⊗L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} {f} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⊗L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {C} {f = f}) =
  mip≗IL⊗L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} {f} eq
mip≗ Γ (E ∷ Δ) Λ eq (⊗L⇒L-assoc {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {C} {f = f} {g = g}) =
  mip≗⊗L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (⊗L⇒L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g = g}) =
  mip≗⊗L⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g = g}) =
  mip≗⊗L⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⇒L-assoc {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁} {A} {B} {C} {f = f} {g = g}) =
  mip≗IL⇒L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⇒L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {C} {f = f} {g = g}) =
  mip≗IL⇒L-comm₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (IL⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {C} {f = f} {g = g}) =
  mip≗IL⇒L-comm₂ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f} {g} eq
mip≗ Γ (E ∷ Δ) Λ eq (⇒L⇒L-assoc {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ = Δ₀} {Λ₀ = Λ₀} {Λ₁ = Λ₁} {A} {B} {A'} {B'} {C} {f = f} {g = g} {h = h}) =
  mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} {h} eq
mip≗ Γ (E ∷ Δ) Λ eq (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁} {Ξ = Ξ} {A} {B} {A'} {B'} {C} {f = f} {f' = f'} {g = g}) =
  mip≗⇒L⇒L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f} {f'} {g} eq
 
