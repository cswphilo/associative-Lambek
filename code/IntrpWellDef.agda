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

mip≗ Γ Δ Λ eq refl = intrp≗ refl
mip≗ Γ Δ Λ eq (~ p) = intrp≗ (~-sym (MIP≗.eq (mip≗ Γ Δ Λ eq p)))
mip≗ Γ Δ Λ eq (p ∘ p') =
  intrp≗ (~-trans (MIP≗.eq (mip≗ Γ Δ Λ eq p)) (MIP≗.eq (mip≗ Γ Δ Λ eq p')))

mip≗ Γ Δ Λ eq (IL {Γ₁} {Δ₁} p) with cases++ Γ₁ Γ Δ₁ (Δ ++ Λ) (sym eq)
mip≗ Γ Δ Λ refl (IL {Γ₁} {Δ₁} p) | inj₁ (Ω , refl , refl) =
  intrp≗ (IL~Γ {Γ₀ = Γ₁} {Γ₁ = Ω} (MIP≗.eq (mip≗ (Γ₁ ++ Ω) Δ Λ refl p)))
... | inj₂ (Ω , eq₁ , refl) with cases++ Ω Δ Δ₁ Λ eq₁
mip≗ Γ Δ Λ (refl) (IL {._} {Δ₁} p) | inj₂ (Ω , refl , refl) | inj₁ (Θ , refl , refl) =
  intrp≗ (IL~Δ {Δ₀ = Ω} {Δ₁ = Θ} (MIP≗.eq (mip≗ Γ (Ω ++ Θ) Λ refl p)))
mip≗ Γ Δ Λ (refl) (IL {._} {Δ₁} p) | inj₂ (Ω , refl , refl) | inj₂ (Θ , refl , refl) =
  intrp≗ (IL~Λ {Λ₀ = Θ} {Λ₁ = Δ₁} (MIP≗.eq (mip≗ Γ Δ (Θ ++ Δ₁) refl p)))

mip≗ Γ Δ Λ refl (⇒R p) =
  intrp≗ (⇒R~ (MIP≗.eq (mip≗ (_ ∷ Γ) Δ Λ refl p)))

mip≗ Γ Δ Λ eq (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} p q)
  with ++? (Γ ++ Δ) Γ₁ Λ (Δ₁ ++ A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , eq₂) with cases++ Δ₁ Ω Λ₁ Λ (sym eq₁)
... | inj₁ (Ω' , refl , refl) with cases++ (Γ₁ ++ Δ₁) Γ Ω' Δ eq₂
mip≗ Γ Δ Λ refl (⇒L {Γ₁} {Δ₁} {._} {A} {B} p q)
  | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
  intrp≗ (⇒L~Γ {Γ₀ = Γ₁} {Γ₁ = Ω''} (MIP≗.eq (mip≗ (Γ₁ ++ B ∷ Ω'') Δ Λ refl q)) p)
... | inj₂ (Ω'' , refl , eq₄) with ++? Γ Γ₁ Ω'' Δ₁ eq₄
mip≗ Γ ._ Λ refl (⇒L {Γ₁} {Δ₁} {._} {A} {B} p q)
  | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) =
  intrp≗ (⇒L~⇒ {Γ = Γ₁} {Δ₀ = Ω'''} {Δ₁ = Ω''} {Λ₀ = Ω'} {Λ₁ = Λ}
    (MIP≗.eq (mip≗ [] Ω''' Ω'' refl p))
    (MIP≗.eq (mip≗ Γ₁ (B ∷ Ω') Λ refl q)))
mip≗ Γ ._ Λ refl (⇒L {Γ₁} {Δ₁} {._} {A} {B} p q)
  | inj₁ (._ , refl , refl) | inj₁ (Ω' , refl , refl) | inj₂ (Ω'' , refl , refl) | inj₂ (E , Ω''' , refl , refl) =
  intrp≗ (⇒L~ΓΛ {Γ₀ = Γ} {Γ₁ = E ∷ Ω'''} {Λ₀ = Ω'} {Λ₁ = Λ}
    (MIP≗.eq (mip≗ Γ (E ∷ Ω''' ++ B ∷ Ω') Λ refl q)) p)
mip≗ Γ Δ Λ eq (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} p q)
  | inj₁ (Ω , eq₁ , eq₂) | inj₂ (Ω' , refl , refl) with ++? Γ₁ Γ Ω Δ eq₂
mip≗ Γ Δ ._ refl (⇒L {Γ₁} {._} {Λ₁} {A} {B} p q)
  | inj₁ (Ω , eq₁ , refl) | inj₂ (Ω' , refl , refl) | inj₁ (Ω'' , refl , refl) =
  intrp≗ (⇒L~⊗ {Γ₀ = Γ} {Γ₁ = Ω''} {Δ₀ = Ω} {Δ₁ = Ω'} {Λ = Λ₁}
    (MIP≗.eq (mip≗ [] Ω Ω' refl p))
    (MIP≗.eq (mip≗ Γ Ω'' (B ∷ Λ₁) refl q)))
mip≗ Γ Δ ._ refl (⇒L {Γ₁} {._} {Λ₁} {A} {B} p q)
  | inj₁ (Ω , eq₁ , refl) | inj₂ (Ω' , refl , refl) | inj₂ (E , Ω'' , refl , refl) =
  intrp≗ (⇒L~Δ {Γ = E ∷ Ω''} {Γ₁ = Γ₁}
    (MIP≗.eq (mip≗ (E ∷ Ω'') Δ Ω' refl p)) q)
mip≗ Γ Δ Λ refl (⇒L {Γ₁} {Δ₁} {Λ₁} {A} {B} p q) | inj₂ (E , Ω , refl , refl) =
  intrp≗ (⇒L~Λ {Γ = Γ} {Λ₀ = E ∷ Ω} {Λ₁ = Λ₁}
    (MIP≗.eq (mip≗ Γ Δ (E ∷ Ω ++ B ∷ Λ₁) refl q)) p)

mip≗ Γ Δ Λ eq (⊗R {Γ₁} {Δ₁} p q) with ++? (Γ ++ Δ) Γ₁ Λ Δ₁ eq
... | inj₁ (Ω , refl , eq₂) with ++? Γ₁ Γ Ω Δ eq₂
mip≗ Γ Δ Λ refl (⊗R {._} {._} p q) | inj₁ (Ω , refl , refl) | inj₁ (Θ , refl , refl) =
  intrp≗ (⊗R~ (MIP≗.eq (mip≗ Γ Θ [] refl p)) (MIP≗.eq (mip≗ [] Ω Λ refl q)))
mip≗ Γ Δ Λ refl (⊗R {Γ₁} {._} p q) | inj₁ (Ω , refl , refl) | inj₂ (E , Θ , refl , refl) =
  intrp≗ (⊗R~₂ {Γ = E ∷ Θ} {Ω = Γ₁} (MIP≗.eq (mip≗ (E ∷ Θ) Δ Λ refl q)) p)
mip≗ Γ Δ Λ refl (⊗R {Γ₁} {Δ₁} p q) | inj₂ (E , Ω , refl , refl) =
  intrp≗ (⊗R~₁ {Γ = Γ} {Λ = E ∷ Ω} (MIP≗.eq (mip≗ Γ Δ (E ∷ Ω) refl p)) q)

mip≗ Γ Δ Λ eq (⊗L {Γ₁} {Δ₁} p) with cases++ Γ₁ Γ Δ₁ (Δ ++ Λ) (sym eq)
mip≗ Γ Δ Λ refl (⊗L {Γ₁} {Δ₁} p) | inj₁ (Ω , refl , refl) =
  intrp≗ (⊗L~Γ {Γ₀ = Γ₁} {Γ₁ = Ω} (MIP≗.eq (mip≗ (Γ₁ ++ _ ∷ _ ∷ Ω) Δ Λ refl p)))
... | inj₂ (Ω , eq₁ , refl) with cases++ Ω Δ Δ₁ Λ eq₁
mip≗ Γ Δ Λ refl (⊗L {._} {Δ₁} p) | inj₂ (Ω , refl , refl) | inj₁ (Θ , refl , refl) =
  intrp≗ (⊗L~Δ {Δ₀ = Ω} {Δ₁ = Θ} (MIP≗.eq (mip≗ Γ (Ω ++ _ ∷ _ ∷ Θ) Λ refl p)))
mip≗ Γ Δ Λ refl (⊗L {._} {Δ₁} p) | inj₂ (Ω , refl , refl) | inj₂ (Θ , refl , refl) =
  intrp≗ (⊗L~Λ {Λ₀ = Θ} {Λ₁ = Δ₁} (MIP≗.eq (mip≗ Γ Δ (Θ ++ _ ∷ _ ∷ Δ₁) refl p)))

mip≗ Γ Δ Λ eq (⇒L⇒R {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {f = f} {g = g}) =
  mip≗⇒L⇒R Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
mip≗ Γ Δ Λ eq (⊗L⇒R {Γ = Γ₁} {Δ = Δ₁} {A} {B} {A'} {B'} {f = f}) =
  mip≗⊗L⇒R Γ Δ Λ {Γ₁} {Δ₁} {A} {B} {A'} {B'} {f} eq
mip≗ Γ Δ Λ eq (⇒L⊗R₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h}) =
  mip≗⇒L⊗R₁ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f} {g} {h} eq
mip≗ Γ Δ Λ eq (⇒L⊗R₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h}) =
  mip≗⇒L⊗R₂ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f} {g} {h} eq
mip≗ Γ Δ Λ eq (⊗L⊗R₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {f = f} {g = g}) =
  mip≗⊗L⊗R₁ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
mip≗ Γ Δ Λ eq (⊗L⊗R₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {f = f} {g = g}) =
  mip≗⊗L⊗R₂ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {f} {g} eq
mip≗ Γ Δ Λ eq (IL⊗R₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {f = f} {g = g}) =
  mip≗IL⊗R₁ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {f = f} {g = g} eq
mip≗ Γ Δ Λ eq (IL⊗R₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {f = f} {g = g}) =
  mip≗IL⊗R₂ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {f = f} {g = g} eq
mip≗ Γ Δ Λ eq (⊗L⊗L {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {C} {f = f}) =
  mip≗⊗L⊗L Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} eq
mip≗ Γ Δ Λ eq (ILIL {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {C} {f = f}) =
  mip≗ILIL Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {C} {f} eq
mip≗ Γ Δ Λ eq (IL⊗L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {C} {f = f}) =
  mip≗IL⊗L-comm₁ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} {f} eq
mip≗ Γ Δ Λ eq (IL⊗L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {A} {B} {C} {f = f}) =
  mip≗IL⊗L-comm₂ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {A} {B} {C} {f} eq
mip≗ Γ Δ Λ eq (⊗L⇒L-assoc {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁} {A} {B} {A'} {B'} {C} {f = f} {g = g}) =
  mip≗⊗L⇒L-assoc Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} eq
mip≗ Γ Δ Λ eq (⊗L⇒L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g = g}) =
  mip≗⊗L⇒L-comm₁ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} eq
mip≗ Γ Δ Λ eq (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {A'} {B'} {C} {f = f} {g = g}) =
  mip≗⊗L⇒L-comm₂ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {C} {f} {g} eq
mip≗ Γ Δ Λ eq (IL⇒L-assoc {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁} {A} {B} {C} {f = f} {g = g}) =
  mip≗IL⇒L-assoc Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} eq
mip≗ Γ Δ Λ eq (IL⇒L-comm₁ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {C} {f = f} {g = g}) =
  mip≗IL⇒L-comm₁ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f} {g} eq
mip≗ Γ Δ Λ eq (IL⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₁} {Λ = Λ₁} {Ω = Ω₁} {A} {B} {C} {f = f} {g = g}) =
  mip≗IL⇒L-comm₂ Γ Δ Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {C} {f} {g} eq
mip≗ Γ Δ Λ eq (⇒L⇒L-assoc {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ = Δ₀} {Λ₀ = Λ₀} {Λ₁ = Λ₁} {A} {B} {A'} {B'} {C} {f = f} {g = g} {h = h}) =
  mip≗⇒L⇒L-assoc Γ Δ Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} {h} eq
mip≗ Γ Δ Λ eq (⇒L⇒L-comm {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁} {Ξ = Ξ} {A} {B} {A'} {B'} {C} {f = f} {f' = f'} {g = g}) =
  mip≗⇒L⇒L-comm Γ Δ Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f} {f'} {g} eq
