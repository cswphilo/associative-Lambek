{-# OPTIONS --rewriting #-}

module Cut where


open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Data.Product
-- open import Fma
open import SeqCalc
open import Utilities

cutIL : ∀ {Γ Δ Λ C}
 → (f : Δ ⊢ I) (g : Γ ++ Λ ⊢ C)
 → Γ ++ Δ ++ Λ ⊢ C
cutIL ax g = IL g
cutIL IR g = g
cutIL {Γ₁} {Λ = Λ} (IL {Γ} f) g = IL {Γ₁ ++ Γ} (cutIL {Γ₁} {Λ = Λ} f g)
cutIL {Γ₁} {Λ = Λ} (⊗L {Γ} f) g = ⊗L {Γ₁ ++ Γ} (cutIL {Γ₁} {Λ = Λ} f g)
cutIL {Γ₁} {Λ = Λ} (⇒L {Γ} f f₁) g = ⇒L {Γ₁ ++ Γ} f (cutIL {Γ₁} {Λ = Λ} f₁ g)
-- cutIL {Γ₁} {Λ = Λ} (⇐L {Γ} f f₁) g = ⇐L {Γ₁ ++ Γ} f (cutIL {Γ₁} {Λ = Λ} f₁ g)

cut : (Γ : Cxt) → ∀ {Δ Λ Ω C D}
  → (f : Δ ⊢ D) (g : Ω ⊢ C)
  → (eq : Ω ≡ Γ ++ D ∷ Λ)
  → Γ ++ Δ ++ Λ ⊢ C

-- cutIL' : ∀ {Γ Γ₁ Δ Δ₁ Λ C D}
--  → (Ω : Cxt)
--  → (f : Δ₁ ⊢ D) (g : Ω ++ Γ₁ ++ Δ ⊢ C)
--  → (eq : Γ₁ ++ I ∷ Δ ≡ Γ ++ D ∷ Λ)
--  → Ω ++ Γ ++ Δ₁ ++ Λ ⊢ C
-- cutIL' {[]} {[]} {Δ} Ω f g refl = cutIL {Ω} {Λ = Δ} f g
-- cutIL' {[]} {D ∷ Γ₁} {Δ₁ = Δ₁} Ω f g refl = IL {Ω ++ Δ₁ ++ Γ₁} (cut Ω f g refl)
-- cutIL' {D ∷ Γ} {[]} Ω f g refl = IL {Ω} (cut (Ω ++ Γ) f g refl)
-- cutIL' {D ∷ Γ} {E ∷ Γ₁} Ω f g eq with inj∷ eq
-- ... | refl , eq₁ = cutIL' (Ω ++ D ∷ []) f g eq₁ 

cut⊗L : ∀ {Γ Δ Λ A B C}
 → (f : Δ ⊢ A ⊗ B) (g : Γ ++ A ∷ B ∷ Λ ⊢ C)
 → Γ ++ Δ ++ Λ ⊢ C
cut⊗L ax g = ⊗L g
cut⊗L {Γ₁} (IL {Γ} f) g = IL {Γ₁ ++ Γ} (cut⊗L f g)
cut⊗L {Γ} (⊗R f f₁) g = cut Γ f (cut (Γ ++ _ ∷ []) f₁ g refl) refl
cut⊗L {Γ₁} (⊗L {Γ} f) g = ⊗L {Γ₁ ++ Γ} (cut⊗L f g)
cut⊗L {Γ₁} (⇒L {Γ} f f₁) g = ⇒L {Γ₁ ++ Γ} f (cut⊗L f₁ g)
-- cut⊗L {Γ₁} (⇐L {Γ} f f₁) g = ⇐L {Γ₁ ++ Γ} f (cut⊗L f₁ g)

-- cut⊗L' : ∀ {Γ Γ₁ Δ Δ₁ Λ A B C D}
--  → (Ω : Cxt)
--  → (f : Δ₁ ⊢ D) (g : Ω ++ Γ₁ ++ A ∷ B ∷ Δ ⊢ C)
--  → (eq : Γ₁ ++ A ⊗ B ∷ Δ ≡ Γ ++ D ∷ Λ)
--  → Ω ++ Γ ++ Δ₁ ++ Λ ⊢ C
-- cut⊗L' {[]} {[]} Ω f g refl = cut⊗L f g
-- cut⊗L' {[]} {D ∷ Γ₁} {Δ₁ = Δ₁} Ω f g refl = ⊗L {Ω ++ Δ₁ ++ Γ₁} (cut Ω f g refl)
-- cut⊗L' {D ∷ Γ} {[]} Ω f g refl = ⊗L {Ω} (cut (Ω ++ _ ∷ _ ∷ Γ) f g refl)
-- cut⊗L' {D ∷ Γ} {E ∷ Γ₁} Ω f g eq with inj∷ eq
-- ... | refl , eq₁ = cut⊗L' (Ω ++ D ∷ []) f g eq₁

cut⇒L : ∀ {Γ Δ Λ Ω A B C}
 → (f : Δ ⊢ A ⇒ B)
 → (g : Ω ⊢ A) (h : Γ ++ B ∷ Λ  ⊢ C)
 → Γ ++ Ω ++ Δ ++ Λ ⊢ C
cut⇒L ax g h = ⇒L g h
cut⇒L {Γ₁} {Ω = Ω} (IL {Γ} f) g h = IL {Γ₁ ++ Ω ++ Γ} (cut⇒L f g h)
cut⇒L {Γ₁} {Ω = Ω} (⊗L {Γ} f) g h = ⊗L {Γ₁ ++ Ω ++ Γ} (cut⇒L f g h)
cut⇒L {Γ} (⇒R f) g h = cut Γ g (cut Γ f h refl) refl
cut⇒L {Γ₁} {Ω = Ω} (⇒L {Γ} f f₁) g h = ⇒L {Γ₁ ++ Ω ++ Γ} f (cut⇒L f₁ g h)
-- cut⇒L {Γ₁} {Ω = Ω} (⇐L {Γ} f f₁) g h = ⇐L {Γ₁ ++ Ω ++ Γ} f (cut⇒L f₁ g h)

-- cut⇐L : ∀ {Γ Δ Λ Ω A B C}
--  → (f : Δ ⊢ B ⇐ A)
--  → (g : Ω ⊢ A) (h : Γ ++ B ∷ Λ  ⊢ C)
--  → Γ ++ Δ ++ Ω ++ Λ ⊢ C
-- cut⇐L {Γ₁} (IL {Γ} f) g h = IL {Γ₁ ++ Γ} (cut⇐L f g h)
-- cut⇐L {Γ₁} (⊗L {Γ} f) g h = ⊗L {Γ₁ ++ Γ} (cut⇐L f g h)
-- cut⇐L {Γ} {Δ} (⇐R f) g h = cut (Γ ++ Δ) g (cut Γ f h refl) refl
-- cut⇐L {Γ₁} (⇒L {Γ} f f₁) g h = ⇒L {Γ₁ ++ Γ} f (cut⇐L f₁ g h)
-- cut⇐L {Γ₁} (⇐L {Γ} f f₁) g h = ⇐L {Γ₁ ++ Γ} f (cut⇐L f₁ g h)

cut Γ f IR eq = ⊥-elim ([]disj∷ Γ eq)
-- cutIL' [] f g eq
cut Γ {Λ = Λ} f (IL {Γ₁} {Δ} g) eq with cases++ Γ Γ₁ Λ (I ∷ Δ) eq
cut Γ {Δ'} {Λ = Λ} f (IL {Γ₁} {Δ} g) refl | inj₁ (Ω , refl , refl) = IL {Γ ++ Δ' ++ Ω} {Δ} (cut Γ f g refl)
cut Γ {Λ = Λ} f (IL {Γ₁} {Δ} g) refl | inj₂ ([] , refl , refl) = cutIL {Γ} {Λ = Λ} f g
cut Γ {Λ = Λ} f (IL {Γ₁} {Δ} g) refl | inj₂ (._ ∷ Ω , refl , refl) = 
  IL {Γ₁} (cut (Γ₁ ++ Ω) f g refl)

cut Γ {Λ = Λ} f (⊗R {Γ₁} {Δ} g h) eq with cases++ Γ Γ₁ Λ Δ eq
cut Γ {Λ = Λ} f (⊗R {Γ₁} {Δ} g h) refl | inj₁ (Ω , refl , refl) = ⊗R (cut Γ f g refl) h
cut Γ {Λ = Λ} f (⊗R {Γ₁} {Δ} g h) refl | inj₂ (Ω , refl , refl) = ⊗R g (cut Ω f h refl)

-- cut⊗L' [] f g eq
cut Γ {Λ = Λ} f (⊗L {Γ₁} {Δ} {A} {B} g) eq with cases++ Γ Γ₁ Λ (_ ∷ Δ) eq
cut Γ {Δ'} {Λ = Λ} f (⊗L {Γ₁} {Δ} {A} {B} g) refl | inj₁ (Ω , refl , refl) = 
  ⊗L {Γ ++ Δ' ++ Ω} {Δ} (cut Γ f g refl)
cut Γ {Λ = Λ} f (⊗L {Γ₁} {Δ} {A} {B} g) refl | inj₂ ([] , refl , refl) = cut⊗L f g
cut Γ {Λ = Λ} f (⊗L {Γ₁} {Δ} {A} {B} g) refl | inj₂ (_ ∷ Ω , refl , refl) = 
  ⊗L {Γ₁} (cut (Γ₁ ++ _ ∷ _ ∷ Ω) f g refl)

cut Γ f (⇒R g) refl = ⇒R (cut (_ ∷ Γ) f g refl)
cut Γ {Λ = Λ} f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) eq with cases++ Γ (Γ₁ ++ Δ) Λ (A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , refl) with cases++ Γ Γ₁ Ω Δ eq₁
cut Γ {Δ₁} {Λ} f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₁ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) = 
  ⇒L {Γ ++ Δ₁ ++ Ξ} g (cut Γ f h refl)
cut Γ {Λ = Λ} f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₁ (Ω , refl , refl) | inj₂ (Ξ , refl , refl) = 
  ⇒L (cut Ξ f g refl) h
cut Γ {Λ = Λ} f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₂ ([] , refl , refl) = cut⇒L f g h
cut Γ {Λ = Λ} f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₂ (D ∷ Ω , refl , refl) = 
  ⇒L g (cut (Γ₁ ++ B ∷ Ω) f h refl)

-- cut Γ f (⇐R g) refl = ⇐R (cut Γ f g refl)
-- cut Γ {Λ = Λ} f (⇐L {Γ₁} {Δ} {Λ₁} {A} {B} g h) eq with cases++ Γ Γ₁ Λ (B ⇐ A ∷ Δ ++ Λ₁) eq
-- cut Γ {Δ₁} {Λ} f (⇐L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₁ (Ω , refl , refl) = ⇐L {Γ ++ Δ₁ ++ Ω} g (cut Γ f h refl)
-- cut Γ {Λ = Λ} f (⇐L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₂ ([] , refl , refl) = cut⇐L f g h
-- ... | inj₂ (D ∷ Ω , eq₁ , refl) with cases++ Ω Δ Λ Λ₁ (inj∷ eq₁ .proj₂)
-- cut ._ {Λ = Λ} f (⇐L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₂ (D ∷ Ω , refl , refl) | inj₁ (Ξ , refl , refl) = 
--   ⇐L (cut Ω f g refl) h
-- cut ._ {Λ = Λ} f (⇐L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₂ (D ∷ Ω , refl , refl) | inj₂ (Ξ , refl , refl) = 
--   ⇐L g (cut (Γ₁ ++ B ∷ Ξ) f h refl)
cut [] f ax refl = f
cut (D ∷ Γ) f ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))
  
cutaxA-right : ∀ {Γ A}
    → (f : Γ ⊢ A)
    → cut [] f ax refl ≗ f
cutaxA-right f = refl

cutaxA-left' : (Γ : Cxt) → ∀ {Λ Ω A C}
    → (f : Ω ⊢ C)
    → (eq : Ω ≡ Γ ++ A ∷ Λ)
    → cut Γ ax f eq ≡ subst-cxt eq f
cutaxA-left' Γ IR eq = ⊥-elim ([]disj∷ Γ eq)
cutaxA-left' Γ {Λ} (IL {Γ₁} {Δ} f) eq with cases++ Γ Γ₁ Λ (I ∷ Δ) eq
cutaxA-left' Γ {Λ} (IL {Γ₁} {Δ} f) refl | inj₁ (Ω , refl , refl) = cong (IL {Γ ++ _ ∷ Ω}) (cutaxA-left' Γ f refl)
cutaxA-left' Γ {Λ} (IL {Γ₁} {Δ} f) refl | inj₂ ([] , refl , refl) = refl
cutaxA-left' Γ {Λ} (IL {Γ₁} {Δ} f) refl | inj₂ (_ ∷ Ω , refl , refl) = cong IL (cutaxA-left' (Γ₁ ++ Ω) f refl)
cutaxA-left' Γ {Λ} (⊗R {Γ₁} {Δ} f f₁) eq with cases++ Γ Γ₁ Λ Δ eq
cutaxA-left' Γ {Λ} (⊗R {Γ₁} {Δ} f f₁) refl | inj₁ (Ω , refl , refl) = cong (λ x → ⊗R {Γ ++ _ ∷ Ω} x f₁) (cutaxA-left' Γ f refl)
cutaxA-left' Γ {Λ} (⊗R {Γ₁} {Δ} f f₁) refl | inj₂ (Ω , refl , refl) = cong (λ x → ⊗R f x) (cutaxA-left' Ω f₁ refl)
cutaxA-left' Γ {Λ} (⊗L {Γ₁} {Δ} {A} {B} f) eq with cases++ Γ Γ₁ Λ (A ⊗ B ∷ Δ) eq
cutaxA-left' Γ {Λ} (⊗L {Γ₁} {Δ} {A} {B} f) refl | inj₁ (Ω , refl , refl) = cong (⊗L {Γ ++ _ ∷ Ω}) (cutaxA-left' Γ f refl)
cutaxA-left' Γ {Λ} (⊗L {Γ₁} {Δ} {A} {B} f) refl | inj₂ ([] , refl , refl) = refl
cutaxA-left' Γ {Λ} (⊗L {Γ₁} {Δ} {A} {B} f) refl | inj₂ (_ ∷ Ω , refl , refl) = cong ⊗L (cutaxA-left' (Γ₁ ++ A ∷ B ∷ Ω) f refl)
cutaxA-left' Γ (⇒R f) refl = cong ⇒R (cutaxA-left' (_ ∷ Γ) f refl)
cutaxA-left' Γ {Λ} (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} f g) eq with cases++ Γ (Γ₁ ++ Δ) Λ (A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , refl) with cases++ Γ Γ₁ Ω Δ eq₁
cutaxA-left' Γ {._} (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} f g) refl | inj₁ (Ω , refl , refl) | inj₁ (Ω' , refl , refl) 
  = cong (λ x → ⇒L {Γ ++ _ ∷ Ω'} f x) (cutaxA-left' Γ g refl)
cutaxA-left' Γ {._} (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} f g) refl | inj₁ (Ω , refl , refl) | inj₂ (Ω' , refl , refl) = cong (λ x → ⇒L x g) (cutaxA-left' Ω' f refl)
cutaxA-left' Γ {Λ} (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} f g) refl | inj₂ ([] , refl , refl) = refl
cutaxA-left' Γ {Λ} (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} f g) refl | inj₂ (_ ∷ Ω , refl , refl) = cong (λ x → ⇒L f x) (cutaxA-left' (Γ₁ ++ B ∷ Ω) g refl)
cutaxA-left' [] ax refl = refl
cutaxA-left' (x ∷ Γ) ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))

cutaxA-left : (Γ : Cxt) → ∀ {Λ Ω A C}
    → (f : Ω ⊢ C)
    → (eq : Ω ≡ Γ ++ A ∷ Λ)
    → cut Γ ax f eq ≗ subst-cxt eq f
cutaxA-left Γ f eq = ≡to≗ (cutaxA-left' Γ f eq)

postulate 
  cutIL≗ : (Γ Δ₀ Δ₁ : Cxt) → ∀ {Λ Ω C D}
    → (f : Δ₀ ++ Δ₁ ⊢ D) (g : Ω ⊢ C) (eq : Ω ≡ Γ ++ D ∷ Λ)
    → cut Γ (IL {Δ₀} {Δ₁} f) g eq ≗ IL {Γ ++ Δ₀} {Δ₁ ++ Λ} (cut Γ f g eq)
  cut⊗L≗ : (Γ Δ₀ Δ₁ : Cxt) → ∀ {Λ Ω A B C D} 
    → (f : Δ₀ ++ A ∷ B ∷ Δ₁ ⊢ D) (g : Ω ⊢ C) (eq : Ω ≡ Γ ++ D ∷ Λ ) 
    → cut Γ (⊗L f) g eq ≗ ⊗L {Γ ++ Δ₀} (cut Γ f g eq)
  cut⇒L≗ : (Γ : Cxt) → ∀ {Δ Δ₀ Δ₁ Λ Ω A B C D}
    → (f : Δ ⊢ A) (f₁ : Δ₀ ++ B ∷ Δ₁ ⊢ D)
    → (g : Ω ⊢ C) 
    → (eq : Ω ≡ Γ ++ D ∷ Λ)
    → cut Γ (⇒L f f₁) g eq ≗ ⇒L {Γ ++ Δ₀} f (cut Γ f₁ g eq)
  cut-cong₂ : (Γ : Cxt) → ∀ {Δ Λ Ω C D}
    → {f : Δ ⊢ D} {g g' : Ω ⊢ C}
    → (eq : Ω ≡ Γ ++ D ∷ Λ)
    → (p : g ≗ g')
    → cut Γ f g eq ≗ cut Γ f g' eq