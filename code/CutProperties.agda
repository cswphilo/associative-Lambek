{-# OPTIONS --rewriting #-}

module CutProperties where

open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_)
open import Data.Sum
open import Data.Empty
open import Data.Product

open import SeqCalc
open import Cut
open import Utilities

-- Cutting ax.

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

-- Cut commuting with the shape analyses used around interpolation triples.

cutIL-cases++₁ : (Γ₀ Γ₁ Λ : Cxt) → ∀ {Δ C D}
  → {f : Δ ⊢ D} {g : Γ₀ ++ Γ₁ ++ D ∷ Λ ⊢ C}
  → IL {Γ₀} {Γ₁ ++ Δ ++ Λ} (cut (Γ₀ ++ Γ₁) f g refl) ≡ cut (Γ₀ ++ I ∷ Γ₁) f (IL {Γ₀} {Γ₁ ++ D ∷ Λ} g) refl
cutIL-cases++₁ Γ₀ Γ₁ Λ {D = D}
  rewrite cases++-inj₂ (I ∷ Γ₁) Γ₀ Λ D = refl

cutIL-cases++₂ : (Γ Λ₀ Λ₁ : Cxt) → ∀ {Δ C D}
  → {f : Δ ⊢ D} {g : Γ ++ D ∷ Λ₀ ++ Λ₁ ⊢ C}
  → IL {Γ ++ Δ ++ Λ₀} {Λ₁} (cut Γ f g refl) ≡ cut Γ f (IL {Γ ++ D ∷ Λ₀} {Λ₁} g) refl
cutIL-cases++₂ Γ Λ₀ Λ₁ {D = D}
  rewrite cases++-inj₁ Γ Λ₀ (I ∷ Λ₁) D = refl

cut⊗L-cases++₁ : (Γ₀ Γ₁ Λ : Cxt) → ∀ {Δ A B C D}
  → {f : Δ ⊢ D} {g : Γ₀ ++ A ∷ B ∷ Γ₁ ++ D ∷ Λ ⊢ C}
  → ⊗L (cut (Γ₀ ++ A ∷ B ∷ Γ₁) f g refl) ≡ cut (Γ₀ ++ A ⊗ B ∷ Γ₁) f (⊗L g) refl
cut⊗L-cases++₁ Γ₀ Γ₁ Λ {A = A} {B} {D = D}
  rewrite cases++-inj₂ (A ⊗ B ∷ Γ₁) Γ₀ Λ D = refl

cut⊗L-cases++₂ : (Γ Λ₀ Λ₁ : Cxt) → ∀ {Δ A B C D}
  → {f : Δ ⊢ D} {g : Γ ++ D ∷ Λ₀ ++ A ∷ B ∷ Λ₁ ⊢ C}
  → ⊗L {Γ ++ Δ ++ Λ₀} (cut Γ f g refl) ≡ cut Γ f (⊗L {Γ ++ D ∷ Λ₀} g) refl
cut⊗L-cases++₂ Γ Λ₀ Λ₁ {A = A} {B} {D = D}
  rewrite cases++-inj₁ Γ Λ₀ (A ⊗ B ∷ Λ₁) D = refl

cut⊗Rcases++₁ : (Γ Λ Ω : Cxt) → ∀ {Δ A B D}
  → {f : Δ ⊢ D} {g : Γ ++ D ∷ Λ ⊢ A} {h : Ω ⊢ B}
  → ⊗R (cut Γ f g refl) h ≡ cut Γ f (⊗R g h) refl
cut⊗Rcases++₁ Γ Λ Ω {D = D} rewrite cases++-inj₁ Γ Λ Ω D = refl

cut⊗Rcases++₂ : (Γ Λ Ω : Cxt) → ∀ {Δ A B D}
  → {f : Δ ⊢ D} {g : Ω ⊢ A} {h : Γ ++ D ∷ Λ ⊢ B}
  → ⊗R g (cut Γ f h refl) ≡ cut (Ω ++ Γ) f (⊗R g h) refl
cut⊗Rcases++₂ Γ Λ Ω {D = D} rewrite cases++-inj₂ Γ Ω Λ D = refl

cut⊗R⊗Lcases++ : (Γ Λ : Cxt) → ∀ {Δ₀ Δ₁ A B C}
  → {f : Δ₀ ⊢ A} {g : Δ₁ ⊢ B}
  → {h : Γ ++ A ∷ B ∷ Λ ⊢ C}
  → cut Γ f (cut (Γ ++ A ∷ []) g h refl) refl ≡ cut Γ (⊗R f g) (⊗L h) refl
cut⊗R⊗Lcases++ Γ Λ {A = A} {B} rewrite cases++-inj₂ [] Γ Λ (A ⊗ B) = refl

cut⇒L-cases++-comm₁ : (Γ₀ : Cxt) → ∀ {Γ₁ Δ Λ Ω A B C D}
  → {f : Ω ⊢ D}
  → {g : Δ ⊢ A} {h : Γ₀ ++ B ∷ Γ₁ ++ D ∷ Λ ⊢ C}
  → cut (Γ₀ ++ Δ ++ A ⇒ B ∷ Γ₁) f (⇒L g h) refl ≡ ⇒L g (cut (Γ₀ ++ B ∷ Γ₁) f h refl)
cut⇒L-cases++-comm₁ Γ₀ {Γ₁} {Δ} {Λ} {A = A} {B} {D = D}
  rewrite cases++-inj₂ (A ⇒ B ∷ Γ₁) (Γ₀ ++ Δ) Λ D = refl

cut⇒L-cases++₁ : (Γ Γ₁ : Cxt) → ∀ {Λ Λ₁ Ω A B C D}
  → {f : Ω ⊢ D}
  → {g : Γ ++ D ∷ Λ ⊢ A} {h : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → cut (Γ₁ ++ Γ) f (⇒L g h) refl ≡ ⇒L (cut Γ f g refl) h
cut⇒L-cases++₁ Γ Γ₁ {Λ} {Λ₁} {A = A} {B} {D = D}
  rewrite cases++-inj₁ (Γ₁ ++ Γ) Λ (A ⇒ B ∷ Λ₁) D |
          cases++-inj₂ Γ Γ₁ Λ D = refl

cut⇒L-cases++-comm₂ : (Γ Λ₀ : Cxt) → ∀ {Δ Λ₁ Ω A B C D}
  → {f : Ω ⊢ D}
  → {g : Δ ⊢ A} {h : Γ ++ D ∷ Λ₀ ++ B ∷ Λ₁ ⊢ C}
  → cut Γ f (⇒L {Γ ++ D ∷ Λ₀} g h) refl ≡ ⇒L {Γ ++ Ω ++ Λ₀} g (cut Γ f h refl)
cut⇒L-cases++-comm₂ Γ Λ₀ {Δ} {Λ₁} {A = A} {B} {D = D}
  rewrite cases++-inj₁ Γ (Λ₀ ++ Δ) (A ⇒ B ∷ Λ₁) D |
          cases++-inj₁ Γ Λ₀ Δ D = refl

cut⇒R⇒Lcases++ : (Γ Λ Ω : Cxt) → ∀ {Δ A B C}
  → {f : A ∷ Δ ⊢ B}
  → {g : Ω ⊢ A} {h : Γ ++ B ∷ Λ ⊢ C}
  → cut (Γ ++ Ω) (⇒R f) (⇒L g h) refl ≡ cut Γ g (cut Γ f h refl) refl
cut⇒R⇒Lcases++ Γ Λ Ω {A = A} {B}
  rewrite cases++-inj₂ [] (Γ ++ Ω) Λ (A ⇒ B) = refl

cut⇒L-cases++-assoc : (Γ₀ Γ₁ : Cxt) → ∀ {Λ₀ Λ₁ Ω A B C D}
  → {f : Ω ⊢ D}
  → {g : Γ₀ ++ D ∷ Λ₀ ⊢ A} {h : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → cut (Γ₁ ++ Γ₀) f (⇒L g h) refl ≡ ⇒L (cut Γ₀ f g refl) h
cut⇒L-cases++-assoc Γ₀ Γ₁ {Λ₀ = Λ₀} {Λ₁} {A = A} {B} {D = D}
  rewrite cases++-inj₁ (Γ₁ ++ Γ₀) Λ₀ (A ⇒ B ∷ Λ₁) D |
          cases++-inj₂ Γ₀ Γ₁ Λ₀ D = refl

-- Cut computation principles used by equivalence proofs.

cutIL≗ : (Γ Δ₀ Δ₁ : Cxt) → ∀ {Λ Ω C D}
  → (f : Δ₀ ++ Δ₁ ⊢ D) (g : Ω ⊢ C) (eq : Ω ≡ Γ ++ D ∷ Λ)
  → cut Γ (IL {Δ₀} {Δ₁} f) g eq ≗ IL {Γ ++ Δ₀} {Δ₁ ++ Λ} (cut Γ f g eq)
cutIL≗ Γ Δ₀ Δ₁ f IR eq = ⊥-elim ([]disj∷ Γ eq)
cutIL≗ Γ Δ₀ Δ₁ f (IL {Γ₁} {Δ} g) eq with cases++ Γ Γ₁ _ (I ∷ Δ) eq
cutIL≗ Γ Δ₀ Δ₁ f (IL {Γ₁} {Δ} g) refl | inj₁ (Ω , refl , refl) =
  IL {Γ ++ Δ₀ ++ I ∷ Δ₁ ++ Ω} {Δ} (cutIL≗ Γ Δ₀ Δ₁ f g refl)
  ∘ ILIL {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Ω} {Λ = Δ}
cutIL≗ Γ Δ₀ Δ₁ f (IL {Γ₁} {Δ} g) refl | inj₂ ([] , refl , refl) = refl
cutIL≗ Γ Δ₀ Δ₁ {Λ = Λ} f (IL {Γ₁} {Δ} g) refl | inj₂ (I ∷ Ω , refl , refl) =
  IL {Γ₁} {Ω ++ Δ₀ ++ I ∷ Δ₁ ++ Λ}
    (cutIL≗ (Γ₁ ++ Ω) Δ₀ Δ₁ f g refl)
  ∘ (~ (ILIL {Γ = Γ₁} {Δ = Ω ++ Δ₀} {Λ = Δ₁ ++ Λ}))
cutIL≗ Γ Δ₀ Δ₁ f (⊗R {Γ₁} {Δ} g h) eq with cases++ Γ Γ₁ _ Δ eq
cutIL≗ Γ Δ₀ Δ₁ f (⊗R {Γ₁} {Δ} g h) refl | inj₁ (Ω , refl , refl) =
  ⊗R (cutIL≗ Γ Δ₀ Δ₁ f g refl) refl
  ∘ (~ (IL⊗R₁ {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Ω} {Λ = Δ}))
cutIL≗ Γ Δ₀ Δ₁ {Λ = Λ} f (⊗R {Γ₁} {Δ} g h) refl | inj₂ (Ω , refl , refl) =
  ⊗R refl (cutIL≗ Ω Δ₀ Δ₁ f h refl)
  ∘ (~ (IL⊗R₂ {Γ = Γ₁} {Δ = Ω ++ Δ₀} {Λ = Δ₁ ++ Λ}))
cutIL≗ Γ Δ₀ Δ₁ f (⊗L {Γ₁} {Δ} {A} {B} g) eq with cases++ Γ Γ₁ _ (A ⊗ B ∷ Δ) eq
cutIL≗ Γ Δ₀ Δ₁ f (⊗L {Γ₁} {Δ} {A} {B} g) refl | inj₁ (Ω , refl , refl) =
  ⊗L {Γ ++ Δ₀ ++ I ∷ Δ₁ ++ Ω} {Δ} (cutIL≗ Γ Δ₀ Δ₁ f g refl)
  ∘ (~ (IL⊗L-comm₁ {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Ω} {Λ = Δ}))
cutIL≗ Γ Δ₀ Δ₁ f (⊗L {Γ₁} {Δ} {A} {B} g) refl | inj₂ ([] , refl , refl) = refl
cutIL≗ Γ Δ₀ Δ₁ {Λ = Λ} f (⊗L {Γ₁} {Δ} {A} {B} g) refl | inj₂ (A ⊗ B ∷ Ω , refl , refl) =
  ⊗L {Γ₁} (cutIL≗ (Γ₁ ++ A ∷ B ∷ Ω) Δ₀ Δ₁ f g refl)
  ∘ (~ (IL⊗L-comm₂ {Γ = Γ₁} {Δ = Ω ++ Δ₀} {Λ = Δ₁ ++ Λ}))
cutIL≗ Γ Δ₀ Δ₁ {Λ = Λ} f (⇒R g) refl =
  ⇒R (cutIL≗ (_ ∷ Γ) Δ₀ Δ₁ f g refl)
  ∘ (~ (IL⇒R {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Λ}))
cutIL≗ Γ Δ₀ Δ₁ f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) eq with cases++ Γ (Γ₁ ++ Δ) _ (A ⇒ B ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , refl) with cases++ Γ Γ₁ Ω Δ eq₁
cutIL≗ Γ Δ₀ Δ₁ f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₁ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) =
  ⇒L {Γ ++ Δ₀ ++ I ∷ Δ₁ ++ Ξ} refl (cutIL≗ Γ Δ₀ Δ₁ f h refl)
  ∘ (~ (IL⇒L-comm₁ {Γ = Γ ++ Δ₀} {Λ = Δ₁ ++ Ξ}))
cutIL≗ Γ Δ₀ Δ₁ f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₁ (Ω , refl , refl) | inj₂ (Ξ , refl , refl) =
  ⇒L (cutIL≗ Ξ Δ₀ Δ₁ f g refl) refl
  ∘ (~ (IL⇒L-assoc {Γ = Γ₁} {Δ₀ = Ξ ++ Δ₀} {Δ₁ = Δ₁ ++ Ω}))
cutIL≗ Γ Δ₀ Δ₁ f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₂ ([] , refl , refl) = refl
cutIL≗ Γ Δ₀ Δ₁ {Λ = Λ} f (⇒L {Γ₁} {Δ} {Λ₁} {A} {B} g h) refl | inj₂ (A ⇒ B ∷ Ω , refl , refl) =
  ⇒L refl (cutIL≗ (Γ₁ ++ B ∷ Ω) Δ₀ Δ₁ f h refl)
  ∘ (~ (IL⇒L-comm₂ {Γ = Γ₁} {Δ = Δ} {Λ = Ω ++ Δ₀} {Ω = Δ₁ ++ Λ}))
cutIL≗ [] Δ₀ Δ₁ f ax refl = refl
cutIL≗ (D ∷ Γ) Δ₀ Δ₁ f ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))

cut⊗L≗ : (Γ Δ₀ Δ₁ : Cxt) → ∀ {Λ Ω A B C D}
  → (f : Δ₀ ++ A ∷ B ∷ Δ₁ ⊢ D) (g : Ω ⊢ C) (eq : Ω ≡ Γ ++ D ∷ Λ )
  → cut Γ (⊗L f) g eq ≗ ⊗L {Γ ++ Δ₀} (cut Γ f g eq)
cut⊗L≗ Γ Δ₀ Δ₁ f IR eq = ⊥-elim ([]disj∷ Γ eq)
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (IL {Γ₁} {Δ} g) eq with cases++ Γ Γ₁ _ (I ∷ Δ) eq
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (IL {Γ₁} {Δ} g) refl | inj₁ (Ω , refl , refl) =
  IL {Γ ++ Δ₀ ++ A ⊗ B ∷ Δ₁ ++ Ω} {Δ} (cut⊗L≗ Γ Δ₀ Δ₁ f g refl)
  ∘ IL⊗L-comm₂ {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Ω} {Λ = Δ}
cut⊗L≗ Γ Δ₀ Δ₁ f (IL {Γ₁} {Δ} g) refl | inj₂ ([] , refl , refl) = refl
cut⊗L≗ Γ Δ₀ Δ₁ {Λ = Λ} {A = A} {B} f (IL {Γ₁} {Δ} g) refl | inj₂ (I ∷ Ω , refl , refl) =
  IL {Γ₁} {Ω ++ Δ₀ ++ A ⊗ B ∷ Δ₁ ++ Λ}
    (cut⊗L≗ (Γ₁ ++ Ω) Δ₀ Δ₁ f g refl)
  ∘ IL⊗L-comm₁ {Γ = Γ₁} {Δ = Ω ++ Δ₀} {Λ = Δ₁ ++ Λ}
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (⊗R {Γ₁} {Δ} g h) eq with cases++ Γ Γ₁ _ Δ eq
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (⊗R {Γ₁} {Δ} g h) refl | inj₁ (Ω , refl , refl) =
  ⊗R (cut⊗L≗ Γ Δ₀ Δ₁ f g refl) refl
  ∘ (~ (⊗L⊗R₁ {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Ω} {Λ = Δ}))
cut⊗L≗ Γ Δ₀ Δ₁ {Λ = Λ} {A = A} {B} f (⊗R {Γ₁} {Δ} g h) refl | inj₂ (Ω , refl , refl) =
  ⊗R refl (cut⊗L≗ Ω Δ₀ Δ₁ f h refl)
  ∘ (~ (⊗L⊗R₂ {Γ = Γ₁} {Δ = Ω ++ Δ₀} {Λ = Δ₁ ++ Λ}))
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (⊗L {Γ₁} {Δ} {A'} {B'} g) eq with cases++ Γ Γ₁ _ (A' ⊗ B' ∷ Δ) eq
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (⊗L {Γ₁} {Δ} {A'} {B'} g) refl | inj₁ (Ω , refl , refl) =
  ⊗L {Γ ++ Δ₀ ++ A ⊗ B ∷ Δ₁ ++ Ω} {Δ} (cut⊗L≗ Γ Δ₀ Δ₁ f g refl)
  ∘ ⊗L⊗L {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Ω} {Λ = Δ}
cut⊗L≗ Γ Δ₀ Δ₁ f (⊗L {Γ₁} {Δ} {A'} {B'} g) refl | inj₂ ([] , refl , refl) = refl
cut⊗L≗ Γ Δ₀ Δ₁ {Λ = Λ} {A = A} {B} f (⊗L {Γ₁} {Δ} {A'} {B'} g) refl | inj₂ (A' ⊗ B' ∷ Ω , refl , refl) =
  ⊗L {Γ₁} (cut⊗L≗ (Γ₁ ++ A' ∷ B' ∷ Ω) Δ₀ Δ₁ f g refl)
  ∘ (~ (⊗L⊗L {Γ = Γ₁} {Δ = Ω ++ Δ₀} {Λ = Δ₁ ++ Λ}))
cut⊗L≗ Γ Δ₀ Δ₁ {Λ = Λ} f (⇒R g) refl =
  ⇒R (cut⊗L≗ (_ ∷ Γ) Δ₀ Δ₁ f g refl)
  ∘ (~ (⊗L⇒R {Γ = Γ ++ Δ₀} {Δ = Δ₁ ++ Λ}))
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (⇒L {Γ₁} {Δ} {Λ₁} {A'} {B'} g h) eq with cases++ Γ (Γ₁ ++ Δ) _ (A' ⇒ B' ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , refl) with cases++ Γ Γ₁ Ω Δ eq₁
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (⇒L {Γ₁} {Δ} {Λ₁} {A'} {B'} g h) refl | inj₁ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) =
  ⇒L {Γ ++ Δ₀ ++ A ⊗ B ∷ Δ₁ ++ Ξ} refl (cut⊗L≗ Γ Δ₀ Δ₁ f h refl)
  ∘ (~ (⊗L⇒L-comm₁ {Γ = Γ ++ Δ₀} {Λ = Δ₁ ++ Ξ}))
cut⊗L≗ Γ Δ₀ Δ₁ {A = A} {B} f (⇒L {Γ₁} {Δ} {Λ₁} {A'} {B'} g h) refl | inj₁ (Ω , refl , refl) | inj₂ (Ξ , refl , refl) =
  ⇒L (cut⊗L≗ Ξ Δ₀ Δ₁ f g refl) refl
  ∘ (~ (⊗L⇒L-assoc {Γ = Γ₁} {Δ₀ = Ξ ++ Δ₀} {Δ₁ = Δ₁ ++ Ω}))
cut⊗L≗ Γ Δ₀ Δ₁ f (⇒L {Γ₁} {Δ} {Λ₁} {A'} {B'} g h) refl | inj₂ ([] , refl , refl) = refl
cut⊗L≗ Γ Δ₀ Δ₁ {Λ = Λ} {A = A} {B} f (⇒L {Γ₁} {Δ} {Λ₁} {A'} {B'} g h) refl | inj₂ (A' ⇒ B' ∷ Ω , refl , refl) =
  ⇒L refl (cut⊗L≗ (Γ₁ ++ B' ∷ Ω) Δ₀ Δ₁ f h refl)
  ∘ (~ (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ} {Λ = Ω ++ Δ₀} {Ω = Δ₁ ++ Λ}))
cut⊗L≗ [] Δ₀ Δ₁ f ax refl = refl
cut⊗L≗ (D ∷ Γ) Δ₀ Δ₁ f ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))

cut⇒L≗ : (Γ : Cxt) → ∀ {Δ Δ₀ Δ₁ Λ Ω A B C D}
  → (f : Δ ⊢ A) (f₁ : Δ₀ ++ B ∷ Δ₁ ⊢ D)
  → (g : Ω ⊢ C)
  → (eq : Ω ≡ Γ ++ D ∷ Λ)
  → cut Γ (⇒L f f₁) g eq ≗ ⇒L {Γ ++ Δ₀} f (cut Γ f₁ g eq)
cut⇒L≗ Γ f f₁ IR eq = ⊥-elim ([]disj∷ Γ eq)
cut⇒L≗ Γ {Δ = Δ} {Δ₀ = Δ₀} {Δ₁} {A = A} {B} f f₁ (IL {Γ₁} {Δ'} g) eq with cases++ Γ Γ₁ _ (I ∷ Δ') eq
cut⇒L≗ Γ {Δ = Δ} {Δ₀ = Δ₀} {Δ₁} {A = A} {B} f f₁ (IL {Γ₁} {Δ'} g) refl | inj₁ (Ω , refl , refl) =
  IL {Γ ++ Δ₀ ++ Δ ++ A ⇒ B ∷ Δ₁ ++ Ω} {Δ'} (cut⇒L≗ Γ f f₁ g refl)
  ∘ IL⇒L-comm₂ {Γ = Γ ++ Δ₀} {Δ = Δ} {Λ = Δ₁ ++ Ω} {Ω = Δ'}
cut⇒L≗ Γ f f₁ (IL {Γ₁} {Δ'} g) refl | inj₂ ([] , refl , refl) = refl
cut⇒L≗ Γ {Δ = Δ} {Δ₀ = Δ₀} {Δ₁} {Λ = Λ} {A = A} {B} f f₁ (IL {Γ₁} {Δ'} g) refl | inj₂ (I ∷ Ω , refl , refl) =
  IL {Γ₁} {Ω ++ Δ₀ ++ Δ ++ A ⇒ B ∷ Δ₁ ++ Λ}
    (cut⇒L≗ (Γ₁ ++ Ω) f f₁ g refl)
  ∘ IL⇒L-comm₁ {Γ = Γ₁} {Λ = Ω ++ Δ₀}
cut⇒L≗ Γ {Δ₀ = Δ₀} {Δ₁} f f₁ (⊗R {Γ₁} {Δ'} g h) eq with cases++ Γ Γ₁ _ Δ' eq
cut⇒L≗ Γ {Δ₀ = Δ₀} {Δ₁} f f₁ (⊗R {Γ₁} {Δ'} g h) refl | inj₁ (Ω , refl , refl) =
  ⊗R (cut⇒L≗ Γ f f₁ g refl) refl
  ∘ (~ (⇒L⊗R₁ {Γ = Γ ++ Δ₀} {Λ = Δ₁ ++ Ω} {Ω = Δ'}))
cut⇒L≗ Γ {Δ₀ = Δ₀} {Δ₁} {Λ = Λ} f f₁ (⊗R {Γ₁} {Δ'} g h) refl | inj₂ (Ω , refl , refl) =
  ⊗R refl (cut⇒L≗ Ω f f₁ h refl)
  ∘ (~ (⇒L⊗R₂ {Γ = Ω ++ Δ₀} {Λ = Δ₁ ++ Λ} {Ω = Γ₁}))
cut⇒L≗ Γ {Δ₀ = Δ₀} {Δ₁} f f₁ (⊗L {Γ₁} {Δ'} {A'} {B'} g) eq with cases++ Γ Γ₁ _ (A' ⊗ B' ∷ Δ') eq
cut⇒L≗ Γ {Δ = Δ} {Δ₀ = Δ₀} {Δ₁} {A = A} {B} f f₁ (⊗L {Γ₁} {Δ'} {A'} {B'} g) refl | inj₁ (Ω , refl , refl) =
  ⊗L {Γ ++ Δ₀ ++ Δ ++ A ⇒ B ∷ Δ₁ ++ Ω} {Δ'} (cut⇒L≗ Γ f f₁ g refl)
  ∘ ⊗L⇒L-comm₂ {Γ = Γ ++ Δ₀} {Λ = Δ₁ ++ Ω}
cut⇒L≗ Γ f f₁ (⊗L {Γ₁} {Δ'} {A'} {B'} g) refl | inj₂ ([] , refl , refl) = refl
cut⇒L≗ Γ {Δ₀ = Δ₀} {Δ₁} {Λ = Λ} f f₁ (⊗L {Γ₁} {Δ'} {A'} {B'} g) refl | inj₂ (A' ⊗ B' ∷ Ω , refl , refl) =
  ⊗L {Γ₁} (cut⇒L≗ (Γ₁ ++ A' ∷ B' ∷ Ω) f f₁ g refl)
  ∘ ⊗L⇒L-comm₁ {Γ = Γ₁} {Λ = Ω ++ Δ₀}
cut⇒L≗ Γ {Δ₀ = Δ₀} {Δ₁} {Λ = Λ} f f₁ (⇒R g) refl =
  ⇒R (cut⇒L≗ (_ ∷ Γ) f f₁ g refl)
  ∘ (~ (⇒L⇒R {Γ = Γ ++ Δ₀} {Λ = Δ₁ ++ Λ}))
cut⇒L≗ Γ {Δ = Δ} {Δ₀} {Δ₁} f f₁ (⇒L {Γ₁} {Δ'} {Λ₁} {A'} {B'} g h) eq with cases++ Γ (Γ₁ ++ Δ') _ (A' ⇒ B' ∷ Λ₁) eq
... | inj₁ (Ω , eq₁ , refl) with cases++ Γ Γ₁ Ω Δ' eq₁
cut⇒L≗ Γ {Δ = Δ} {Δ₀} {Δ₁} {A = A} {B} f f₁ (⇒L {Γ₁} {Δ'} {Λ₁} {A'} {B'} g h) refl | inj₁ (Ω , refl , refl) | inj₁ (Ξ , refl , refl) =
  ⇒L {Γ ++ Δ₀ ++ Δ ++ A ⇒ B ∷ Δ₁ ++ Ξ} refl (cut⇒L≗ Γ f f₁ h refl)
  ∘ (~ (⇒L⇒L-comm {Γ = Γ ++ Δ₀} {Λ = Δ₁ ++ Ξ}))
cut⇒L≗ Γ {Δ = Δ} {Δ₀} {Δ₁} f f₁ (⇒L {Γ₁} {Δ'} {Λ₁} {A'} {B'} g h) refl | inj₁ (Ω , refl , refl) | inj₂ (Ξ , refl , refl) =
  ⇒L (cut⇒L≗ Ξ f f₁ g refl) refl
  ∘ (~ (⇒L⇒L-assoc {Γ₀ = Ξ ++ Δ₀} {Γ₁ = Γ₁} {Λ₀ = Δ₁ ++ Ω}))
cut⇒L≗ Γ f f₁ (⇒L {Γ₁} {Δ'} {Λ₁} {A'} {B'} g h) refl | inj₂ ([] , refl , refl) = refl
cut⇒L≗ Γ {Δ₀ = Δ₀} {Δ₁} {Λ = Λ} f f₁ (⇒L {Γ₁} {Δ'} {Λ₁} {A'} {B'} g h) refl | inj₂ (A' ⇒ B' ∷ Ω , refl , refl) =
  ⇒L refl (cut⇒L≗ (Γ₁ ++ B' ∷ Ω) f f₁ h refl)
  ∘ ⇒L⇒L-comm {Γ = Γ₁} {Λ = Ω ++ Δ₀} {Ξ = Δ₁ ++ Λ}
cut⇒L≗ [] f f₁ ax refl = refl
cut⇒L≗ (D ∷ Γ) f f₁ ax eq = ⊥-elim ([]disj∷ Γ (inj∷ eq .proj₂))

postulate
  cut-cong₂ : (Γ : Cxt) → ∀ {Δ Λ Ω C D}
    → {f : Δ ⊢ D} {g g' : Ω ⊢ C}
    → (eq : Ω ≡ Γ ++ D ∷ Λ)
    → (p : g ≗ g')
    → cut Γ f g eq ≗ cut Γ f g' eq
