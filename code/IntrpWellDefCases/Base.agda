{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.Base where

open import Data.Sum using (inj₁; inj₂) public
open import Data.List using (List; []; _∷_; _++_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst) public
open import Data.Product public

open import SeqCalc public
open import Cut public
open import CutProperties public
open import Utilities public
open import Mip public
open import IntrpTriples public

{-
Shared context for the split-out `mip≗` congruence cases.

Each case file in `IntrpWellDefCases/` isolates one congruence generator of
`_≗_`. The goal is to record the list-equality geometry without having to keep
all twenty cases in one module while the proofs are still incomplete.
-}

record MIP≗ (Γ Δ Λ : Cxt) (C : Fma) (n n' : MIP Γ Δ Λ C) : Set where
  constructor intrp≗
  field
    eq : n ~ n'

mip[]≗ : ∀ Γ Λ {Ω : Cxt} {C : Fma} {f f' : Ω ⊢ C}
  → (eq : Ω ≡ Γ ++ Λ)
  → f ≗ f'
  → MIP≗ Γ [] Λ C (mip Γ [] Λ f eq) (mip Γ [] Λ f' eq)
mip[]≗ Γ Λ refl p = intrp≗ (g~ (IL p))

mipIL~Λ : ∀ Γ Δ Λ₀ Λ₁ {C} {f : Γ ++ Δ ++ Λ₀ ++ Λ₁ ⊢ C}
  → mip Γ Δ (Λ₀ ++ I ∷ Λ₁) (IL {Γ ++ Δ ++ Λ₀} {Λ₁} f) refl
      ~ IL~Λ' {Γ} {Δ} {Λ₀} {Λ₁} (mip Γ Δ (Λ₀ ++ Λ₁) f refl)
mipIL~Λ Γ [] Λ₀ Λ₁ = g~ (~ ILIL)
mipIL~Λ Γ (A ∷ Δ) Λ₀ Λ₁
  rewrite ++?-inj₂ Γ (Δ ++ Λ₀) (I ∷ Λ₁) A |
          cases++-inj₂ Λ₀ Δ Λ₁ I = refl

mipIL~Δ : ∀ Γ Δ₀ Δ₁ Λ {C} {f : Γ ++ Δ₀ ++ Δ₁ ++ Λ ⊢ C}
  → mip Γ (Δ₀ ++ I ∷ Δ₁) Λ (IL {Γ ++ Δ₀} {Δ₁ ++ Λ} f) refl
      ~ IL~Δ' {Γ} {Δ₀} {Δ₁} {Λ} (mip Γ (Δ₀ ++ Δ₁) Λ f refl)
mipIL~Δ Γ [] Δ₁ Λ
  rewrite ++?-inj₁ [] Γ (I ∷ Δ₁ ++ Λ) = refl
mipIL~Δ Γ (A ∷ Δ₀) Δ₁ Λ
  rewrite ++?-inj₂ Γ Δ₀ (I ∷ Δ₁ ++ Λ) A |
          cases++-inj₁ Δ₀ Δ₁ Λ I = refl

mip⇒R~ : ∀ Γ Δ Λ {A B : Fma} {f : A ∷ Γ ++ Δ ++ Λ ⊢ B}
  → mip Γ Δ Λ (⇒R f) refl ~ ⇒R~' (mip (A ∷ Γ) Δ Λ f refl)
mip⇒R~ Γ [] Λ = g~ IL⇒R
mip⇒R~ Γ (E ∷ Δ) Λ = refl

mip⇐R~ : ∀ Γ Δ Λ {A B : Fma} {f : Γ ++ Δ ++ Λ ++ A ∷ [] ⊢ B}
  → mip Γ Δ Λ (⇐R {Γ ++ Δ ++ Λ} {A} {B} f) refl
      ~ ⇐R~' {Γ = Γ} {Δ = Δ} {Λ = Λ} {A = A} {C = B}
          (mip Γ Δ (Λ ++ A ∷ []) f refl)
mip⇐R~ Γ [] Λ = g~ IL⇐R
mip⇐R~ Γ (E ∷ Δ) Λ = refl

mip⊗R₁~ : ∀ Γ Δ Λ {A B : Fma}
  {f : Γ ++ Δ ⊢ A} {g : Λ ⊢ B}
  → mip Γ Δ Λ (⊗R f g) refl
      ~ ⊗R~₁' (mip Γ Δ [] f refl) g
mip⊗R₁~ Γ [] Λ = g~ IL⊗R₁
mip⊗R₁~ Γ (E ∷ Δ) Λ
  rewrite ++?-inj₂ Γ Δ Λ E |
          ++?-inj₁ [] Δ Λ = refl

mip⊗R₁Λ~ : ∀ Γ Δ Λ Ω {A B : Fma}
  {f : Γ ++ Δ ++ Λ ⊢ A} {g : Ω ⊢ B}
  → mip Γ Δ (Λ ++ Ω) (⊗R {Γ ++ Δ ++ Λ} {Ω} f g) refl
      ~ ⊗R~₁' (mip Γ Δ Λ f refl) g
mip⊗R₁Λ~ Γ [] Λ Ω = g~ IL⊗R₁
mip⊗R₁Λ~ Γ (E ∷ Δ) Λ Ω
  rewrite ++?-inj₂ Γ (Δ ++ Λ) Ω E |
          ++?-inj₁ Λ Δ Ω = refl

mip⊗R₂~ : ∀ Γ₁ Δ₁ Δ Λ {A B : Fma}
  {f : Γ₁ ⊢ A} {g : Δ₁ ++ Δ ++ Λ ⊢ B}
  → mip (Γ₁ ++ Δ₁) Δ Λ (⊗R f g) refl
      ~ ⊗R~₂' (mip Δ₁ Δ Λ g refl) f
mip⊗R₂~ Γ₁ Δ₁ [] Λ = g~ IL⊗R₂
mip⊗R₂~ Γ₁ Δ₁ (E ∷ Δ) Λ
  rewrite ++?-inj₁ Δ₁ Γ₁ (E ∷ Δ ++ Λ) = refl

cut⊗RIR⊗L⊗R-base : ∀ Γ Δ Λ {A B D : Fma}
  {f : Γ ⊢ A} {g : D ∷ Δ ++ Λ ⊢ B}
  → ⊗R f g ≗
      cut Γ (⊗R IR ax)
        (⊗L {Γ} {Δ ++ Λ} (⊗R (IL {Γ} {[]} f) g)) refl
cut⊗RIR⊗L⊗R-base Γ Δ Λ {D = D} {g = g}
  rewrite cases++-inj₂ [] Γ (Δ ++ Λ) (I ⊗ D) |
          cases++-inj₂ [] (Γ ++ I ∷ []) (Δ ++ Λ) D |
          cases++-inj₁ Γ [] (D ∷ Δ ++ Λ) I |
          cases++-inj₂ [] Γ [] I =
    ⊗R refl (~ cutaxA-left [] g refl)

mip⊗Rmid~ : ∀ Γ Δ₀ F Δ₁ Λ {A B : Fma}
  {f : Γ ++ Δ₀ ⊢ A} {g : F ∷ Δ₁ ++ Λ ⊢ B}
  → mip Γ (Δ₀ ++ F ∷ Δ₁) Λ
      (⊗R {Γ ++ Δ₀} {F ∷ Δ₁ ++ Λ} f g) refl
      ~ ⊗R~' (mip Γ Δ₀ [] f refl) (mip [] (F ∷ Δ₁) Λ g refl)
mip⊗Rmid~ Γ [] F Δ₁ Λ {g = g}
  rewrite ++?-inj₁ [] Γ (F ∷ Δ₁ ++ Λ) =
  let H = mip [] (F ∷ Δ₁) Λ g refl
  in ↝∷
    (⊗R IR ax ,
     cut⊗RIR⊗L⊗R-base Γ [] Λ {g = MIP.g H} ,
     (~ ≡to≗ (cut⊗Rcases++₂ [] [] [] {f = MIP.h H} {g = IR} {h = ax})) ∘
       ⊗R refl (cutaxA-right (MIP.h H)))
    refl
mip⊗Rmid~ Γ (E ∷ Δ₀) F Δ₁ Λ
  rewrite ++?-inj₂ Γ Δ₀ (F ∷ Δ₁ ++ Λ) E |
          ++?-inj₂ Δ₀ Δ₁ Λ F = refl

mip⇒L~⇒ : ∀ Γ₁ Δ₀ Δ₁ Λ₀ Λ
  {A B C : Fma}
  {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₀ ++ Λ ⊢ C}
  → mip (Γ₁ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Λ₀) Λ (⇒L {Γ₁} {Δ₀ ++ Δ₁} {Λ₀ ++ Λ} f g) refl
      ~ ⇒L~⇒' (mip [] Δ₀ Δ₁ f refl) (mip Γ₁ (B ∷ Λ₀) Λ g refl)
mip⇒L~⇒ Γ₁ Δ₀ [] Λ₀ Λ {A} {B}
  rewrite ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Λ₀ ++ Λ) = refl
mip⇒L~⇒ Γ₁ Δ₀ (D ∷ Δ₁) Λ₀ Λ {A} {B}
  rewrite ++?-inj₂ (Γ₁ ++ Δ₀) Δ₁ (A ⇒ B ∷ Λ₀ ++ Λ) D |
          cases++-inj₂ Δ₀ Γ₁ Δ₁ D |
          cases++-inj₁ Δ₁ Λ₀ Λ (A ⇒ B) = refl

mip⇒L~Δ : ∀ Γ₁ Δ Λ₀ Λ₁
  {A B C : Fma}
  {f : Δ ++ Λ₀ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → mip Γ₁ Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (⇒L {Γ₁} {Δ ++ Λ₀} {Λ₁} f g) refl
      ~ ⇒L~Δ' (mip [] Δ Λ₀ f refl) g
mip⇒L~Δ Γ₁ [] Λ₀ Λ₁ = g~ IL⇒L-assoc
mip⇒L~Δ Γ₁ (D ∷ Δ) Λ₀ Λ₁ {A} {B}
  rewrite ++?-inj₂ Γ₁ (Δ ++ Λ₀) (A ⇒ B ∷ Λ₁) D |
          cases++-inj₂ [] Γ₁ (Δ ++ Λ₀) D |
          cases++-inj₂ Λ₀ Δ Λ₁ (A ⇒ B) = refl

mip⇒L~ΔΓ : ∀ Γ₁ Δ₀ Δ Λ₀ Λ₁
  {A B C : Fma}
  {f : Δ₀ ++ Δ ++ Λ₀ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → mip (Γ₁ ++ Δ₀) Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (⇒L {Γ₁} {Δ₀ ++ Δ ++ Λ₀} {Λ₁} f g) refl
      ~ ⇒L~Δ' (mip Δ₀ Δ Λ₀ f refl) g
mip⇒L~ΔΓ Γ₁ Δ₀ [] Λ₀ Λ₁ = g~ IL⇒L-assoc
mip⇒L~ΔΓ Γ₁ Δ₀ (D ∷ Δ) Λ₀ Λ₁ {A} {B}
  rewrite ++?-inj₂ (Γ₁ ++ Δ₀) (Δ ++ Λ₀) (A ⇒ B ∷ Λ₁) D |
          cases++-inj₂ Δ₀ Γ₁ (Δ ++ Λ₀) D |
          cases++-inj₂ Λ₀ Δ Λ₁ (A ⇒ B) = refl

mip⊗L~Λ : ∀ Γ Δ Λ₀ Λ₁ {A' B' C}
  {f : Γ ++ Δ ++ Λ₀ ++ A' ∷ B' ∷ Λ₁ ⊢ C}
  → mip Γ Δ (Λ₀ ++ A' ⊗ B' ∷ Λ₁) (⊗L {Γ ++ Δ ++ Λ₀} f) refl
      ~ ⊗L~Λ' {Γ} {Δ} {Λ₀} {Λ₁} (mip Γ Δ (Λ₀ ++ A' ∷ B' ∷ Λ₁) f refl)
mip⊗L~Λ Γ [] Λ₀ Λ₁ = g~ IL⊗L-comm₁
mip⊗L~Λ Γ (E ∷ Δ) Λ₀ Λ₁ {A'} {B'}
  rewrite ++?-inj₂ Γ (Δ ++ Λ₀) (A' ⊗ B' ∷ Λ₁) E |
          cases++-inj₂ Λ₀ Δ Λ₁ (A' ⊗ B') = refl

mip⊗L~Δ : ∀ Γ Δ₀ Δ₁ Λ {A' B' C}
  {f : Γ ++ Δ₀ ++ A' ∷ B' ∷ Δ₁ ++ Λ ⊢ C}
  → mip Γ (Δ₀ ++ A' ⊗ B' ∷ Δ₁) Λ (⊗L {Γ ++ Δ₀} f) refl
      ~ ⊗L~Δ' {Γ} {Δ₀} {Δ₁} {Λ} (mip Γ (Δ₀ ++ A' ∷ B' ∷ Δ₁) Λ f refl)
mip⊗L~Δ Γ [] Δ₁ Λ {A'} {B'}
  rewrite ++?-inj₁ [] Γ (A' ⊗ B' ∷ Δ₁ ++ Λ) = refl
mip⊗L~Δ Γ (E ∷ Δ₀) Δ₁ Λ {A'} {B'}
  rewrite ++?-inj₂ Γ Δ₀ (A' ⊗ B' ∷ Δ₁ ++ Λ) E |
          cases++-inj₁ Δ₀ Δ₁ Λ (A' ⊗ B') = refl

mip⊗L~Γ : ∀ Γ₀ Γ₁ Δ Λ {A' B' C}
  {f : Γ₀ ++ A' ∷ B' ∷ Γ₁ ++ Δ ++ Λ ⊢ C}
  → mip (Γ₀ ++ A' ⊗ B' ∷ Γ₁) Δ Λ (⊗L {Γ₀} {Γ₁ ++ Δ ++ Λ} f) refl
      ~ ⊗L~Γ' {Γ₀} {Γ₁} {Δ} {Λ} (mip (Γ₀ ++ A' ∷ B' ∷ Γ₁) Δ Λ f refl)
mip⊗L~Γ Γ₀ Γ₁ [] Λ = g~ IL⊗L-comm₂
mip⊗L~Γ Γ₀ Γ₁ (E ∷ Δ) Λ {A'} {B'}
  rewrite ++?-inj₁ (A' ⊗ B' ∷ Γ₁) Γ₀ (E ∷ Δ ++ Λ) = refl

-- mip of ⇐L when the window lies in g, separated from B by a nonempty H ∷ Γ₁.
mip⇐L~Γ : ∀ Γ₀ H Γ₁ Δ Λ
  {Ω : Cxt} {A B C : Fma}
  {f : Ω ⊢ A} {g : Γ₀ ++ B ∷ H ∷ Γ₁ ++ Δ ++ Λ ⊢ C}
  → mip (Γ₀ ++ B ⇐ A ∷ Ω ++ H ∷ Γ₁) Δ Λ
      (⇐L {Γ₀} {Ω} {H ∷ Γ₁ ++ Δ ++ Λ} f g) refl
      ~ ⇐L~Γ' {Γ₀ = Γ₀} {Γ₁ = H ∷ Γ₁} (mip (Γ₀ ++ B ∷ H ∷ Γ₁) Δ Λ g refl) f
mip⇐L~Γ Γ₀ H Γ₁ [] Λ = g~ IL⇐L-comm₂
mip⇐L~Γ Γ₀ H Γ₁ (E ∷ Δ) Λ {Ω} {A} {B}
  rewrite cases++-inj₁ Γ₀ (Ω ++ H ∷ Γ₁ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₀ (Ω ++ H ∷ Γ₁) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (H ∷ Γ₁ ++ E ∷ Δ) Ω Λ |
          ++?-inj₂ Ω Γ₁ (E ∷ Δ) H = refl

-- mip of ⇐L when the window lies in f's argument, ending before a nonempty
-- M ∷ Λ₀ tail of f's argument (so the window is not flush with g).
mip⇐L~Δ : ∀ Γ₁ Δ₀ Δ M Λ₀ Λ₁
  {A B C : Fma}
  {f : Δ₀ ++ Δ ++ M ∷ Λ₀ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → mip (Γ₁ ++ B ⇐ A ∷ Δ₀) Δ (M ∷ Λ₀ ++ Λ₁) (⇐L {Γ₁} {Δ₀ ++ Δ ++ M ∷ Λ₀} {Λ₁} f g) refl
      ~ ⇐L~Δ' {Γ = Δ₀} {Γ₁ = Γ₁} {Δ = Δ} {Λ = M ∷ Λ₀} {Λ₁ = Λ₁} (mip Δ₀ Δ (M ∷ Λ₀) f refl) g
mip⇐L~Δ Γ₁ Δ₀ [] M Λ₀ Λ₁ = g~ IL⇐L-assoc
mip⇐L~Δ Γ₁ Δ₀ (E ∷ Δ) M Λ₀ Λ₁ {A} {B}
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ E ∷ Δ) (M ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Δ₀ ++ E ∷ Δ) Λ₀ Λ₁ M = refl

IL⇐L⊗R-seed-base : ∀ Γ Δ Λ {A B C : Fma}
  {f : Δ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
  → IL {Γ ++ B ⇐ A ∷ Δ} {Λ} (⇐L f g) ≗
      cut (Γ ++ B ⇐ A ∷ Δ) (IL {[]} {[]} (⊗R IR IR))
        (⊗L {Γ ++ B ⇐ A ∷ Δ} {Λ}
          (⇐L {Γ} {Δ ++ I ∷ []} {I ∷ Λ}
            (IL {Δ} {[]} f) (IL {Γ ++ B ∷ []} {Λ} g))) refl
IL⇐L⊗R-seed-base Γ Δ Λ {A} {B}
  rewrite cases++-inj₂ [] (Γ ++ B ⇐ A ∷ Δ) Λ (I ⊗ I) |
          cases++-inj₂ (B ⇐ A ∷ Δ ++ I ∷ []) Γ Λ I |
          cases++-inj₂ Δ [] Λ I |
          cases++-inj₂ [] (Δ ++ I ∷ []) Λ I |
          cases++-inj₂ (B ⇐ A ∷ Δ) Γ Λ I |
          cases++-inj₂ [] (Γ ++ B ∷ []) Λ I |
          cases++-inj₁ Δ [] Λ I |
          cases++-inj₂ [] Δ [] I = refl

mip⇐L~⊗mid-base : ∀ Γ₁ Δ₀ Δ₁ Ω Λ
  {A B C : Fma}
  {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Ω ++ Λ ⊢ C}
  → mip (Γ₁ ++ B ⇐ A ∷ Δ₀) (Δ₁ ++ Ω) Λ
      (⇐L {Γ₁} {Δ₀ ++ Δ₁} {Ω ++ Λ} f g) refl
      ~ ⇐L~⊗' {Γ₀ = Γ₁} {Γ₁ = Δ₀}
          (mip Δ₀ Δ₁ [] f refl)
          (mip (Γ₁ ++ B ∷ []) Ω Λ g refl)
mip⇐L~⊗mid-base Γ₁ Δ₀ [] [] Λ =
  ↝∷ (IL {[]} {[]} (⊗R IR IR) , IL⇐L⊗R-seed-base Γ₁ Δ₀ Λ , refl) refl
mip⇐L~⊗mid-base Γ₁ Δ₀ [] (E ∷ Ω) Λ {A} {B}
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ E ∷ Ω) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (E ∷ Ω) (B ⇐ A) |
          ++?-inj₁ (E ∷ Ω) Δ₀ Λ |
          ++?-inj₁ [] Δ₀ (E ∷ Ω) = refl
mip⇐L~⊗mid-base Γ₁ Δ₀ (E ∷ Δ₁) Ω Λ {A} {B}
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ E ∷ Δ₁ ++ Ω) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (E ∷ Δ₁ ++ Ω) (B ⇐ A) |
          ++?-inj₁ Ω (Δ₀ ++ E ∷ Δ₁) Λ |
          ++?-inj₁ (E ∷ Δ₁) Δ₀ Ω = refl
-- Shared helper lemmas factored out of the individual well-definedness cases.
-- The case modules below should import only this base module, while the public
-- case-proof imports are collected separately in IntrpWellDefCases.All.
mipIL~Γ : ∀ Γ₀ Γ₁ Δ Λ {C} {f : Γ₀ ++ Γ₁ ++ Δ ++ Λ ⊢ C}
  → mip (Γ₀ ++ I ∷ Γ₁) Δ Λ (IL {Γ₀} {Γ₁ ++ Δ ++ Λ} f) refl
      ~ IL~Γ' {Γ₀} {Γ₁} {Δ} {Λ} (mip (Γ₀ ++ Γ₁) Δ Λ f refl)
mipIL~Γ Γ₀ Γ₁ [] Λ = g~ ILIL
mipIL~Γ Γ₀ Γ₁ (A ∷ Δ) Λ 
  rewrite ++?-inj₁ (I ∷ Γ₁) Γ₀ (A ∷ Δ ++ Λ) = refl

mip⇒L~Λ∷ : ∀ Γ Δ E Λ₀ Λ₁
  {Ω : Cxt} {A B C : Fma}
  {f : Ω ⊢ A} {g : Γ ++ Δ ++ E ∷ Λ₀ ++ B ∷ Λ₁ ⊢ C}
  → mip Γ Δ (E ∷ Λ₀ ++ Ω ++ A ⇒ B ∷ Λ₁)
      (⇒L {Γ ++ Δ ++ E ∷ Λ₀} {Ω} {Λ₁} f g) refl
      ~ ⇒L~Λ' {Γ} {Δ} {E ∷ Λ₀} {Λ₁} (mip Γ Δ (E ∷ Λ₀ ++ B ∷ Λ₁) g refl) f
mip⇒L~Λ∷ Γ [] E Λ₀ Λ₁ = g~ IL⇒L-comm₁
mip⇒L~Λ∷ Γ (D ∷ Δ) E Λ₀ Λ₁ {Ω} {A} {B}
  rewrite ++?-inj₂ Γ (Δ ++ E ∷ Λ₀ ++ Ω) (A ⇒ B ∷ Λ₁) D |
          cases++-inj₁ Γ (Δ ++ E ∷ Λ₀) Ω D |
          cases++-inj₂ (E ∷ Λ₀ ++ Ω) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Λ₀ Ω E = refl

mip⇒L~Γ : ∀ Γ₀ Γ₁ Δ Λ
  {Ω : Cxt} {A B C : Fma}
  {f : Ω ⊢ A} {g : Γ₀ ++ B ∷ Γ₁ ++ Δ ++ Λ ⊢ C}
  → mip (Γ₀ ++ Ω ++ A ⇒ B ∷ Γ₁) Δ Λ
      (⇒L {Γ₀} {Ω} {Γ₁ ++ Δ ++ Λ} f g) refl
      ~ ⇒L~Γ' {Γ₀ = Γ₀} {Γ₁ = Γ₁} (mip (Γ₀ ++ B ∷ Γ₁) Δ Λ g refl) f
mip⇒L~Γ Γ₀ Γ₁ [] Λ = g~ IL⇒L-comm₂
mip⇒L~Γ Γ₀ Γ₁ (E ∷ Δ) Λ {Ω} {A} {B}
  rewrite ++?-inj₁ (A ⇒ B ∷ Γ₁) (Γ₀ ++ Ω) (E ∷ Δ ++ Λ) = refl

mip⇐L~Λ : ∀ Γ Δ Λ₀ Λ₁
  {Ω : Cxt} {A B C : Fma}
  {f : Ω ⊢ A} {g : Γ ++ Δ ++ Λ₀ ++ B ∷ Λ₁ ⊢ C}
  → mip Γ Δ (Λ₀ ++ B ⇐ A ∷ Ω ++ Λ₁)
      (⇐L {Γ ++ Δ ++ Λ₀} {Ω} {Λ₁} f g) refl
      ~ ⇐L~Λ' {Γ} {Δ} {Λ₀} {Λ₁} (mip Γ Δ (Λ₀ ++ B ∷ Λ₁) g refl) f
mip⇐L~Λ Γ [] Λ₀ Λ₁ = g~ IL⇐L-comm₁
mip⇐L~Λ Γ (D ∷ Δ) Λ₀ Λ₁ {Ω} {A} {B}
  rewrite cases++-inj₂ Λ₀ (Γ ++ D ∷ Δ) (Ω ++ Λ₁) (B ⇐ A) = refl

cutIRIL : ∀ Γ Λ {C : Fma} {g : Γ ++ Λ ⊢ C}
  → cut Γ IR (IL {Γ} {Λ} g) refl ≗ g
cutIRIL Γ Λ rewrite cases++-inj₂ [] Γ Λ I = refl

IL⇒L⊗R-seed : ∀ Γ Δ Λ {A B C : Fma}
  {f : Δ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
  → IL (⇒L f g) ≗
      cut Γ (IL {[]} {[]} (⊗R IR IR))
        (⊗L {Γ} {Δ ++ A ⇒ B ∷ Λ}
          (⇒L {Γ ++ I ∷ []} {I ∷ Δ} {Λ}
            (IL {[]} {Δ} f) (IL {Γ} {B ∷ Λ} g))) refl
IL⇒L⊗R-seed Γ Δ Λ {A} {B}
  rewrite cases++-inj₂ [] Γ (Δ ++ A ⇒ B ∷ Λ) (I ⊗ I) |
          cases++-inj₁ (Γ ++ I ∷ []) Δ (A ⇒ B ∷ Λ) I |
          cases++-inj₂ [] (Γ ++ I ∷ []) Δ I |
          cases++-inj₁ Γ Δ (A ⇒ B ∷ Λ) I |
          cases++-inj₁ Γ [] Δ I |
          cases++-inj₂ [] Γ (B ∷ Λ) I = refl

cut⊗RIR⊗L⇒L : ∀ Γ Δ Λ {A B C D : Fma}
  {f : D ∷ Δ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
  → ⇒L {Γ} {D ∷ Δ} {Λ} f g ≗
      cut Γ (⊗R IR ax)
        (⊗L {Γ} {Δ ++ A ⇒ B ∷ Λ}
          (⇒L {Γ ++ I ∷ []} {D ∷ Δ} {Λ}
            f (IL {Γ} {B ∷ Λ} g))) refl
cut⊗RIR⊗L⇒L Γ Δ Λ {A} {B} {C} {D} {f = f} {g}
  rewrite cases++-inj₂ [] Γ (Δ ++ A ⇒ B ∷ Λ) (I ⊗ D) |
          cases++-inj₁ (Γ ++ I ∷ []) Δ (A ⇒ B ∷ Λ) D |
          cases++-inj₂ [] (Γ ++ I ∷ []) Δ D |
          cases++-inj₁ Γ (D ∷ Δ) (A ⇒ B ∷ Λ) I |
          cases++-inj₁ Γ [] (D ∷ Δ) I |
          cases++-inj₂ [] Γ (B ∷ Λ) I =
    ⇒L (~ cutaxA-left [] f refl) refl
