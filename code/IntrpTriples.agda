{-# OPTIONS --rewriting #-}

module IntrpTriples where

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

_⊩_ : ∀ {Γ Δ Λ C} → (n n' : MIP Γ Δ Λ C) → Set
_⊩_ {Γ} (intrp D₁ g₁ h₁) (intrp D₂ g₂ h₂) = Σ (D₁ ∷ [] ⊢ D₂) λ t → (g₁ ≗ cut Γ t g₂ refl) × (cut [] h₁ t refl ≗ h₂)

data _~_ {Γ Δ Λ : Cxt} {C : Fma} : MIP Γ Δ Λ C → MIP Γ Δ Λ C → Set where
  refl : {n : MIP Γ Δ Λ C} → n ~ n
  ↝∷ : {n n' p : MIP Γ Δ Λ C} 
          → n ⊩ n' → n' ~ p
          → n ~ p
  ↜∷ : {n n' p : MIP Γ Δ Λ C} 
          → n' ⊩ n → n' ~ p
          → n ~ p

∷↝ : {Γ Δ Λ : Cxt} {C : Fma} 
  → {n n' p : MIP Γ Δ Λ C}
  → n ⊩ n' → p ~ n'
  → p ~ n
∷↝ x refl = ↜∷ x refl
∷↝ x (↝∷ y eq) = ↝∷ y (∷↝ x eq)
∷↝ x (↜∷ y eq) = ↜∷ y (∷↝ x eq)

∷↜ : {Γ Δ Λ : Cxt} {C : Fma} 
  → {n n' p : MIP Γ Δ Λ C}
  → n' ⊩ n → p ~ n'
  → p ~ n
∷↜ x refl = ↝∷ x refl
∷↜ x (↝∷ y eq) = ↝∷ y (∷↜ x eq)
∷↜ x (↜∷ y eq) = ↜∷ y (∷↜ x eq)

~-sym : {Γ Δ Λ : Cxt} {C : Fma} 
  → {n n' : MIP Γ Δ Λ C}
  → n ~ n'
  → n' ~ n
~-sym refl = refl
~-sym (↝∷ x eq) = ∷↝ x (~-sym eq)
~-sym (↜∷ x eq) = ∷↜ x (~-sym eq)

~-trans : {Γ Δ Λ : Cxt} {C : Fma} 
  → {n n' n'' : MIP Γ Δ Λ C}
  → n ~ n' → n' ~ n''
  → n ~ n''
~-trans refl eq₂ = eq₂
~-trans (↝∷ x eq₁) eq₂ = ↝∷ x (~-trans eq₁ eq₂)
~-trans (↜∷ x eq₁) eq₂ = ↜∷ x (~-trans eq₁ eq₂)

postulate 
  cut⊗L≗ : (Γ Δ₀ Δ₁ : Cxt) → ∀ {Λ Ω A B C D} 
    → (f : Δ₀ ++ A ∷ B ∷ Δ₁ ⊢ D) (g : Ω ⊢ C) (eq : Ω ≡ Γ ++ D ∷ Λ ) 
    → cut Γ (⊗L f) g eq ≗ ⊗L {Γ ++ Δ₀} (cut Γ f g eq)
  cut⇒L≗ : (Γ : Cxt) → ∀ {Δ Δ₀ Δ₁ Λ Ω A B C D}
    → (f : Δ ⊢ A) (f₁ : Δ₀ ++ B ∷ Δ₁ ⊢ D)
    → (g : Ω ⊢ C) 
    → (eq : Ω ≡ Γ ++ D ∷ Λ)
    → cut Γ (⇒L f f₁) g eq ≗ ⇒L {Γ ++ Δ₀} f (cut Γ f₁ g eq)
  cutaxA-left : (Γ : Cxt) → ∀ {Λ Ω A C}
    → (f : Ω ⊢ C)
    → (eq : Ω ≡ Γ ++ A ∷ Λ)
    → cut Γ ax f eq ≗ subst-cxt eq f
  -- cut-cong₁ : (Γ : Cxt) → ∀ {Δ Λ Ω C D}
  --   → {f f' : Δ ⊢ D} {g : Ω ⊢ C}
  --   → (eq : Ω ≡ Γ ++ D ∷ Λ)
  --   → (p : f ≗ f')
  --   → cut Γ f g eq ≗ cut Γ f' g eq
  cut-cong₂ : (Γ : Cxt) → ∀ {Δ Λ Ω C D}
    → {f : Δ ⊢ D} {g g' : Ω ⊢ C}
    → (eq : Ω ≡ Γ ++ D ∷ Λ)
    → (p : g ≗ g')
    → cut Γ f g eq ≗ cut Γ f g' eq
  -- cut-assoc : (Γ₀ Γ₁ : Cxt) → ∀ {Δ Λ₀ Λ₁ Ω C D E}
  --   → (f : Δ ⊢ D) (g : Γ₀ ++ D ∷ Λ₀ ⊢ E) (h : Ω ⊢ C)
  --   → (eq : Ω ≡ Γ₁ ++ E ∷ Λ₁)
  --   → cut Γ₁ (cut Γ₀ f g refl) h eq ≗ cut (Γ₁ ++ Γ₀) f (cut Γ₁ g h eq) refl
-- cutaxA-right : ∀ {Γ A}
--     → (f : Γ ⊢ A)
--     → cut [] f axA refl ≗ f
-- cutaxA-right {A = at x} f = refl
-- cutaxA-right {A = I} f = {!   !}
-- cutaxA-right {A = A ⊗ A₁} f = {!   !}
-- cutaxA-right {A = A ⇒ A₁} f = {!   !}

cutaxA-right : ∀ {Γ A}
    → (f : Γ ⊢ A)
    → cut [] f ax refl ≗ f
cutaxA-right f = refl
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

⊗L~Γ' : {Γ₀ Γ₁ Δ Λ : Cxt} {A B C : Fma}   
  → (n : MIP (Γ₀ ++ A ∷ B ∷ Γ₁) Δ Λ C)
  → MIP (Γ₀ ++ A ⊗ B ∷ Γ₁) Δ Λ C
⊗L~Γ' (intrp D g h) = intrp D (⊗L g) h 

⊗L~Γ : {Γ₀ Γ₁ Δ Λ : Cxt} {A B C : Fma}   
  → {n n' : MIP (Γ₀ ++ A ∷ B ∷ Γ₁) Δ Λ C}
  → n ~ n'
  → ⊗L~Γ' n ~ ⊗L~Γ' n' -- For some reason, this lemma cannot be defined directly.
                      -- Agda would take A ⊗ B as the interpolant formula for no reason.
  -- Γ₀ ++ A ∷ B ∷ Γ₁ ++ MIP.D n ∷ Λ ⊢ C
⊗L~Γ refl = refl
⊗L~Γ {Γ₀} {Γ₁} {Λ = Λ} (↝∷ (t , eqg , eqh) eq) = ↝∷ ((t , (⊗L eqg ∘ ≡to≗ (cut⊗L-cases++₁ Γ₀ Γ₁ Λ)) , eqh)) (⊗L~Γ eq)
⊗L~Γ {Γ₀} {Γ₁} {Λ = Λ} (↜∷ (t , eqg , eqh) eq) = ↜∷ ((t , (⊗L eqg ∘ ≡to≗ (cut⊗L-cases++₁ Γ₀ Γ₁ Λ)) , eqh)) (⊗L~Γ eq)

⊗L~Δ : {Γ Δ₀ Δ₁ Λ : Cxt} {A B C : Fma}   
  → {n n' : MIP Γ (Δ₀ ++ A ∷ B ∷ Δ₁) Λ C}
  → n ~ n'
  → intrp (MIP.D n) (MIP.g n) (⊗L (MIP.h n)) ~ intrp (MIP.D n') (MIP.g n') (⊗L (MIP.h n'))
⊗L~Δ refl = refl
⊗L~Δ {Δ₀ = Δ₀} {Δ₁} (↝∷ (t , eqg , eqh) eq) = ↝∷ (t , eqg , (cut⊗L≗ [] Δ₀ Δ₁ _ t refl ∘ ⊗L eqh)) (⊗L~Δ eq)
⊗L~Δ {Δ₀ = Δ₀} {Δ₁} (↜∷ (t , eqg , eqh) eq) = ↜∷ (t , eqg , (cut⊗L≗ [] Δ₀ Δ₁ _ t refl ∘ ⊗L eqh)) (⊗L~Δ eq)

⊗L~Λ : {Γ Δ Λ₀ Λ₁ : Cxt} {A B C : Fma}   
  → {n n' : MIP Γ Δ (Λ₀ ++ A ∷ B ∷ Λ₁) C}
  → n ~ n'
  → intrp (MIP.D n) (⊗L {Γ ++ _ ∷ Λ₀} (MIP.g n)) (MIP.h n) ~ intrp (MIP.D n') (⊗L {Γ ++ _ ∷ Λ₀} (MIP.g n')) (MIP.h n')
⊗L~Λ refl = refl
⊗L~Λ {Γ} {Λ₀ = Λ₀} {Λ₁} (↝∷ (t , eqg , eqh) eq) = ↝∷ (t , (⊗L {Γ ++ _ ∷ Λ₀} eqg ∘ ≡to≗ (cut⊗L-cases++₂ Γ Λ₀ Λ₁)) , eqh) (⊗L~Λ eq)
⊗L~Λ {Γ} {Λ₀ = Λ₀} {Λ₁} (↜∷ (t , eqg , eqh) eq) = ↜∷ (t , (⊗L {Γ ++ _ ∷ Λ₀} eqg ∘ ≡to≗ (cut⊗L-cases++₂ Γ Λ₀ Λ₁)) , eqh) (⊗L~Λ eq)

⇒R~ : {Γ Δ Λ : Cxt} {A C : Fma}   
  → {n n' : MIP (A ∷ Γ) Δ Λ C}
  → n ~ n'
  → intrp (MIP.D n) (⇒R (MIP.g n)) (MIP.h n) ~ intrp (MIP.D n') (⇒R (MIP.g n')) (MIP.h n')
⇒R~ refl = refl
⇒R~ (↝∷ (t , eqg , eqh) eq) = ↝∷ (t , ⇒R eqg , eqh) (⇒R~ eq)
⇒R~ (↜∷ (t , eqg , eqh) eq) = ↜∷ (t , ⇒R eqg , eqh) (⇒R~ eq)

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

⊗R~₁ : {Γ Δ Λ Ω : Cxt} {A B : Fma}
  → {n n' : MIP Γ Δ Λ A} 
  → {f f' : Ω ⊢ B}
  → n ~ n'
  → f ≗ f'
  → intrp (MIP.D n) (⊗R (MIP.g n) f) (MIP.h n) ~ intrp (MIP.D n') (⊗R (MIP.g n') f') (MIP.h n')
⊗R~₁ {Γ} {n = n} {f' = f'} refl q = ↝∷ (ax , (⊗R refl q ∘ (~ cutaxA-left Γ (⊗R (MIP.g n) f') refl)) , cutaxA-right (MIP.h n)) refl
⊗R~₁ {Γ} {Λ = Λ} {Ω} (↝∷ (t , eqg , eqh) eq) q = ↝∷ (t , (⊗R eqg refl ∘ ≡to≗ (cut⊗Rcases++₁ Γ Λ Ω)) , eqh) (⊗R~₁ eq q)
⊗R~₁ {Γ} {Λ = Λ} {Ω} (↜∷ (t , eqg , eqh) eq) q = ↜∷ (t , (⊗R eqg refl ∘ ≡to≗ (cut⊗Rcases++₁ Γ Λ Ω)) , eqh) (⊗R~₁ eq q)

⊗R~₂' : {Γ Δ Λ Ω : Cxt} {A B : Fma}   
  → (n : MIP Γ Δ Λ B) 
  → (f : Ω ⊢ A)
  → MIP (Ω ++ Γ) Δ Λ (A ⊗ B)
⊗R~₂' (intrp D g h) f = intrp D (⊗R f g) h

⊗R~₂ : {Γ Δ Λ Ω : Cxt} {A B : Fma}
  → {n n' : MIP Γ Δ Λ B} 
  → {f f' : Ω ⊢ A}
  → n ~ n'
  → f ≗ f'
  → ⊗R~₂' n f ~ ⊗R~₂' n' f'
⊗R~₂ {Γ} {Ω = Ω} {n = n} {f' = f'} refl q = ↝∷ (ax , (⊗R q refl ∘ (~ cutaxA-left (Ω ++ Γ) (⊗R f' (MIP.g n)) refl)) , cutaxA-right _) refl
⊗R~₂ {Γ} {Λ = Λ} {Ω} (↝∷ (t , eqg , eqh) eq) q = ↝∷ (t , (⊗R refl eqg ∘ ≡to≗(cut⊗Rcases++₂ Γ Λ Ω)) , eqh) (⊗R~₂ eq q)
⊗R~₂ {Γ} {Λ = Λ} {Ω} (↜∷ (t , eqg , eqh) eq) q = ↜∷ (t , (⊗R refl eqg ∘ ≡to≗(cut⊗Rcases++₂ Γ Λ Ω)) , eqh) (⊗R~₂ eq q)

⊗R~' : ∀ {Γ Δ₀ Δ₁ Λ A B}
  → (n : MIP Γ Δ₀ [] A) (n' : MIP [] Δ₁ Λ B)
  → MIP Γ (Δ₀ ++ Δ₁) Λ (A ⊗ B)
⊗R~' (intrp D g h) (intrp E g' h') = intrp (D ⊗ E) (⊗L (⊗R g g')) (⊗R h h')

⊗R~ : ∀ {Γ Δ₀ Δ₁ Λ A B}
  → {n n' : MIP Γ Δ₀ [] A} {m m' : MIP [] Δ₁ Λ B}
  → n ~ n' → m ~ m'
  → ⊗R~' n m ~ ⊗R~' n' m'
⊗R~ refl refl = refl
⊗R~ {Γ} {Λ = Λ} {n = n} refl (↝∷ {n' = m} (t , eqg , eqh) q) 
  = ↝∷ (⊗L {[]} (⊗R ax t) , (⊗L (((⊗R refl eqg ∘ ≡to≗ (cut⊗Rcases++₂ [] Λ (Γ ++ MIP.D n ∷ []))) 
    ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D n ∷ []) t (⊗R (MIP.g n) (MIP.g m)) refl) refl)) ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ Λ)) 
    ∘ (~ cut⊗L≗ Γ [] [] (⊗R ax t) (⊗L (⊗R (MIP.g n) (MIP.g m))) refl)) , 
    ⊗R (cutaxA-right _) eqh) 
    (⊗R~ refl q)
⊗R~ {Γ} {Λ = Λ} {n = n} {m = m} refl (↜∷ (t , eqg , eqh) q) 
  = ↜∷ (⊗L {[]} (⊗R ax t) , (⊗L (((⊗R refl eqg ∘ ≡to≗ (cut⊗Rcases++₂ [] Λ (Γ ++ MIP.D n ∷ []))) 
    ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D n ∷ []) t (⊗R (MIP.g n) (MIP.g m)) refl) refl)) ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ Λ)) 
    ∘ (~ cut⊗L≗ Γ [] [] (⊗R ax t) (⊗L (⊗R (MIP.g n) (MIP.g m))) refl)) , 
  ⊗R (cutaxA-right _) eqh) 
    (⊗R~ refl q)
⊗R~ {Γ} {Λ = Λ} {m = m} (↝∷ {n' = n'} (t , eqg , eqh) p) q 
  = ↝∷ (⊗L {[]} (⊗R t ax) , (⊗L (((⊗R eqg refl ∘ ≡to≗ (cut⊗Rcases++₁ Γ [] (MIP.D m ∷ Λ))) 
    ∘ (~ cut-cong₂ Γ refl (cutaxA-left (Γ ++ MIP.D n' ∷ []) (⊗R (MIP.g n') (MIP.g m)) refl))) ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ Λ)) 
    ∘ (~ cut⊗L≗ Γ [] [] (⊗R t ax) (⊗L (⊗R (MIP.g n') (MIP.g m))) refl)) , 
    (⊗R refl (cutaxA-right _) ∘ ⊗R eqh refl)) 
    (⊗R~ p q)
⊗R~ {Γ} {Λ = Λ} {n = n} {m = m} (↜∷ (t , eqg , eqh) p) q 
  = ↜∷ (⊗L {[]} (⊗R t ax) , (⊗L (((⊗R eqg refl ∘ ≡to≗ (cut⊗Rcases++₁ Γ [] (MIP.D m ∷ Λ))) 
    ∘ (~ cut-cong₂ Γ refl (cutaxA-left (Γ ++ MIP.D n ∷ []) (⊗R (MIP.g n) (MIP.g m)) refl))) ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ Λ)) 
    ∘ (~ cut⊗L≗ Γ [] [] (⊗R t ax) (⊗L (⊗R (MIP.g n) (MIP.g m))) refl)) , 
    (⊗R refl (cutaxA-right _) ∘ ⊗R eqh refl)) 
    (⊗R~ p q)

⇒L~Γ' : {Γ₀ Γ₁ Δ Λ Ω : Cxt} {A B C : Fma}   
  → (n : MIP (Γ₀ ++ B ∷ Γ₁) Δ Λ C)
  → (f : Ω ⊢ A)
  → MIP (Γ₀ ++ Ω ++ A ⇒ B ∷ Γ₁) Δ Λ C
⇒L~Γ' (intrp D g h) f = intrp D (⇒L f g) h

cut⇒L-cases++-comm₁ : (Γ₀ : Cxt) → ∀ {Γ₁ Δ Λ Ω A B C D}
  → {f : Ω ⊢ D} 
  → {g : Δ ⊢ A} {h : Γ₀ ++ B ∷ Γ₁ ++ D ∷ Λ ⊢ C}
  → cut (Γ₀ ++ Δ ++ A ⇒ B ∷ Γ₁) f (⇒L g h) refl ≡ ⇒L g (cut (Γ₀ ++ B ∷ Γ₁) f h refl)
cut⇒L-cases++-comm₁ Γ₀ {Γ₁} {Δ} {Λ} {A = A} {B} {D = D} 
  rewrite cases++-inj₂ (A ⇒ B ∷ Γ₁) (Γ₀ ++ Δ) Λ D = refl

⇒L~Γ : {Γ₀ Γ₁ Δ Λ Ω : Cxt} {A B C : Fma}   
  → {n n' : MIP (Γ₀ ++ B ∷ Γ₁) Δ Λ C}
  → {f f' : Ω ⊢ A}
  → n ~ n' → f ≗ f'
  → ⇒L~Γ' n f ~ ⇒L~Γ' n' f'
⇒L~Γ {Γ₀} {Γ₁} {Λ = Λ} {Ω} {A} {B} {n = n} {f' = f'} refl p 
  = ↝∷ (ax , (⇒L p refl ∘ (~ cutaxA-left (Γ₀ ++ Ω ++ A ⇒ B ∷ Γ₁) (⇒L f' (MIP.g n)) refl)) , cutaxA-right _) refl
⇒L~Γ {Γ₀} {Γ₁} {Λ = Λ} {Ω} {A} {B} (↝∷ (t , eqg , eqh) eq) p 
  = ↝∷ (t , (⇒L refl eqg ∘ (~ (≡to≗ (cut⇒L-cases++-comm₁ Γ₀)))) , eqh) (⇒L~Γ eq p)
⇒L~Γ {Γ₀} {Γ₁} {Λ = Λ} {Ω} {A} {B} (↜∷ (t , eqg , eqh) eq) p 
  = ↜∷ (t , (⇒L refl eqg ∘ (~ (≡to≗ (cut⇒L-cases++-comm₁ Γ₀)))) , eqh) (⇒L~Γ eq p)

⇒L~Δ' : {Γ Γ₁ Δ Λ Λ₁ : Cxt} {A B C : Fma}   
  → (n : MIP Γ Δ Λ A)
  → (f : Γ₁ ++ B ∷ Λ₁ ⊢ C)
  → MIP (Γ₁ ++ Γ) Δ (Λ ++ A ⇒ B ∷ Λ₁) C
⇒L~Δ'  (intrp D g h) f = intrp D (⇒L g f) h

cut⇒L-cases++₁ : (Γ Γ₁ : Cxt) → ∀ {Λ Λ₁ Ω A B C D}
  → {f : Ω ⊢ D} 
  → {g : Γ ++ D ∷ Λ ⊢ A} {h : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → cut (Γ₁ ++ Γ) f (⇒L g h) refl ≡ ⇒L (cut Γ f g refl) h
cut⇒L-cases++₁ Γ Γ₁ {Λ} {Λ₁} {A = A} {B} {D = D} 
  rewrite cases++-inj₁ (Γ₁ ++ Γ) Λ (A ⇒ B ∷ Λ₁) D | 
          cases++-inj₂ Γ Γ₁ Λ D = refl
⇒L~Δ : {Γ Γ₁ Δ Λ Λ₁ : Cxt} {A B C : Fma}   
  → {n n' : MIP Γ Δ Λ A}
  → {f f' : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → n ~ n' → f ≗ f'
  → ⇒L~Δ' n f ~ ⇒L~Δ' n' f'
⇒L~Δ {Γ} {Γ₁} {n = n} {f' = f'} refl p = ↝∷ (ax , (⇒L refl p ∘ (~ cutaxA-left (Γ₁ ++ Γ) (⇒L (MIP.g n) f') refl)) , cutaxA-right _) refl
⇒L~Δ {Γ} {Γ₁} (↝∷ (t , eqg , eqh) eq) p = ↝∷ (t , (⇒L eqg refl ∘ (~ ≡to≗ (cut⇒L-cases++₁ Γ Γ₁))) , eqh) (⇒L~Δ eq p)
⇒L~Δ {Γ} {Γ₁} (↜∷ (t , eqg , eqh) eq) p = ↜∷ (t , (⇒L eqg refl ∘ (~ ≡to≗ (cut⇒L-cases++₁ Γ Γ₁))) , eqh) (⇒L~Δ eq p)

⇒L~Λ' : {Γ Δ Λ₀ Λ₁ Ω : Cxt} {A B C : Fma}   
  → (n : MIP Γ Δ (Λ₀ ++ B ∷ Λ₁) C)
  → (f : Ω ⊢ A)
  → MIP Γ Δ (Λ₀ ++ Ω ++ A ⇒ B ∷ Λ₁) C
⇒L~Λ' {Γ} {Λ₀ = Λ₀} (intrp D g h) f = intrp D (⇒L {Γ ++ _ ∷ Λ₀} f g) h

cut⇒L-cases++-comm₂ : (Γ Λ₀ : Cxt) → ∀ {Δ Λ₁ Ω A B C D}
  → {f : Ω ⊢ D} 
  → {g : Δ ⊢ A} {h : Γ ++ D ∷ Λ₀ ++ B ∷ Λ₁ ⊢ C}
  → cut Γ f (⇒L {Γ ++ D ∷ Λ₀} g h) refl ≡ ⇒L {Γ ++ Ω ++ Λ₀} g (cut Γ f h refl)
cut⇒L-cases++-comm₂ Γ Λ₀ {Δ} {Λ₁} {A = A} {B} {D = D} 
  rewrite cases++-inj₁ Γ (Λ₀ ++ Δ) (A ⇒ B ∷ Λ₁) D |
          cases++-inj₁ Γ Λ₀ Δ D = refl
⇒L~Λ : {Γ Δ Λ₀ Λ₁ Ω : Cxt} {A B C : Fma}   
  → {n n' : MIP Γ Δ (Λ₀ ++ B ∷ Λ₁) C}
  → {f f' : Ω ⊢ A}
  → n ~ n'
  → f ≗ f'
  → ⇒L~Λ' n f ~ ⇒L~Λ' n' f'
⇒L~Λ {Γ} {Λ₀ = Λ₀} {n = n} {f' = f'} refl p 
  = ↝∷ (ax , (⇒L p refl ∘ (~ cutaxA-left Γ (⇒L {Γ ++ _ ∷ Λ₀} f' (MIP.g n)) refl)) , cutaxA-right _) refl
⇒L~Λ {Γ} {Λ₀ = Λ₀} (↝∷ (t , eqg , eqh) eq) p = ↝∷ (t , (⇒L refl eqg ∘ (~ ≡to≗ (cut⇒L-cases++-comm₂ Γ Λ₀))) , eqh) (⇒L~Λ eq p)
⇒L~Λ {Γ} {Λ₀ = Λ₀} (↜∷ {n' = n'} (t , eqg , eqh) eq) p 
  = ↜∷ (t , (⇒L {Γ ++ MIP.D n' ∷ Λ₀} refl eqg ∘ (~ ≡to≗ (cut⇒L-cases++-comm₂ Γ Λ₀))) , eqh) (⇒L~Λ eq p)

⇒L~ΓΛ' : {Γ₀ Γ₁ Λ₀ Λ₁ Ω : Cxt} {A B C : Fma}   
  → (n : MIP Γ₀ (Γ₁ ++ B ∷ Λ₀) Λ₁ C)
  → (f : Ω ⊢ A)
  → MIP Γ₀ (Γ₁ ++ Ω ++ A ⇒ B ∷ Λ₀) Λ₁ C
⇒L~ΓΛ' (intrp D g h) f = intrp D g (⇒L f h)

⇒L~ΓΛ : {Γ₀ Γ₁ Λ₀ Λ₁ Ω : Cxt} {A B C : Fma}   
  → {n n' : MIP Γ₀ (Γ₁ ++ B ∷ Λ₀) Λ₁ C}
  → {f f' : Ω ⊢ A}
  → n ~ n' → f ≗ f'
  → ⇒L~ΓΛ' n f ~ ⇒L~ΓΛ' n' f'
⇒L~ΓΛ {Γ₀} {n = n} refl p = ↝∷ (ax , (~ cutaxA-left Γ₀ (n .MIP.g) refl) , (cutaxA-right _ ∘ ⇒L p refl)) refl
⇒L~ΓΛ {n = n} {f = f} (↝∷ {n' = n'} (t , eqg , eqh) eq) p  
  = ↝∷ (t , eqg , (cut⇒L≗ [] f (n .MIP.h) t refl ∘ ⇒L refl eqh)) (⇒L~ΓΛ eq p)
⇒L~ΓΛ {n = n'} {f = f} (↜∷ {n' = n} (t , eqg , eqh) eq) p 
  = ↜∷ (t , eqg , (cut⇒L≗ [] f (n .MIP.h) t refl ∘ ⇒L refl eqh)) (⇒L~ΓΛ eq p)

⇒L~⇒' : ∀ {Γ Δ₀ Δ₁ Λ₀ Λ₁ A B C}
  → (n : MIP [] Δ₀ Δ₁ A) (m : MIP Γ (B ∷ Λ₀) Λ₁ C)
  → MIP (Γ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Λ₀) Λ₁ C
⇒L~⇒' (intrp D g h) (intrp E g' h') = intrp (D ⇒ E) (⇒L h g') (⇒R (⇒L {[]} g h'))

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

⇒L~⇒ : ∀ {Γ Δ₀ Δ₁ Λ₀ Λ₁ A B C}
  → {n n' : MIP [] Δ₀ Δ₁ A} {m m' : MIP Γ (B ∷ Λ₀) Λ₁ C}
  → n ~ n' → m ~ m'
  → ⇒L~⇒' n m ~ ⇒L~⇒' n' m' 
⇒L~⇒ refl refl = refl
⇒L~⇒ {Γ} {Δ₀} {Λ₁ = Λ₁} {n = intrp D g h} refl (↝∷ {n = intrp E g' h'} {n' = intrp F g'' h''} (t , eqg , eqh) q) 
  = ↝∷ (⇒R (⇒L {[]} ax t) , 
    ((⇒L (~ cutaxA-right _) eqg ∘ (~ ≡to≗ (cut⇒L-cases++-assoc [] Γ))) 
    ∘ (~ cut-cong₂ Γ refl (cut⇒L≗ Γ ax t g'' refl))) 
    ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ Γ Λ₁ Δ₀)) , 
    ⇒R (cutaxA-left [] (cut [] (⇒L g h') t refl) refl 
    ∘ (cut⇒L≗ [] g h' t refl ∘ ⇒L refl eqh))) (⇒L~⇒ refl q)
⇒L~⇒ {Γ} {Δ₀} {Λ₁ = Λ₁} {n = intrp D g h} refl (↜∷ {n = intrp E g' h'} {n' = intrp F g'' h''} (t , eqg , eqh) q) 
  = ↜∷ (⇒R (⇒L {[]} ax t) , 
    (((⇒L (~ cutaxA-right _) eqg ∘ (~ ≡to≗ (cut⇒L-cases++-assoc [] Γ))) 
    ∘ (~ cut-cong₂ Γ refl (cut⇒L≗ Γ ax t g' refl))) 
    ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ Γ Λ₁ Δ₀))) , 
    ⇒R (cutaxA-left [] (cut [] (⇒L g h'') t refl) refl  
    ∘ (cut⇒L≗ [] g h'' t refl ∘ ⇒L refl eqh))) (⇒L~⇒ refl q)
⇒L~⇒ {Γ} {Δ₀} {Λ₁ = Λ₁} {n = intrp D g h} {m = intrp E g' h'} (↝∷ {n' = intrp F g'' h''} (t , eqg , eqh) p) q 
  = ↜∷ (⇒R (⇒L {[]} t ax) , 
    ((⇒L (~ eqh) (~ cutaxA-left Γ g' refl) ∘ (~ ≡to≗ (cut⇒L-cases++-assoc [] Γ))) 
    ∘ (~ cut-cong₂ Γ refl (cut⇒L≗ Γ t ax g' refl))) ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ Λ₁ Δ₀))) , 
    ⇒R (refl ∘ ⇒L (~ eqg) (cutaxA-right _))) (⇒L~⇒ p q)
    -- refl in refl ∘ ⇒L (~ eqg) (cutaxA-right _)) was "cut-cong₂ [] refl (cut⇒L≗ [] g'' h' ax refl)""
  {-
  Our goal is ⇒L~⇒' (intrp D g h) (intrp E g' h') ~ ⇒L~⇒' n' m' while
  by I.H. we have ⇒L~⇒' (intrp F g'' h'') (intrp E g' h') ~ ⇒L~⇒' n' m',
  therefore we need to provide a proof of ⇒L~⇒' (intrp D g h) (intrp E g' h') ⊩ ⇒L~⇒' (intrp F g'' h'') (intrp E g' h').
  Given t : D ⊢ F from I.H., we can only construct F ⇒ E ⊢ D ⇒ E.
  Therefore we swap to ↜∷ in the goal.
  -}
⇒L~⇒ {Γ} {Δ₀} {Λ₁ = Λ₁} {n = intrp D g h} {m = intrp E g' h'} (↜∷ {n' = intrp F g'' h''} (t , eqg , eqh) p) q 
  = ↝∷ (⇒R (⇒L {[]} t ax) , (((⇒L (~ eqh) (~ cutaxA-left Γ g' refl) ∘ (~ ≡to≗ (cut⇒L-cases++-assoc [] Γ))) 
    ∘ (~ cut-cong₂ Γ refl (cut⇒L≗ Γ t ax g' refl))) ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ Λ₁ Δ₀)))) , 
    ⇒R (refl ∘ ⇒L (~ eqg) (cutaxA-right _))) (⇒L~⇒ p q)
    -- refl in refl ∘ ⇒L (~ eqg) (cutaxA-right _)) was "cut-cong₂ [] refl (cut⇒L≗ [] g h' ax refl)"" 

⇒L~⊗' : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ Λ A B C}
  → (n : MIP [] Δ₀ Δ₁ A) (m : MIP Γ₀ Γ₁ (B ∷ Λ) C)
  → MIP Γ₀ (Γ₁ ++ Δ₀) (Δ₁ ++ A ⇒ B ∷ Λ) C
⇒L~⊗' (intrp D g h) (intrp E g' h') = intrp (E ⊗ D) (⊗L (⇒L {_ ++ _ ∷ []} g g')) (⊗R h' h)

⇒L~⊗ : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ Λ A B C}
  → {n n' : MIP [] Δ₀ Δ₁ A} {m m' : MIP Γ₀ Γ₁ (B ∷ Λ) C}
  → n ~ n' → m ~ m'
  → ⇒L~⊗' n m ~ ⇒L~⊗' n' m' 
⇒L~⊗ refl refl = refl
⇒L~⊗ {Γ₀} {Δ₁ = Δ₁} {Λ} {A} {B} {n = intrp D g h} {m = intrp E g' h'} refl (↝∷ {n' = intrp F g'' h''} (t , eqg , eqh) q) 
  = ↝∷ (⊗L {[]} (⊗R t ax) , 
    ⊗L (((⇒L refl eqg ∘ (~ (≡to≗ (cut⇒L-cases++-comm₂ Γ₀ [])))) 
    ∘ (~ cut-cong₂ Γ₀ refl (cutaxA-left (Γ₀ ++ F ∷ []) (⇒L {Γ₀ ++ F ∷ []} g g'') refl))) 
    ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ₀ (Δ₁ ++ A ⇒ B ∷ Λ) {f = t} {ax} {⇒L {Γ₀ ++ F ∷ []} g g''})) 
    ∘ (~ cut⊗L≗ Γ₀ [] [] (⊗R t ax) (⊗L {Γ₀} (⇒L {Γ₀ ++ F ∷ []} g g'')) refl) , 
    ⊗R eqh (cutaxA-right _)) 
    (⇒L~⊗ refl q)
⇒L~⊗ {Γ₀} {Δ₁ = Δ₁} {Λ} {A} {B} {n = intrp D g h} {m = intrp E g' h'} refl (↜∷ {n' = intrp F g'' h''} (t , eqg , eqh) q) 
  = ↜∷ (⊗L {[]} (⊗R t ax) , 
    (⊗L ((⇒L {Γ₀ ++ F ∷ []} refl eqg ∘ ((~ (≡to≗ (cut⇒L-cases++-comm₂ Γ₀ []))) 
    ∘ (~ cut-cong₂ Γ₀ refl (cutaxA-left (Γ₀ ++ E ∷ []) (⇒L {Γ₀ ++ E ∷ []} g g') refl)))) 
    ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ₀ (Δ₁ ++ A ⇒ B ∷ Λ) {f = t} {ax} {⇒L {Γ₀ ++ E ∷ []} g g'}))
    ∘ (~ cut⊗L≗ Γ₀ [] [] (⊗R t ax) (⊗L {Γ₀} (⇒L {Γ₀ ++ E ∷ []} g g')) refl)) ,
    ⊗R eqh (cutaxA-right _)) 
    (⇒L~⊗ refl q)
    
⇒L~⊗ {Γ₀} {Δ₁ = Δ₁} {Λ} {A} {B} {n = intrp D g h} {m = intrp E g' h'} (↝∷ {n' = intrp F g'' h''} (t , eqg , eqh) p) q 
  = ↝∷ (⊗L {[]} (⊗R ax t) , 
    ⊗L (((⇒L eqg refl 
    ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] (Γ₀ ++ E ∷ []))))) 
    ∘ (~ cutaxA-left Γ₀ (cut (Γ₀ ++ E ∷ []) t (⇒L {Γ₀ ++ E ∷ []} g'' g') refl) refl)) 
    ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ₀ (Δ₁ ++ A ⇒ B ∷ Λ) {f = ax} {t} {⇒L {Γ₀ ++ E ∷ []} g'' g'})) 
    ∘ (~ cut⊗L≗ Γ₀ [] [] (⊗R ax t) (⊗L {Γ₀} (⇒L {Γ₀ ++ E ∷ []} g'' g')) refl) , 
    ⊗R (cutaxA-right _) eqh) 
    (⇒L~⊗ p q)
⇒L~⊗ {Γ₀} {Δ₁ = Δ₁} {Λ} {A} {B} {n = intrp D g h} {m = intrp E g' h'} (↜∷ {n' = intrp F g'' h''} (t , eqg , eqh) p) q 
  = ↜∷ (⊗L {[]} (⊗R ax t) , 
    (⊗L (((⇒L eqg refl 
    ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] (Γ₀ ++ E ∷ []))))) 
    ∘ (~ cutaxA-left Γ₀ (cut (Γ₀ ++ E ∷ []) t (⇒L {Γ₀ ++ E ∷ []} g g') refl) refl)) 
    ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ₀ (Δ₁ ++ A ⇒ B ∷ Λ) {f = ax} {t} {⇒L {Γ₀ ++ E ∷ []} g g'})) 
    ∘ (~ cut⊗L≗ Γ₀ [] [] (⊗R ax t) (⊗L {Γ₀} (⇒L {Γ₀ ++ E ∷ []} g g')) refl)) , 
    ⊗R (cutaxA-right _) eqh) 
    (⇒L~⊗ p q)