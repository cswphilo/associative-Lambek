{-# OPTIONS --rewriting #-}

module SeqCalc where

-- open import Fma
open import Data.List
open import Relation.Binary.PropositionalEquality hiding (_≗_; [_])
open import Utilities

postulate At : Set

infix 22 _⇒_  _⊗_
--  _∨_ _∧_



-- Formulae

data Fma : Set where
  at : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma
  _⇒_ : Fma → Fma → Fma
  

Cxt : Set
Cxt = List Fma

infix 4 _⊢_

data _⊢_ : Cxt → Fma → Set where

  ax : ∀ {A}
    → A ∷ [] ⊢ A
  
  IR : [] ⊢ I

  IL : ∀ {Γ Δ C}
    → Γ ++ Δ ⊢ C
    → Γ ++ I ∷ Δ ⊢ C

  ⊗R : ∀ {Γ Δ A B}
    → Γ ⊢ A → Δ ⊢ B
    → Γ ++ Δ ⊢ A ⊗ B

  ⊗L : ∀ {Γ Δ A B C}
    → Γ ++ A ∷ B ∷ Δ ⊢ C
    → Γ ++ A ⊗ B ∷ Δ ⊢ C

  ⇒R : ∀ {Γ A B}
    → A ∷ Γ ⊢ B
    → Γ ⊢ A ⇒ B

  ⇒L : ∀ {Γ Δ Λ A B C}
    → Δ ⊢ A → Γ ++ B ∷ Λ ⊢ C
    → Γ ++ Δ ++ A ⇒ B ∷ Λ ⊢ C


subst-cxt : ∀ {Γ Δ C} → Γ ≡ Δ
  → Γ ⊢ C → Δ ⊢ C
subst-cxt refl f = f  

subst-succ : ∀ {Γ C D} → C ≡ D
  → Γ ⊢ C → Γ ⊢ D
subst-succ refl f = f 

-- axA : {A : Fma} → A ∷ [] ⊢ A
-- axA {at x} = ax
-- axA {I} = IL {[]} IR
-- axA {A ⊗ A₁} = ⊗L {[]} (⊗R axA axA)
-- axA {A ⇒ A₁} = ⇒R (⇒L {[]} axA axA)
-- axA {A ⇐ A₁} = ⇐R (⇐L {[]} axA axA)

-- Equivalence of derivations of product-free L

data _≗_ : {Γ : Cxt} {A : Fma} → Γ ⊢ A → Γ ⊢ A → Set where
-- equivalence relation
  refl : ∀{Γ A} {f : Γ ⊢ A} → f ≗ f
  ~_ : ∀{Γ A} {f g : Γ ⊢ A} → f ≗ g → g ≗ f
  _∘_ : ∀{Γ A} {f g h : Γ ⊢ A} → f ≗ g → g ≗ h → f ≗ h

-- congruence
  -- IL : ∀ {Γ Δ C}
  --   → {f g : Γ ++ Δ ⊢ C}
  --   → f ≗ g
  --   → IL {Γ} {Δ} f ≗ IL g
  ⇒R : ∀{Γ A B}
    → {f g : A ∷ Γ ⊢ B} 
    → f ≗ g
    → ⇒R f ≗ ⇒R g
  ⇒L : ∀{Γ Δ Λ A B C}
    → {f f' : Δ ⊢ A} {g g' : Γ ++ B ∷ Λ  ⊢ C}
    → f ≗ f' → g ≗ g'
    → ⇒L f g ≗ ⇒L f' g'
  ⊗R : ∀ {Γ Δ A B}
    → {f f' : Γ ⊢ A} {g g' : Δ ⊢ B}
    → f ≗ f' → g ≗ g'
    → ⊗R f g ≗ ⊗R f' g'
  ⊗L : ∀ {Γ Δ A B C}
    → {f g : Γ ++ A ∷ B ∷ Δ ⊢ C}
    → f ≗ g
    → ⊗L f ≗ ⊗L g

-- -- permutative conversions
  ⇒L⇒R : ∀{Γ Δ Λ A B A' B'}
    → {f : Δ ⊢ A} {g : A' ∷ Γ ++ B ∷ Λ ⊢ B'}
    → ⇒L f (⇒R g) ≗ ⇒R (⇒L f g)
  ⊗L⇒R : ∀{Γ Δ A B A' B'} 
    → {f : A' ∷ Γ ++ A ∷ B ∷ Δ ⊢ B'}
    → ⊗L (⇒R f) ≗ ⇒R (⊗L {_ ∷ _} f)
  -- IL⇒R : ∀{Γ Δ A' B'} 
  --   → {f : A' ∷ Γ ++ Δ ⊢ B'}
  --   → IL {Γ} {Δ} (⇒R f) ≗ ⇒R (IL {_ ∷ _} f)
  ⇒L⊗R₁ : ∀{Γ Δ Λ Ω A B A' B'} 
    → {f : Δ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ A'}
    → {h : Ω ⊢ B'}
    → ⇒L f (⊗R g h) ≗ ⊗R (⇒L f g) h
  ⇒L⊗R₂ : ∀{Γ Δ Λ Ω A B A' B'} 
    → {f : Δ ⊢ A} {g : Ω ⊢ A'}
    → {h : Γ ++ B ∷ Λ ⊢ B'}
    → ⇒L {Ω ++ Γ} f (⊗R g h) ≗ ⊗R g (⇒L f h)
  ⊗L⊗R₁ : ∀{Γ Δ Λ A B A' B'}
    → {f : Γ ++ A ∷ B ∷ Δ ⊢ A'}
    → {g : Λ ⊢ B'}
    → ⊗L (⊗R f g) ≗ ⊗R (⊗L f) g
  ⊗L⊗R₂ : ∀{Γ Δ Λ A B A' B'}
    → {f : Γ ⊢ A'}
    → {g : Δ ++ A ∷ B ∷ Λ ⊢ B'}
    → ⊗L {Γ ++ Δ} (⊗R f g) ≗ ⊗R f (⊗L g)
  -- IL⊗R₁ : ∀{Γ Δ Λ A' B'}
  --   → {f : Γ ++ Δ ⊢ A'}
  --   → {g : Λ ⊢ B'}
  --   → IL (⊗R f g) ≗ ⊗R (IL {Γ} {Δ} f) g
  -- IL⊗R₂ : ∀{Γ Δ Λ A' B'}
  --   → {f : Γ ⊢ A'}
  --   → {g : Δ ++ Λ ⊢ B'}
  --   → IL {Γ ++ Δ} (⊗R f g) ≗ ⊗R f (IL {Δ} {Λ} g)
  ⊗L⊗L : ∀ {Γ Δ Λ A B A' B' C} 
    → {f : Γ ++ A ∷ B ∷ Δ ++ A' ∷ B' ∷ Λ ⊢ C}
    → ⊗L {Γ ++ A ⊗ B ∷ Δ} (⊗L f) ≗ ⊗L (⊗L {Γ ++ A ∷ B ∷ Δ} f)
  -- ILIL : ∀ {Γ Δ Λ C} 
  --   → {f : Γ ++ Δ ++ Λ ⊢ C}
  --   → IL {Γ ++ I ∷ Δ} {Λ} (IL f) ≗ IL (IL {Γ ++ Δ} f)
  
  -- IL⊗L-comm₁ : ∀ {Γ Δ Λ A B C}
  --   → {f : Γ ++ Δ ++ A ∷ B ∷ Λ ⊢ C}
  --   → IL (⊗L {Γ ++ Δ} f) ≗ ⊗L {Γ ++ I ∷ Δ} (IL f)

  -- IL⊗L-comm₂ : ∀ {Γ Δ Λ A B C}
  --   → {f : Γ ++ A ∷ B ∷ Δ ++ Λ ⊢ C}
  --   → IL {Γ ++ A ⊗ B ∷ Δ} {Λ} (⊗L f) ≗ ⊗L (IL {Γ ++ A ∷ B ∷ Δ} f)

  ⊗L⇒L-assoc : ∀{Γ Δ₀ Δ₁ Λ A B A' B' C}
    → {f : Δ₀ ++ A' ∷ B' ∷ Δ₁ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
    → ⊗L {Γ ++ Δ₀} (⇒L f g) ≗ ⇒L (⊗L f) g
  ⊗L⇒L-comm₁ : ∀{Γ Δ Λ Ω A B A' B' C} 
    → {f : Δ ⊢ A} {g : Γ ++ A' ∷ B' ∷ Λ ++ B ∷ Ω ⊢ C}
    → ⊗L (⇒L {Γ ++ A' ∷ B' ∷ Λ} f g) ≗ ⇒L {Γ ++ A' ⊗ B' ∷ Λ} f (⊗L g) 
  ⊗L⇒L-comm₂ : ∀{Γ Δ Λ Ω A B A' B' C} 
    → {f : Δ ⊢ A} {g : Γ ++ B ∷ Λ ++ A' ∷ B' ∷ Ω ⊢ C}
    → ⊗L {Γ ++ Δ ++ A ⇒ B ∷ Λ} (⇒L f g) ≗ ⇒L f (⊗L {Γ ++ B ∷ Λ} g) 

  -- IL⇒L-assoc : ∀{Γ Δ₀ Δ₁ Λ A B C}
  --   → {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
  --   → IL {Γ ++ Δ₀} (⇒L f g) ≗ ⇒L (IL {Δ₀} {Δ₁} f) g
  -- IL⇒L-comm₁ : ∀{Γ Δ Λ Ω A B C} 
  --   → {f : Δ ⊢ A} {g : Γ ++ Λ ++ B ∷ Ω ⊢ C}
  --   → IL (⇒L {Γ ++ Λ} f g) ≗ ⇒L {Γ ++ I ∷ Λ} f (IL g) 
  -- IL⇒L-comm₂ : ∀{Γ Δ Λ Ω A B C} 
  --   → {f : Δ ⊢ A} {g : Γ ++ B ∷ Λ ++ Ω ⊢ C}
  --   → IL {Γ ++ Δ ++ A ⇒ B ∷ Λ} (⇒L f g) ≗ ⇒L f (IL {Γ ++ B ∷ Λ} {Ω} g) 

  ⇒L⇒L-assoc : ∀{Γ₀ Γ₁ Δ Λ₀ Λ₁ A B A' B' C}
    → {f : Δ ⊢ A'}
    → {g : Γ₀ ++ B' ∷ Λ₀ ⊢ A} {h : Γ₁ ++ B ∷ Λ₁ ⊢ C}
    → ⇒L {Γ₁ ++ Γ₀} f (⇒L g h) ≗ ⇒L (⇒L f g) h
  ⇒L⇒L-comm : ∀{Γ Δ₀ Δ₁ Λ Ξ A B A' B' C} 
    → {f : Δ₀ ⊢ A} {f' : Δ₁ ⊢ A'}
    → {g : Γ ++ B ∷ Λ ++ B' ∷ Ξ ⊢ C}
    → ⇒L f (⇒L {Γ ++ B ∷ Λ} f' g) ≗ ⇒L {Γ ++ Δ₀ ++ A ⇒ B ∷ Λ} f' (⇒L f g)

≡to≗ : ∀{T C}
  → {f g : T ⊢ C}
  → f ≡ g
  → f ≗ g
≡to≗ refl = refl
 
     