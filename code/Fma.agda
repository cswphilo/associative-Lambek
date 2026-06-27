{-# OPTIONS --rewriting #-}

module Fma where

open import Utilities
open import Data.List renaming (map to mapList; fromMaybe to backlist)
open import Data.Unit
open import Data.Empty
open import Data.Product
-- ============================================================
-- Formulae of  Associative Lambek Calculus L
-- ============================================================

postulate At : Set

infix 22 _⇒_ _⇐_ _⊗_
--  _∨_ _∧_



-- Formulae

data Fma : Set where
  at : At → Fma
  I : Fma
  _⊗_ : Fma → Fma → Fma
  _⇒_ _⇐_ : Fma → Fma → Fma
  

Cxt : Set
Cxt = List Fma

-- isAt : Fma → Set
-- isAt (at x) = ⊤
-- isAt (A ⇒ A₁) = ⊥
-- isAt (A ⇐ A₁) = ⊥

-- AtFma : Set
-- AtFma = Σ Fma λ A → isAt A

-- ToAt : AtFma → Fma
-- ToAt = λ X → proj₁ X

-- AtCxt : Set
-- AtCxt = List AtFma

-- ToAtCxt : AtCxt → Cxt
-- ToAtCxt = λ Γ → mapList ToAt Γ
