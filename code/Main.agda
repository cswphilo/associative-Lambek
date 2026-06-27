{-# OPTIONS --rewriting #-}

module Main where

-- Formulae and contexts of associative Lambek calculus L.
import Fma

-- Sequent calculus and the congruence relation of derivations (≗) for L.
import SeqCalc

-- Cut admissibility for L.
import Cut

-- Properties of cut used by the interpolation development.
import CutProperties

-- Maehara interpolation procedure for L, implemented as mip.
-- Given any f : Γ ++ Δ ++ Λ ⊢ C, it produces an interpolant D
-- with derivations g : Γ ++ D ∷ Λ ⊢ C and h : Δ ⊢ D.
import Mip

-- Proof-relevant interaction between cut and Maehara interpolation.
import CutIntrp

-- The equivalence relation of interpolation triples (∼).
import IntrpTriples

-- Maehara interpolation is well-defined wrt. ≗: equivalent derivations
-- are sent by mip to equivalent interpolation triples.
import IntrpWellDef
