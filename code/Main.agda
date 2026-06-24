{-# OPTIONS --rewriting #-}

module Main where

-- Sequent calculus and the congruence relation of derivation (≗) 
-- of the right implication fragment of associative Lambek calculus (Lam⇒)
import SeqCalc

-- Cut is admissible in Lam⇒
import Cut

-- Maehara interpolation procedure of Lam⇒, which is a function mip
-- where given any f : Γ , Δ , Λ ⊢ C, there exist
-- a formula D and two derivations g : Γ , D , Λ ⊢ C and h : Δ ⊢ D,
-- where (D , g , h) is called as interpolation triples.
import Mip

-- The equivalence relation of interpolation triples (∼)
import IntrpTriples

-- Maehara interpolation procedure defined in Mip is well-defined wrt. ≗, i.e.
-- if f ≗ f', then (D , g , h) ∼ (D' , g' , h') where
-- mip f = (D , g , h) and mip f' = (D' , g' , h')
import IntrpWellDef