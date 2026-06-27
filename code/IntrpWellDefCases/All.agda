{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.All where

open import IntrpWellDefCases.Base public using (MIP≗; intrp≗)

open import IntrpWellDefCases.ImpLImpR public using (mip≗⇒L⇒R)
open import IntrpWellDefCases.LeftImpLImpR public using (mip≗⇐L⇒R)
open import IntrpWellDefCases.TensorLImpR public using (mip≗⊗L⇒R)
open import IntrpWellDefCases.ILImpR public using (mip≗IL⇒R)

open import IntrpWellDefCases.ImpLLeftImpR public using (mip≗⇒L⇐R)
open import IntrpWellDefCases.LeftImpLLeftImpR public using (mip≗⇐L⇐R)
open import IntrpWellDefCases.TensorLLeftImpR public using (mip≗⊗L⇐R)
open import IntrpWellDefCases.ILLeftImpR public using (mip≗IL⇐R)

open import IntrpWellDefCases.ImpLTensorR1 public using (mip≗⇒L⊗R₁)
open import IntrpWellDefCases.ImpLTensorR2 public using (mip≗⇒L⊗R₂)
open import IntrpWellDefCases.LeftImpLTensorR1 public using (mip≗⇐L⊗R₁)
open import IntrpWellDefCases.LeftImpLTensorR2 public using (mip≗⇐L⊗R₂)
open import IntrpWellDefCases.TensorLTensorR1 public using (mip≗⊗L⊗R₁)
open import IntrpWellDefCases.TensorLTensorR2 public using (mip≗⊗L⊗R₂)
open import IntrpWellDefCases.ILTensorR1 public using (mip≗IL⊗R₁)
open import IntrpWellDefCases.ILTensorR2 public using (mip≗IL⊗R₂)

open import IntrpWellDefCases.TensorLTensorL public using (mip≗⊗L⊗L)
open import IntrpWellDefCases.ILIL public using (mip≗ILIL)
open import IntrpWellDefCases.ILTensorLComm1 public using (mip≗IL⊗L-comm₁)
open import IntrpWellDefCases.ILTensorLComm2 public using (mip≗IL⊗L-comm₂)

open import IntrpWellDefCases.TensorLImpLAssoc public using (mip≗⊗L⇒L-assoc)
open import IntrpWellDefCases.TensorLImpLComm1 public using (mip≗⊗L⇒L-comm₁)
open import IntrpWellDefCases.TensorLImpLComm2 public using (mip≗⊗L⇒L-comm₂)
open import IntrpWellDefCases.ILImpLAssoc public using (mip≗IL⇒L-assoc)
open import IntrpWellDefCases.ILImpLComm1 public using (mip≗IL⇒L-comm₁)
open import IntrpWellDefCases.ILImpLComm2 public using (mip≗IL⇒L-comm₂)

open import IntrpWellDefCases.TensorLLeftImpLAssoc public using (mip≗⊗L⇐L-assoc)
open import IntrpWellDefCases.TensorLLeftImpLComm1 public using (mip≗⊗L⇐L-comm₁)
open import IntrpWellDefCases.TensorLLeftImpLComm2 public using (mip≗⊗L⇐L-comm₂)
open import IntrpWellDefCases.ILLeftImpLAssoc public using (mip≗IL⇐L-assoc)
open import IntrpWellDefCases.ILLeftImpLComm1 public using (mip≗IL⇐L-comm₁)
open import IntrpWellDefCases.ILLeftImpLComm2 public using (mip≗IL⇐L-comm₂)

open import IntrpWellDefCases.ImpLImpLAssoc public using (mip≗⇒L⇒L-assoc)
open import IntrpWellDefCases.ImpLImpLComm public using (mip≗⇒L⇒L-comm)
open import IntrpWellDefCases.ImpLLeftImpLAssoc public using (mip≗⇒L⇐L-assoc)
open import IntrpWellDefCases.ImpLLeftImpLComm public using (mip≗⇒L⇐L-comm)
open import IntrpWellDefCases.LeftImpLImpLAssoc public using (mip≗⇐L⇒L-assoc)
open import IntrpWellDefCases.LeftImpLImpLComm public using (mip≗⇐L⇒L-comm)
open import IntrpWellDefCases.LeftImpLLeftImpLAssoc public using (mip≗⇐L⇐L-assoc)
open import IntrpWellDefCases.LeftImpLLeftImpLComm public using (mip≗⇐L⇐L-comm)
