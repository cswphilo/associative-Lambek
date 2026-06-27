{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ILLeftImpLAssoc where

open import Data.Empty using (⊥-elim)
open import IntrpWellDefCases.Base

cut⇐R⇐LIL⇐₀ : ∀ Δ {A B D : Fma}
  → (f : Δ ⊢ A) → (h : B ∷ [] ⊢ D)
  → cut []
      (⇐R {Γ = B ⇐ A ∷ Δ} {A = I} {B = D}
        (⇐L {Γ = []} {Δ = Δ ++ I ∷ []} {Λ = []}
          {A = A} {B = B} {C = D}
          (IL {Γ = Δ} {Δ = []} f) h))
      (⇐L {Γ = []} {Δ = []} {Λ = []}
        {A = I} {B = D} {C = D} IR ax)
      refl
    ≗ ⇐L {Γ = []} {Δ = Δ} {Λ = []}
        {A = A} {B = B} {C = D} f h
cut⇐R⇐LIL⇐₀ Δ f h
  rewrite cases++-inj₁ Δ [] [] I |
          cases++-inj₂ [] Δ [] I = refl

cut⇐R⇐LIL⇐₁ : ∀ Γ Δ {A B D : Fma}
  → (f : Δ ⊢ A) → (h : Γ ++ B ∷ [] ⊢ D)
  → cut []
      (⇐R {Γ = Γ ++ B ⇐ A ∷ Δ} {A = I} {B = D}
        (⇐L {Γ = Γ} {Δ = Δ ++ I ∷ []} {Λ = []}
          {A = A} {B = B} {C = D}
          (IL {Γ = Δ} {Δ = []} f) h))
      (⇐L {Γ = []} {Δ = []} {Λ = []}
        {A = I} {B = D} {C = D} IR ax)
      refl
    ≗ ⇐L {Γ = Γ} {Δ = Δ} {Λ = []}
        {A = A} {B = B} {C = D} f h
cut⇐R⇐LIL⇐₁ Γ Δ {A} {B} f h
  rewrite cases++-inj₂ (B ⇐ A ∷ Δ) Γ [] I |
          cases++-inj₁ Δ [] [] I |
          cases++-inj₂ [] Δ [] I = refl

IL⇐L⊗R-seed : ∀ Γ Δ Λ {A B C : Fma}
  {f : Δ ⊢ A} {g : Γ ++ B ∷ Λ ⊢ C}
  → IL {Γ ++ B ⇐ A ∷ Δ} {Λ} (⇐L f g) ≗
      cut (Γ ++ B ⇐ A ∷ Δ) (IL {[]} {[]} (⊗R IR IR))
        (⊗L {Γ ++ B ⇐ A ∷ Δ} {Λ}
          (⇐L {Γ} {Δ ++ I ∷ []} {I ∷ Λ}
            (IL {Δ} {[]} f) (IL {Γ ++ B ∷ []} {Λ} g))) refl
IL⇐L⊗R-seed Γ Δ Λ {A} {B}
  rewrite cases++-inj₂ [] (Γ ++ B ⇐ A ∷ Δ) Λ (I ⊗ I) |
          cases++-inj₂ (B ⇐ A ∷ Δ ++ I ∷ []) Γ Λ I |
          cases++-inj₂ Δ [] Λ I |
          cases++-inj₂ [] (Δ ++ I ∷ []) Λ I |
          cases++-inj₂ (B ⇐ A ∷ Δ) Γ Λ I |
          cases++-inj₂ [] (Γ ++ B ∷ []) Λ I |
          cases++-inj₁ Δ [] Λ I |
          cases++-inj₂ [] Δ [] I = refl

mip≗IL⇐L-assoc : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ : Cxt} {A B C : Fma}
  {f : Δ₀ ++ Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Δ₁ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (IL {Γ = Γ₁ ++ B ⇐ A ∷ Δ₀} {Δ₁ ++ Λ₁} (⇐L {Γ₁} {Δ₀ ++ Δ₁} {Λ₁} f g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₀ ++ I ∷ Δ₁} {Λ₁} (IL {Δ₀} {Δ₁} f) g) eq)
mip≗IL⇐L-assoc Γ [] Λ eq = mip[]≗ Γ Λ eq IL⇐L-assoc
mip≗IL⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq
  with cases++ (Γ₁ ++ B ⇐ A ∷ Δ₀) Γ (Δ₁ ++ Λ₁) (E ∷ Δ ++ Λ) (sym eq)
... | inj₁ (Ω , refl , eq2) with ++? Ω Δ₁ (E ∷ Δ ++ Λ) Λ₁ eq2
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Δ₁) (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₁ (Δ₁ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ (I ∷ Δ₁) (Γ₁ ++ B ⇐ A ∷ Δ₀) (E ∷ Δ ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₀ ++ Δ₁ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ Δ₁) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) (Δ₀ ++ Δ₁) Λ |
          ++?-inj₁ [] (Δ₀ ++ Δ₁) (E ∷ Δ) |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Δ₁ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Δ₁) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) (Δ₀ ++ I ∷ Δ₁) Λ |
          ++?-inj₁ [] (Δ₀ ++ I ∷ Δ₁) (E ∷ Δ) =
    intrp≗ (g~ (IL⊗L-comm₁ {Γ₁ ++ B ⇐ A ∷ Δ₀} {Δ₁} ∘
      ⊗L {Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Δ₁} (IL⇐L-assoc ∘ ⇐L (~ ILIL) refl)))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Δ₁ ++ x ∷ Ω') (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} refl | inj₁ (.(Δ₁ ++ x ∷ Ω') , refl , refl) | inj₁ (x ∷ Ω' , refl , refl) =
  intrp≗ (~-trans (mipIL~Γ (Γ₁ ++ B ⇐ A ∷ Δ₀) (Δ₁ ++ x ∷ Ω') (E ∷ Δ) Λ)
    (~-trans (IL~Γ {Γ₀ = Γ₁ ++ B ⇐ A ∷ Δ₀} {Γ₁ = Δ₁ ++ x ∷ Ω'} (mip⇐L~Γ Γ₁ x Ω' (E ∷ Δ) Λ {Ω = Δ₀ ++ Δ₁}))
      (~-trans (g~ IL⇐L-assoc)
        (~-sym (mip⇐L~Γ Γ₁ x Ω' (E ∷ Δ) Λ {Ω = Δ₀ ++ I ∷ Δ₁})))))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Ω) (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₁ (Ω , refl , eq2) | inj₂ (F , Ω' , refl , eqb)
  with inj∷ eqb
... | refl , eqb2 with ++? Ω' Δ Λ₁ Λ eqb2
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Ω) (E ∷ Δ) Λ {Γ₁} {Δ₀} {.(Ω ++ E ∷ Δ)} {Λ₁} {A} {B} refl | inj₁ (Ω , refl , eq2) | inj₂ (E , .(Δ) , refl , eqb) | refl , eqb2 | inj₁ ([] , refl , refl)
  rewrite ++?-inj₁ (I ∷ Ω) (Γ₁ ++ B ⇐ A ∷ Δ₀) (E ∷ Δ ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₀ ++ Ω ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ Ω) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ [] (Δ₀ ++ Ω ++ E ∷ Δ) Λ |
          ++?-inj₁ (E ∷ Δ) (Δ₀ ++ Ω) [] |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Ω ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Ω) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ [] (Δ₀ ++ I ∷ Ω ++ E ∷ Δ) Λ |
          ++?-inj₁ (E ∷ Δ) (Δ₀ ++ I ∷ Ω) [] =
    intrp≗ (~-trans (g~ (IL⊗L-comm₁ {Γ₁ ++ B ⇐ A ∷ Δ₀} {Ω} ∘
      ⊗L {Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Ω} IL⇐L-assoc))
      (~-sym (⇐L~⊗ (mipIL~Γ Δ₀ Ω (E ∷ Δ) []) refl)))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Ω) (E ∷ Δ) Λ {Γ₁} {Δ₀} {.(Ω ++ E ∷ Δ ++ x ∷ Ω'')} {Λ₁} {A} {B} refl | inj₁ (Ω , refl , eq2) | inj₂ (E , .(Δ ++ x ∷ Ω'') , refl , eqb) | refl , eqb2 | inj₁ (x ∷ Ω'' , refl , refl) =
  intrp≗ (~-trans (mipIL~Γ (Γ₁ ++ B ⇐ A ∷ Δ₀) Ω (E ∷ Δ) (x ∷ Ω'' ++ Λ₁))
    (~-trans (IL~Γ {Γ₀ = Γ₁ ++ B ⇐ A ∷ Δ₀} {Γ₁ = Ω} (mip⇐L~Δ Γ₁ (Δ₀ ++ Ω) (E ∷ Δ) x Ω'' Λ₁))
      (~-trans (g~ IL⇐L-assoc)
        (~-trans (~-sym (⇐L~Δ (mipIL~Γ Δ₀ Ω (E ∷ Δ) (x ∷ Ω'')) refl))
          (~-sym (mip⇐L~Δ Γ₁ (Δ₀ ++ I ∷ Ω) (E ∷ Δ) x Ω'' Λ₁))))))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Ω) (E ∷ .(Ω' ++ G ∷ Ω'')) Λ {Γ₁} {Δ₀} {.(Ω ++ E ∷ Ω')} {.(G ∷ Ω'' ++ Λ)} {A} {B} refl | inj₁ (Ω , refl , eq2) | inj₂ (E , Ω' , refl , eqb) | refl , eqb2 | inj₂ (G , Ω'' , refl , refl)
  rewrite ++?-inj₁ (I ∷ Ω) (Γ₁ ++ B ⇐ A ∷ Δ₀) (E ∷ Ω' ++ G ∷ Ω'' ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₀ ++ Ω ++ E ∷ Ω' ++ G ∷ Ω'') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ Ω) (E ∷ Ω' ++ G ∷ Ω'') (B ⇐ A) |
          ++?-inj₁ (G ∷ Ω'') (Δ₀ ++ Ω ++ E ∷ Ω') Λ |
          ++?-inj₁ (E ∷ Ω') (Δ₀ ++ Ω) (G ∷ Ω'') |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Ω ++ E ∷ Ω' ++ G ∷ Ω'') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Ω) (E ∷ Ω' ++ G ∷ Ω'') (B ⇐ A) |
          ++?-inj₁ (G ∷ Ω'') (Δ₀ ++ I ∷ Ω ++ E ∷ Ω') Λ |
          ++?-inj₁ (E ∷ Ω') (Δ₀ ++ I ∷ Ω) (G ∷ Ω'') =
    intrp≗ (~-trans (g~ (IL⊗L-comm₁ {Γ₁ ++ B ⇐ A ∷ Δ₀} {Ω} ∘
      ⊗L {Γ₁ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Ω} IL⇐L-assoc))
      (~-sym (⇐L~⊗ (mipIL~Γ Δ₀ Ω (E ∷ Ω') []) refl)))
mip≗IL⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq
  | inj₂ (Ω , eq1 , eq2)
  with cases++ Ω (E ∷ Δ) (Δ₁ ++ Λ₁) Λ eq1 | ++? Γ Γ₁ Ω (B ⇐ A ∷ Δ₀) eq2
mip≗IL⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₂ (Ω , eq1 , eq2) | inj₁ (Ω' , eqa , eqb) | inj₁ (Ω₀ , eqc , eqd) with cases∷ Ω eqa
... | inj₁ (refl , refl , refl) with ++? Δ Δ₁ Λ Λ₁ eqb
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀) (I ∷ .(Δ₁ ++ Ω''')) Λ {Γ₁} {Δ₀} {Δ₁} {.(Ω''' ++ Λ)} {A} {B} refl
  | inj₂ ([] , refl , refl) | inj₁ (.(Δ₁ ++ Ω''') , refl , refl) | inj₁ (.(B ⇐ A ∷ Δ₀) , refl , refl)
  | inj₁ (refl , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ B ⇐ A ∷ Δ₀) (I ∷ Δ₁ ++ Ω''' ++ Λ) |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (I ∷ Δ₁ ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' (Δ₀ ++ I ∷ Δ₁) Λ |
          ++?-inj₁ (I ∷ Δ₁) Δ₀ Ω'''
  with Δ₁
... | [] with Ω'''
... | [] =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = []} {Δ₁ = []}
          (↝∷ (IL {[]} {[]} (⊗R IR IR) , IL⇐L⊗R-seed Γ₁ Δ₀ Λ , refl) refl))
        (~-trans
          (h~ (IL⊗R₁ {Γ = []} {Δ = []} {Λ = []}))
          (~-sym (⇐L~⊗ (mipIL~Δ Δ₀ [] [] []) refl))))
... | F ∷ Ω''''
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ F ∷ Ω'''') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (F ∷ Ω'''') (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω'''') Δ₀ Λ |
          ++?-inj₁ [] Δ₀ (F ∷ Ω'''') =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = []} {Δ₁ = F ∷ Ω''''} refl)
        (~-trans
          (h~ (IL⊗R₁ {Γ = []} {Δ = []} {Λ = F ∷ Ω''''}))
          (~-sym (⇐L~⊗ (mipIL~Δ Δ₀ [] [] []) refl))))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀) (I ∷ .(Δ₁₀ ++ Ω''')) Λ {Γ₁} {Δ₀} {Δ₁₀} {.(Ω''' ++ Λ)} {A} {B} refl
  | inj₂ ([] , refl , refl) | inj₁ (.(Δ₁₀ ++ Ω''') , refl , refl) | inj₁ (.(B ⇐ A ∷ Δ₀) , refl , refl)
  | inj₁ (refl , refl , refl) | inj₁ (Ω''' , refl , refl) | F ∷ Δ₁
  rewrite cases++-inj₁ Γ₁ (Δ₀ ++ F ∷ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (F ∷ Δ₁ ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' (Δ₀ ++ F ∷ Δ₁) Λ |
          ++?-inj₁ (F ∷ Δ₁) Δ₀ Ω''' =
    intrp≗
      (~-trans
        (IL~Δ {Δ₀ = []} {Δ₁ = F ∷ Δ₁ ++ Ω'''} refl)
        (~-trans
          (h~ (IL⊗R₁ {Γ = []} {Δ = F ∷ Δ₁} {Λ = Ω'''}))
          (~-sym (⇐L~⊗ (mipIL~Δ Δ₀ [] (F ∷ Δ₁) []) refl))))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Δ₀) (I ∷ Δ) .(F ∷ Ω''' ++ Λ₁) {Γ₁} {Δ₀} {.(Δ ++ F ∷ Ω''')} {Λ₁} {A} {B} refl
  | inj₂ ([] , refl , refl) | inj₁ (Δ , refl , refl) | inj₁ (.(B ⇐ A ∷ Δ₀) , refl , refl)
  | inj₁ (refl , refl , refl) | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ B ⇐ A ∷ Δ₀) (I ∷ Δ ++ F ∷ Ω''' ++ Λ₁) |
          cases++-inj₁ Γ₁ (Δ₀ ++ I ∷ Δ) (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Δ₀ (I ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Δ₀ ++ I ∷ Δ) Ω''' Λ₁ F |
          ++?-inj₁ [] Δ₀ (I ∷ Δ ++ F ∷ Ω''') =
    intrp≗ (IL~Δ {Δ₀ = []} {Δ₁ = Δ} (mip⇐L~Δ Γ₁ Δ₀ Δ F Ω''' Λ₁))
mip≗IL⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₂ (Ω , eq1 , eq2) | inj₁ (Ω' , eqa , eqb) | inj₁ (Ω₀ , eqc , eqd) | inj₂ (Ω'' , eqe , refl) with cases∷ Ω₀ eqc
... | inj₁ (refl , refl , refl) with ++? Ω' Δ₁ Λ Λ₁ eqb
mip≗IL⇐L-assoc .Γ₁ (B ⇐ A ∷ .(Ω'' ++ I ∷ Δ₁ ++ Ω''')) Λ {Γ₁} {Ω''} {Δ₁} {.(Ω''' ++ Λ)} {A} {B} refl
  | inj₂ (.(B ⇐ A ∷ Ω'') , refl , refl) | inj₁ (.(Δ₁ ++ Ω''') , refl , refl) | inj₁ ([] , refl , refl)
  | inj₂ (Ω'' , refl , refl) | inj₁ (refl , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₂ Γ₁ Ω'' (I ∷ Δ₁ ++ Ω''' ++ Λ) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ω'' ++ I ∷ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ Ω'' (Δ₁ ++ Ω''') Λ I |
          cases++-inj₂ [] Γ₁ (Ω'' ++ I ∷ Δ₁ ++ Ω''') (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ω'' ++ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          ++?-inj₁ Ω''' (Ω'' ++ I ∷ Δ₁) Λ |
          cases++-inj₂ [] Γ₁ (Ω'' ++ Δ₁ ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' (Ω'' ++ Δ₁) Λ = intrp≗ (h~ IL⇐L-assoc)
mip≗IL⇐L-assoc .Γ₁ (B ⇐ A ∷ Δ) Λ {Γ₁} {Ω''} {Δ₁} {Λ₁} {A} {B} refl
  | inj₂ (.(B ⇐ A ∷ Ω'') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ ([] , refl , refl)
  | inj₂ (Ω'' , refl , refl) | inj₁ (refl , refl , refl) | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ Γ₁ Ω'' (I ∷ Ω' ++ F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Ω'' Ω' (F ∷ Ω''' ++ Λ₁) I |
          cases++-inj₁ Γ₁ (Ω'' ++ Ω') (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Ω'' ++ Ω') (B ⇐ A) |
          ++?-inj₂ (Ω'' ++ Ω') Ω''' Λ₁ F |
          cases++-inj₁ Γ₁ (Ω'' ++ I ∷ Ω') (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ (Ω'' ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₂ (Ω'' ++ I ∷ Ω') Ω''' Λ₁ F |
          ++?-inj₁ (I ∷ Ω') Ω'' (F ∷ Ω''') =
    intrp≗ (h~ (IL⇐R ∘ ⇐R IL⇐L-assoc))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ω₀'') (E ∷ .(Ω'' ++ I ∷ Ω')) Λ {Γ₁} {.(Ω₀'' ++ E ∷ Ω'')} {Δ₁} {Λ₁} {A} {B} eq
  | inj₂ (.(E ∷ Ω'') , eq1 , eq2) | inj₁ (Ω' , eqa , eqb) | inj₁ (.(B ⇐ A ∷ Ω₀'') , refl , refl)
  | inj₂ (Ω'' , refl , refl) | inj₂ (Ω₀'' , refl , refl)
  with ++? Ω' Δ₁ Λ Λ₁ eqb
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ω₀'') (E ∷ .(Ω'' ++ I ∷ Δ₁ ++ Ω''')) Λ {Γ₁} {.(Ω₀'' ++ E ∷ Ω'')} {Δ₁} {.(Ω''' ++ Λ)} {A} {B} refl
  | inj₂ (.(E ∷ Ω'') , refl , refl) | inj₁ (.(Δ₁ ++ Ω''') , refl , refl) | inj₁ (.(B ⇐ A ∷ Ω₀'') , refl , refl)
  | inj₂ (Ω'' , refl , refl) | inj₂ (Ω₀'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω₀'') Ω'' (I ∷ Δ₁ ++ Ω''' ++ Λ) E |
          cases++-inj₁ Ω'' (Δ₁ ++ Ω''') Λ I |
          cases++-inj₁ Γ₁ (Ω₀'' ++ E ∷ Ω'' ++ I ∷ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ω₀'' ++ E ∷ Ω'' ++ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₀'' (E ∷ Ω'' ++ I ∷ Δ₁ ++ Ω''') (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₀'' (E ∷ Ω'' ++ Δ₁ ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' (Ω₀'' ++ E ∷ Ω'' ++ I ∷ Δ₁) Λ |
          ++?-inj₁ Ω''' (Ω₀'' ++ E ∷ Ω'' ++ Δ₁) Λ |
          ++?-inj₁ (E ∷ Ω'' ++ I ∷ Δ₁) Ω₀'' Ω''' |
          ++?-inj₁ (E ∷ Ω'' ++ Δ₁) Ω₀'' Ω''' |
          ++?-inj₂ Ω₀'' Ω'' (I ∷ Δ₁) E |
          cases++-inj₁ Ω'' Δ₁ [] I =
    intrp≗ (h~ (IL⊗R₁ {Γ = E ∷ Ω''} {Δ = Δ₁} {Λ = Ω'''}))
mip≗IL⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ω₀'') (E ∷ .(Ω'' ++ I ∷ Ω')) .(F ∷ Ω''' ++ Λ₁) {Γ₁} {.(Ω₀'' ++ E ∷ Ω'')} {.(Ω' ++ F ∷ Ω''')} {Λ₁} {A} {B} refl
  | inj₂ (.(E ∷ Ω'') , refl , refl) | inj₁ (Ω' , refl , refl) | inj₁ (.(B ⇐ A ∷ Ω₀'') , refl , refl)
  | inj₂ (Ω'' , refl , refl) | inj₂ (Ω₀'' , refl , refl) | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω₀'') Ω'' (I ∷ Ω' ++ F ∷ Ω''' ++ Λ₁) E |
          cases++-inj₁ Ω'' Ω' (F ∷ Ω''' ++ Λ₁) I |
          cases++-inj₁ Γ₁ (Ω₀'' ++ E ∷ Ω'' ++ I ∷ Ω') (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₀'' (E ∷ Ω'' ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₂ (Ω₀'' ++ E ∷ Ω'' ++ I ∷ Ω') Ω''' Λ₁ F |
          ++?-inj₂ Ω₀'' Ω'' (I ∷ Ω' ++ F ∷ Ω''') E |
          cases++-inj₁ Ω'' Ω' (F ∷ Ω''') I |
          cases++-inj₁ Γ₁ (Ω₀'' ++ E ∷ Ω'' ++ Ω') (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₀'' (E ∷ Ω'' ++ Ω') (B ⇐ A) |
          ++?-inj₂ (Ω₀'' ++ E ∷ Ω'' ++ Ω') Ω''' Λ₁ F = intrp≗ refl
mip≗IL⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} eq | inj₂ (Ω , eq1 , eq2) | inj₁ (Ω' , eqa , eqb) | inj₂ (x , Ω₀ , refl , refl)
  with inj∷ eqa
... | refl , refl with ++? Ω' Δ₁ Λ Λ₁ eqb
mip≗IL⇐L-assoc Γ (x ∷ .(Ω₀ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Δ₁ ++ Ω''')) Λ
  {.(Γ ++ x ∷ Ω₀)} {Δ₀} {Δ₁} {.(Ω''' ++ Λ)} {A} {B} refl
  | inj₂ (.(x ∷ Ω₀ ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | inj₁ (.(Δ₁ ++ Ω''') , refl , refl)
  | inj₂ (x , Ω₀ , refl , refl)
  | refl , refl
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ⇐ A ∷ Δ₀) (I ∷ Δ₁ ++ Ω''' ++ Λ) x |
          cases++-inj₁ (Ω₀ ++ B ⇐ A ∷ Δ₀) (Δ₁ ++ Ω''') Λ I |
          cases++-inj₁ (Γ ++ x ∷ Ω₀) (Δ₀ ++ I ∷ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₁ (Γ ++ x ∷ Ω₀) (Δ₀ ++ Δ₁ ++ Ω''') Λ (B ⇐ A) |
          cases++-inj₂ (x ∷ Ω₀) Γ (Δ₀ ++ I ∷ Δ₁ ++ Ω''') (B ⇐ A) |
          cases++-inj₂ (x ∷ Ω₀) Γ (Δ₀ ++ Δ₁ ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' (Δ₀ ++ I ∷ Δ₁) Λ |
          ++?-inj₁ Ω''' (Δ₀ ++ Δ₁) Λ = intrp≗ (h~ IL⇐L-assoc)
mip≗IL⇐L-assoc Γ (x ∷ .(Ω₀ ++ B ⇐ A ∷ Δ₀ ++ I ∷ Ω')) .(F ∷ Ω''' ++ Λ₁)
  {.(Γ ++ x ∷ Ω₀)} {Δ₀} {.(Ω' ++ F ∷ Ω''')} {Λ₁} {A} {B} refl
  | inj₂ (.(x ∷ Ω₀ ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₂ (x , Ω₀ , refl , refl)
  | refl , refl
  | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ⇐ A ∷ Δ₀) (I ∷ Ω' ++ F ∷ Ω''' ++ Λ₁) x |
          cases++-inj₁ (Ω₀ ++ B ⇐ A ∷ Δ₀) Ω' (F ∷ Ω''' ++ Λ₁) I |
          cases++-inj₁ (Γ ++ x ∷ Ω₀) (Δ₀ ++ I ∷ Ω') (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (x ∷ Ω₀) Γ (Δ₀ ++ I ∷ Ω') (B ⇐ A) |
          ++?-inj₂ (Δ₀ ++ I ∷ Ω') Ω''' Λ₁ F |
          ++?-inj₁ (I ∷ Ω') Δ₀ (F ∷ Ω''') |
          cases++-inj₁ (Γ ++ x ∷ Ω₀) (Δ₀ ++ Ω') (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (x ∷ Ω₀) Γ (Δ₀ ++ Ω') (B ⇐ A) |
          ++?-inj₂ (Δ₀ ++ Ω') Ω''' Λ₁ F = intrp≗ (h~ (IL⇐R ∘ ⇐R IL⇐L-assoc))
mip≗IL⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} eq | inj₂ (Ω , eq1 , eq2) | inj₂ (Ω' , refl , refl) | inj₁ (Ω₀ , eqc , refl) with cases∷ Ω₀ eqc
mip≗IL⇐L-assoc .Γ₁ (B ⇐ A ∷ Δ) .(I ∷ Λ₁)
  {Γ₁} {.Δ} {[]} {Λ₁} {A} {B} {C} {f} {g} refl
  | inj₂ (.(B ⇐ A ∷ Δ) , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ Γ₁ Δ (I ∷ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Δ Λ₁ I |
          cases++-inj₁ Γ₁ Δ Λ₁ (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₁ [] Δ Λ₁ |
          cases++-inj₁ Γ₁ Δ (I ∷ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₂ Δ [] Λ₁ I |
          ++?-inj₁ [] Δ (I ∷ []) =
    let H = mip Γ₁ (B ∷ []) Λ₁ g refl
        t : (MIP.D H ⇐ I) ∷ [] ⊢ MIP.D H
        t = ⇐L {Γ = []} {Δ = []} {Λ = []}
              {A = I} {B = MIP.D H} {C = MIP.D H} IR ax
        eqg :
          ⇐L {Γ = Γ₁} {Δ = I ∷ []} {Λ = Λ₁}
            {A = I} {B = MIP.D H} {C = C}
            (IL {Γ = []} {Δ = []} IR) (MIP.g H)
          ≗ cut Γ₁ t
              (IL {Γ = Γ₁ ++ MIP.D H ∷ []} {Δ = Λ₁}
                (MIP.g H))
              refl
        eqg =
          (((~ (IL⇐L-assoc {Γ = Γ₁} {Δ₀ = []} {Δ₁ = []} {Λ = Λ₁}
                {A = I} {B = MIP.D H} {C = C}
                {f = IR} {g = MIP.g H}))
            ∘ IL {Γ = Γ₁ ++ MIP.D H ⇐ I ∷ []} {Δ = Λ₁}
                (~ ((cut⇐L≗ Γ₁ IR ax (MIP.g H) refl)
                  ∘ ⇐L refl (cutaxA-left Γ₁ (MIP.g H) refl))))
           ∘ ≡to≗ (cutIL-cases++₂ Γ₁ [] Λ₁))
        eqh :
          cut []
            (⇐R {Γ = B ⇐ A ∷ Δ} {A = I} {B = MIP.D H}
              (⇐L {Γ = []} {Δ = Δ ++ I ∷ []} {Λ = []}
                {A = A} {B = B} {C = MIP.D H}
                (IL {Γ = Δ} {Δ = []} f) (MIP.h H)))
            t refl
          ≗ ⇐L {Γ = []} {Δ = Δ} {Λ = []}
              {A = A} {B = B} {C = MIP.D H}
              f (MIP.h H)
        eqh = cut⇐R⇐LIL⇐ Δ f (MIP.h H)
    in intrp≗ (↜∷ (t , eqg , eqh) refl)
  where
    cut⇐R⇐LIL⇐ : ∀ Δ {A B D : Fma}
      → (f : Δ ⊢ A) → (h : B ∷ [] ⊢ D)
      → cut []
          (⇐R {Γ = B ⇐ A ∷ Δ} {A = I} {B = D}
            (⇐L {Γ = []} {Δ = Δ ++ I ∷ []} {Λ = []}
              {A = A} {B = B} {C = D}
              (IL {Γ = Δ} {Δ = []} f) h))
          (⇐L {Γ = []} {Δ = []} {Λ = []}
            {A = I} {B = D} {C = D} IR ax)
          refl
        ≗ ⇐L {Γ = []} {Δ = Δ} {Λ = []}
            {A = A} {B = B} {C = D} f h
    cut⇐R⇐LIL⇐ Δ f h
      rewrite cases++-inj₁ Δ [] [] I |
              cases++-inj₂ [] Δ [] I = refl
mip≗IL⇐L-assoc .Γ₁ (B ⇐ A ∷ Δ) .(I ∷ E' ∷ Δ' ++ Λ₁)
  {Γ₁} {.Δ} {E' ∷ Δ'} {Λ₁} {A} {B} {C} {f} {g} refl
  | inj₂ (.(B ⇐ A ∷ Δ) , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ Γ₁ Δ (I ∷ E' ∷ Δ' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Δ (E' ∷ Δ' ++ Λ₁) I |
          cases++-inj₁ Γ₁ Δ (E' ∷ Δ' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₂ Δ Δ' Λ₁ E' |
          cases++-inj₁ Γ₁ Δ (I ∷ E' ∷ Δ' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₂ Δ (E' ∷ Δ') Λ₁ I |
          ++?-inj₁ [] Δ (I ∷ E' ∷ Δ') =
    intrp≗ (g~ (IL⇐L-assoc {Γ = Γ₁} {Δ₀ = []} {Δ₁ = E' ∷ Δ'} {Λ = Λ₁}))
mip≗IL⇐L-assoc .Γ₁ (B ⇐ A ∷ Δ) .(F ∷ Ω'' ++ I ∷ Δ₁ ++ Λ₁)
  {Γ₁} {.(Δ ++ F ∷ Ω'')} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} refl
  | inj₂ (.(B ⇐ A ∷ Δ ++ F ∷ Ω'') , refl , refl)
  | inj₂ (F ∷ Ω'' , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  rewrite ++?-inj₂ Γ₁ (Δ ++ F ∷ Ω'') (I ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (F ∷ Ω'') Δ (Δ₁ ++ Λ₁) I |
          cases++-inj₁ Γ₁ Δ (F ∷ Ω'' ++ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₂ Δ (Ω'' ++ Δ₁) Λ₁ F |
          cases++-inj₁ Γ₁ Δ (F ∷ Ω'' ++ I ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ₁ Δ (B ⇐ A) |
          ++?-inj₂ Δ (Ω'' ++ I ∷ Δ₁) Λ₁ F |
          ++?-inj₂ Δ Ω'' (I ∷ Δ₁) F |
          cases++-inj₁ Ω'' Δ₁ [] I =
    intrp≗ (g~ (IL⇐L-assoc {Γ = Γ₁} {Δ₀ = F ∷ Ω''} {Δ₁ = Δ₁} {Λ = Λ₁}))
mip≗IL⇐L-assoc .(Γ₁ ++ Ω₀) (E ∷ Δ) .(Ω' ++ I ∷ Δ₁ ++ Λ₁)
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} refl
  | inj₂ (.(E ∷ Δ ++ Ω') , eq1 , eq2)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (Ω₀'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω₀'') (Δ ++ Ω') (I ∷ Δ₁ ++ Λ₁) E |
          cases++-inj₂ Ω' Δ (Δ₁ ++ Λ₁) I |
          cases++-inj₁ Γ₁ (Ω₀'' ++ E ∷ Δ) (Ω' ++ I ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ω₀'' ++ E ∷ Δ) (Ω' ++ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₀'' (E ∷ Δ) (B ⇐ A) with Ω'
... | F ∷ Ω''
  rewrite ++?-inj₂ (Ω₀'' ++ E ∷ Δ) (Ω'' ++ Δ₁) Λ₁ F |
          ++?-inj₂ (Ω₀'' ++ E ∷ Δ) (Ω'' ++ I ∷ Δ₁) Λ₁ F |
          ++?-inj₂ Ω₀'' (Δ ++ F ∷ Ω'') (I ∷ Δ₁) E |
          cases++-inj₂ (F ∷ Ω'') Δ Δ₁ I =
    let H = mip Ω₀'' (E ∷ Δ) (F ∷ Ω'' ++ Δ₁) f refl
    in intrp≗ (g~ (IL⇐L-assoc {Γ = Γ₁}
      {Δ₀ = Ω₀'' ++ MIP.D H ∷ F ∷ Ω''} {Δ₁ = Δ₁} {Λ = Λ₁}))
... | [] rewrite ++?-inj₂ (Ω₀'' ++ E ∷ Δ) Δ₁ Λ₁ I |
                 ++?-inj₂ Ω₀'' Δ (I ∷ Δ₁) E |
                 cases++-inj₂ [] Δ Δ₁ I with Δ₁
... | [] rewrite ++?-inj₁ [] (Ω₀'' ++ E ∷ Δ) Λ₁ |
                 ++?-inj₁ (E ∷ Δ) Ω₀'' [] =
  let H = mip Ω₀'' (E ∷ Δ) [] f refl
      Γo = Γ₁ ++ B ⇐ A ∷ Ω₀''
      body =
        ⇐L {Γ = Γ₁} {Δ = Ω₀'' ++ MIP.D H ∷ []} {Λ = I ∷ Λ₁}
          (MIP.g H) (IL {Γ₁ ++ B ∷ []} {Λ₁} g)
      eqbody : ⇐L (MIP.g H) g ≗ cut Γo (⊗R ax IR) (⊗L {Γo} {Λ₁} body) refl
      eqbody =
        (((⇐L {Γ₁} refl (~ (cutIRIL (Γ₁ ++ B ∷ []) Λ₁))
          ∘ (~ (≡to≗ (cut⇐L-cases++-comm₁ Γ₁ {Γ₁ = []}
            {Δ = Ω₀'' ++ MIP.D H ∷ []} {Λ = Λ₁}
            {f = IR} {g = MIP.g H}
            {h = IL {Γ₁ ++ B ∷ []} {Λ₁} g}))))
          ∘ (~ (cutaxA-left Γo
            (cut (Γo ++ MIP.D H ∷ []) IR body refl) refl)))
          ∘ (≡to≗ (cut⊗R⊗Lcases++ Γo Λ₁
            {f = ax} {g = IR} {h = body})))
      eqg =
        ((~ (IL⇐L-assoc {Γ = Γ₁}
          {Δ₀ = Ω₀'' ++ MIP.D H ∷ []} {Δ₁ = []} {Λ = Λ₁}))
        ∘ (IL {Γo ++ MIP.D H ∷ []} {Λ₁} eqbody
          ∘ ≡to≗ (cutIL-cases++₂ Γo [] Λ₁
            {f = ⊗R ax IR} {g = ⊗L {Γo} {Λ₁} body})))
  in intrp≗ (↜∷ (⊗R ax IR , eqg , refl) refl)
... | G ∷ Δ₁' rewrite ++?-inj₂ (Ω₀'' ++ E ∷ Δ) Δ₁' Λ₁ G =
  let H = mip Ω₀'' (E ∷ Δ) (G ∷ Δ₁') f refl
  in intrp≗ (g~ (IL⇐L-assoc {Γ = Γ₁}
    {Δ₀ = Ω₀'' ++ MIP.D H ∷ []} {Δ₁ = G ∷ Δ₁'} {Λ = Λ₁}))
mip≗IL⇐L-assoc Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} eq
  | inj₂ (Ω , eq1 , eq2)
  | inj₂ (Ω' , eqa , eqb)
  | inj₂ (x , Ω₀ , eqc , eqd)
  with cases∷ Ω eq1
... | inj₁ (refl , refl , eqtail) = ⊥-elim ([]disj∷ [] eqd)
... | inj₂ (Ω'' , eq1a , refl) with inj∷ eqb | inj∷ eqd
... | refl , eqb2 | refl , eqd2 with cases++ Ω₀ Δ Δ₀ Ω' (trans (sym eqb2) eqd2)
mip≗IL⇐L-assoc Γ (E ∷ .(Ω₀ ++ B ⇐ A ∷ Ωm)) .(Ω' ++ I ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Ω₀)} {.(Ωm ++ Ω')} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} refl
  | inj₂ (.(E ∷ Ω₀ ++ B ⇐ A ∷ Ωm ++ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₂ (E , Ω₀ , refl , refl)
  | inj₂ (.(Ω₀ ++ B ⇐ A ∷ Ωm ++ Ω') , refl , refl)
  | refl , refl
  | refl , refl
  | inj₁ (Ωm , refl , refl)
  rewrite ++?-inj₂ Γ (Ω₀ ++ B ⇐ A ∷ Ωm ++ Ω') (I ∷ Δ₁ ++ Λ₁) E |
          cases++-inj₂ Ω' (Ω₀ ++ B ⇐ A ∷ Ωm) (Δ₁ ++ Λ₁) I |
          cases++-inj₁ (Γ ++ E ∷ Ω₀) Ωm (Ω' ++ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₀) Γ Ωm (B ⇐ A) with Ω'
... | F ∷ Ωp
  rewrite ++?-inj₂ Ωm (Ωp ++ Δ₁) Λ₁ F |
          cases++-inj₁ (Γ ++ E ∷ Ω₀) Ωm (F ∷ Ωp ++ I ∷ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₀) Γ Ωm (B ⇐ A) |
          ++?-inj₂ Ωm (Ωp ++ I ∷ Δ₁) Λ₁ F |
          ++?-inj₂ Ωm Ωp (I ∷ Δ₁) F |
          cases++-inj₁ Ωp Δ₁ [] I =
    intrp≗ (g~ (IL⇐L-assoc {Γ = Γ} {Δ₀ = F ∷ Ωp} {Δ₁ = Δ₁} {Λ = Λ₁}))
... | [] with Δ₁
... | G ∷ Δ₁'
  rewrite ++?-inj₂ Ωm Δ₁' Λ₁ G |
          cases++-inj₁ (Γ ++ E ∷ Ω₀) Ωm (I ∷ G ∷ Δ₁' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₀) Γ Ωm (B ⇐ A) |
          ++?-inj₂ Ωm (G ∷ Δ₁') Λ₁ I |
          ++?-inj₁ [] Ωm (I ∷ G ∷ Δ₁') =
    intrp≗ (g~ (IL⇐L-assoc {Γ = Γ} {Δ₀ = []} {Δ₁ = G ∷ Δ₁'} {Λ = Λ₁}))
... | [] rewrite ++?-inj₁ [] Ωm Λ₁ |
                 cases++-inj₁ (Γ ++ E ∷ Ω₀) Ωm (I ∷ Λ₁) (B ⇐ A) |
                 cases++-inj₂ (E ∷ Ω₀) Γ Ωm (B ⇐ A) |
                 ++?-inj₂ Ωm [] Λ₁ I |
                 ++?-inj₁ [] Ωm (I ∷ []) =
  let H = mip Γ (E ∷ Ω₀ ++ B ∷ []) Λ₁ g refl
      t = ⇐L {Γ = []} {Δ = []} {Λ = []}
            {A = I} {B = MIP.D H} {C = MIP.D H} IR ax
      eqg =
        (((~ (IL⇐L-assoc {Γ = Γ} {Δ₀ = []} {Δ₁ = []} {Λ = Λ₁}
          {A = I} {B = MIP.D H} {C = C}
          {f = IR} {g = MIP.g H}))
          ∘ IL {Γ = Γ ++ MIP.D H ⇐ I ∷ []} {Δ = Λ₁}
              (~ ((cut⇐L≗ Γ IR ax (MIP.g H) refl)
                ∘ ⇐L refl (cutaxA-left Γ (MIP.g H) refl))))
          ∘ ≡to≗ (cutIL-cases++₂ Γ [] Λ₁))
      eqh = cut⇐R⇐LIL⇐₁ (E ∷ Ω₀) Ωm f (MIP.h H)
  in intrp≗ (↜∷ (t , eqg , eqh) refl)
mip≗IL⇐L-assoc Γ (E ∷ Δ) .(Ωs ++ B ⇐ A ∷ Δ₀ ++ I ∷ Δ₁ ++ Λ₁)
  {.(Γ ++ E ∷ Δ ++ Ωs)} {Δ₀} {Δ₁} {Λ₁} {A} {B} {C} {f} {g} refl
  | inj₂ (.(E ∷ Δ ++ Ωs ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | inj₂ (.(Ωs ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | inj₂ (E , .(Δ ++ Ωs) , refl , refl)
  | inj₂ (.(Δ ++ Ωs ++ B ⇐ A ∷ Δ₀) , refl , refl)
  | refl , refl
  | refl , refl
  | inj₂ (Ωs , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ωs ++ B ⇐ A ∷ Δ₀) (I ∷ Δ₁ ++ Λ₁) E |
          cases++-inj₂ (Ωs ++ B ⇐ A ∷ Δ₀) Δ (Δ₁ ++ Λ₁) I |
          cases++-inj₂ Ωs (Γ ++ E ∷ Δ) (Δ₀ ++ Δ₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ Ωs (Γ ++ E ∷ Δ) (Δ₀ ++ I ∷ Δ₁ ++ Λ₁) (B ⇐ A) =
  let H = mip Γ (E ∷ Δ) (Ωs ++ B ∷ Λ₁) g refl
  in intrp≗ (g~ (IL⇐L-assoc {Γ = Γ ++ MIP.D H ∷ Ωs}
    {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = Λ₁}))
