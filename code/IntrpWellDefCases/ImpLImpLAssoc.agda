{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLImpLAssoc where

open import IntrpWellDefCases.Base
open import Data.Sum

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

mip⇒L~⊗mid : ∀ Γ₀ Δ E Λ₁
  {Ω : Cxt} {A B C : Fma}
  {f : Δ ++ E ∷ Ω ⊢ A} {g : Γ₀ ++ B ∷ Λ₁ ⊢ C}
  → mip [] (Γ₀ ++ Δ) (E ∷ Ω ++ A ⇒ B ∷ Λ₁)
      (⇒L {Γ₀} {Δ ++ E ∷ Ω} {Λ₁} f g) refl
      ~ ⇒L~⊗' (mip [] Δ (E ∷ Ω) f refl)
               (mip [] Γ₀ (B ∷ Λ₁) g refl)
mip⇒L~⊗mid [] [] E Λ₁ {f = f} {g = g} =
  ↝∷ (IL {[]} {[]} (⊗R IR IR) , refl , refl) refl
mip⇒L~⊗mid [] (x ∷ Δ) E Λ₁ {Ω} {A} {B}
  rewrite cases++-inj₂ (E ∷ Ω) Δ Λ₁ (A ⇒ B) =
    ↝∷ (⊗R IR ax , ⇒L (~ cutaxA-left [] _ refl) refl , refl) refl
mip⇒L~⊗mid (x ∷ Γ₀) Δ E Λ₁ {Ω} {A} {B}
  rewrite cases++-inj₂ (E ∷ Ω) (Γ₀ ++ Δ) Λ₁ (A ⇒ B) |
          ++?-inj₁ Δ Γ₀ (E ∷ Ω) = refl

mip≗⇒L⇒L-assoc : ∀ Γ Δ Λ
  {Γ₀ Γ₁ Δ₀ Λ₀ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ⊢ A'} {g : Γ₀ ++ B' ∷ Λ₀ ⊢ A} {h : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⇒L {Γ₁ ++ Γ₀} f (⇒L g h)) eq)
      (mip Γ Δ Λ (⇒L (⇒L f g) h) eq)

-- empty middle context: both sides are intrp I (IL …) IR, differing by ⇒L⇒L-assoc inside IL
mip≗⇒L⇒L-assoc Γ [] Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq = mip[]≗ Γ Λ eq ⇒L⇒L-assoc

-- nonempty middle context: mirror mip's ⇒L split on the outer ⇒L of the LHS
-- derivation ⇒L {Γ₁ ++ Γ₀} f (⇒L g h).  NB: Λ_d = Λ₀ ++ A ⇒ B ∷ Λ₁ is compound
-- (the inner ⇒L contributes the second connective), so the ys'-equation of ++?
-- is generally stuck on refl and needs further inj∷/cases++ splitting per case.
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  with ++? Γ (Γ₁ ++ Γ₀ ++ Δ₀) (E ∷ Δ ++ Λ) (A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) eq
... | inj₁ ([] , eq2 , refl) 
  with cases++ Λ₀ Δ Λ₁ Λ (sym (inj∷ eq2 .proj₂)) 
mip≗⇒L⇒L-assoc ._ (A' ⇒ B' ∷ .(Λ₀ ++ A ⇒ B ∷ Ω)) Λ {[]} {Γ₁} {[]} {Λ₀} {.(Ω ++ Λ)} {A} {B} {A'} {B'} {h = f''} refl
  | inj₁ ([] , refl , refl) | inj₁ (Ω , refl , refl) 
  rewrite ++?-inj₂ Γ₁ Λ₀ (A ⇒ B ∷ Ω ++ Λ) (A' ⇒ B') |
          ++?-inj₂ Γ₁ Λ₀ (A ⇒ B ∷ Ω ++ Λ) B' |
          cases++-inj₂ [] Γ₁ Λ₀ B' |
          cases++-inj₂ [] Γ₁ Λ₀ (A' ⇒ B') |
          cases++-inj₁ Λ₀ Ω Λ (A ⇒ B) = 
  let intrp D g h = mip Γ₁ (B ∷ Ω) Λ f'' refl 
  in intrp≗ (↝∷ (⇒R (⇒L {[]} {Λ = []} ax (⇒L {[]} IR ax)) , 
  
     (((⇒L refl (⇒L refl (~ cutaxA-left Γ₁ g refl)) 
     ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
     ∘ (~(cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ ax (⇒L {[]} IR ax) g refl ∘ ⇒L refl (cut⇒L≗ Γ₁ IR ax g refl))))) 
     ∘ (~(≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ [])))) , 
     
     ⇒R (⇒L⇒L-assoc ∘ ⇒L (~ IL⇒L-assoc) refl)) refl)
mip≗⇒L⇒L-assoc ._ (A' ⇒ B' ∷ .(Λ₀ ++ A ⇒ B ∷ Ω)) Λ {[]} {Γ₁} {E ∷ Δ₀} {Λ₀} {.(Ω ++ Λ)} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl
  | inj₁ ([] , refl , refl) | inj₁ (Ω , refl , refl) 
  rewrite ++?-inj₂ (Γ₁ ++ E ∷ Δ₀) Λ₀ (A ⇒ B ∷ Ω ++ Λ) (A' ⇒ B') |
          ++?-inj₂ Γ₁ Λ₀ (A ⇒ B ∷ Ω ++ Λ) B' |
          cases++-inj₂ [] Γ₁ Λ₀ B' |
          cases++-inj₂ (E ∷ Δ₀) Γ₁ Λ₀ (A' ⇒ B') |
          cases++-inj₁ Λ₀ Ω Λ (A ⇒ B) |
          cases++-inj₂ [] Δ₀ Λ₀ (A' ⇒ B') =
  let intrp D g h = mip [] (E ∷ Δ₀) [] f refl
      intrp D'' g'' h'' = mip Γ₁ (B ∷ Ω) Λ f'' refl 
  in intrp≗ (↝∷ (⇒R (⇒L {[]} {Λ = []} ax (⇒L {[]} IR ax)) ,

      (((⇒L refl (⇒L refl (~ cutaxA-left Γ₁ g'' refl)) 
      ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
      ∘ (~ (cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ ax (⇒L {[]} IR ax) g'' refl ∘ ⇒L refl (cut⇒L≗ Γ₁ IR ax g'' refl))))) 
      ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ (E ∷ Δ₀))))) , 
      
      ⇒R (⇒L (cutaxA-left [] g refl) refl ∘ ⇒L⇒L-assoc)) refl)
mip≗⇒L⇒L-assoc .(Γ₁ ++ F ∷ Γ₀ ++ Δ₀) (A' ⇒ B' ∷ .(Λ₀ ++ A ⇒ B ∷ Ω)) Λ {F ∷ Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ ([] , refl , refl) | inj₁ (Ω , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ F ∷ Γ₀ ++ Δ₀) Λ₀ (A ⇒ B ∷ Ω ++ Λ) (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ F ∷ Γ₀) Λ₀ (A ⇒ B ∷ Ω ++ Λ) B' |
          cases++-inj₂ (F ∷ Γ₀) Γ₁ Λ₀ B' |
          cases++-inj₂ (F ∷ Γ₀ ++ Δ₀) Γ₁ Λ₀ (A' ⇒ B') |
          cases++-inj₁ Λ₀ Ω Λ (A ⇒ B) |
          ++?-inj₂ [] (Γ₀ ++ Δ₀) (A' ⇒ B' ∷ Λ₀) F |
          cases++-inj₁ [] Γ₀ Δ₀ F |
          cases++-inj₂ [] (Γ₀ ++ Δ₀) Λ₀ (A' ⇒ B') |
          ++?-inj₁ Δ₀ Γ₀ [] =
    intrp≗ (↜∷ (⇒R (⇒R (⇒L {[]} (⊗R ax ax) ax)) ,

      (((⇒L (≡to≗ (cut⊗Rcases++₂ [] [] (F ∷ Γ₀))) (~ cutaxA-left Γ₁ _ refl)
      ∘ (~ (≡to≗ (cut⇒L-cases++-assoc (F ∷ Γ₀) Γ₁))))
      ∘ cut-cong₂ (Γ₁ ++ F ∷ Γ₀) {g' = (cut (Γ₁ ++ F ∷ Γ₀) (⇒R (⇒L {[]} (⊗R ax ax) ax))
            (⇒L (MIP.h (mip [] (F ∷ Γ₀) (B' ∷ Λ₀) g refl))
          (MIP.g (mip Γ₁ (B ∷ Ω) Λ h refl))) refl)} refl ((~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))
      ∘ (cut-cong₂ Γ₁ refl (~ cut⇒L≗ Γ₁ (⊗R ax ax) ax (MIP.g (mip Γ₁ (B ∷ Ω) Λ h refl)) refl)
      ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ (F ∷ Γ₀)))))))
      ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ (Γ₁ ++ F ∷ Γ₀) Λ Δ₀))) ,
      
      ⇒R (⇒R ((~ ⇒L⇒L-assoc) ∘ ⇒L (cutaxA-left [] _ refl) (⇒L (cutaxA-left [] _ refl) refl)) ∘ (~ ⇒L⇒R {[]}))) refl)
mip≗⇒L⇒L-assoc .(Γ₁ ++ Γ₀ ++ Δ₀) (A' ⇒ B' ∷ Δ) .(Ω ++ A ⇒ B ∷ Λ₁) {Γ₀} {Γ₁} {Δ₀} {.(Δ ++ Ω)} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ ([] , refl , refl) | inj₂ (Ω , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Γ₀ ++ Δ₀) (Δ ++ Ω) (A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Γ₀) (Δ ++ Ω) (A ⇒ B ∷ Λ₁) B' |
          cases++-inj₂ Γ₀ Γ₁ (Δ ++ Ω) B' |
          cases++-inj₂ (Γ₀ ++ Δ₀) Γ₁ (Δ ++ Ω) (A' ⇒ B') |
          cases++-inj₂ Ω Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] (Γ₀ ++ Δ₀) (A' ⇒ B' ∷ Δ ++ Ω) =
    intrp≗ (g~ ⇒L⇒L-assoc)
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (y ∷ Ω , eq2 , refl) with inj∷ eq2
... | refl , eq2' with cases++ Λ₀ Ω Λ₁ (E ∷ Δ ++ Λ) (sym eq2')
mip≗⇒L⇒L-assoc .(Γ₁ ++ Γ₀ ++ Δ₀ ++ ((A' ⇒ B') ∷ Λ₀ ++ (A ⇒ B) ∷ Φ)) (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Φ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.((A' ⇒ B') ∷ Λ₀ ++ (A ⇒ B) ∷ Φ) , refl , refl) | refl , refl | inj₁ (Φ , refl , refl)
  rewrite ++?-inj₁ ((A ⇒ B) ∷ Φ) (Γ₁ ++ Γ₀ ++ B' ∷ Λ₀) (E ∷ Δ ++ Λ) |
          ++?-inj₁ ((A ⇒ B) ∷ Φ) (Γ₁ ++ Γ₀ ++ Δ₀ ++ (A' ⇒ B') ∷ Λ₀) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇒L⇒L-assoc)
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {[]} {Γ₁} {[]} {Λ₂} {Λ₁} {A} {B} {A'} {B'} {f = f} {g = f'} {f''} refl | inj₁ (.(A' ⇒ B') ∷ Λ₀ , refl , refl) | refl , eq2' | inj₂ ([] , refl , refl) 
  rewrite ++?-inj₁ [] (Γ₁ ++ A' ⇒ B' ∷ Λ₂) (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ B' ∷ Λ₂) (A ⇒ B ∷ Δ ++ Λ) = 
  let intrp D' g' h' = mip [] (B' ∷ Λ₂) [] f' refl
      intrp D'' g'' h'' = mip Γ₁ (B ∷ Δ) Λ f'' refl
  in intrp≗ (↝∷ (⇒R (⇒L {[]} {[]} IR (⇒L {[]} ax ax)) ,

     ((((((⇒L⇒L-assoc
     ∘ (~ (⇒L (≡to≗ (cut⇒L-cases++-assoc [] [] {Λ₀ = []} {Ω = []} {f = IR} {g = IL {[]} {[]} f})) refl)))
     ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁))))
     ∘ (~ cut-cong₂ Γ₁ refl (≡to≗ (cut⇒L-cases++-assoc [] Γ₁))))
     ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ Γ₁ (D' ⇒ D'' ∷ Λ) [])))
     ∘ (~ cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ IR (⇒L {[]} ax ax) g'' refl ∘ ⇒L refl (cut⇒L≗ Γ₁ ax ax g'' refl ∘ ⇒L refl (cutaxA-left Γ₁ g'' refl)))))
     ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ (A' ⇒ B' ∷ Λ₀)))) ,

     (⇒R (⇒L refl (⇒L (cutaxA-left [] g' refl) refl)) ∘ ⇒R ⇒L⇒L-assoc)) refl)
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {[]} {Γ₁} {F ∷ Δ₀} {Λ₂} {Λ₁} {A} {B} {A'} {B'} {f = f} {g = f'} {f''} refl | inj₁ (.(A' ⇒ B') ∷ Λ₀ , refl , refl) | refl , eq2' | inj₂ ([] , refl , refl)
  rewrite ++?-inj₁ [] (Γ₁ ++ F ∷ Δ₀ ++ A' ⇒ B' ∷ Λ₂) (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ B' ∷ Λ₂) (A ⇒ B ∷ Δ ++ Λ) |
          cases++-inj₁ Δ₀ Λ₀ [] (A' ⇒ B') = 
  let intrp D' g' h' = mip [] (B' ∷ Λ₂) [] f' refl
      intrp D'' g'' h'' = mip Γ₁ (B ∷ Δ) Λ f'' refl
  in intrp≗ (↝∷ (⇒R (⇒L {[]} {[]} IR (⇒L {[]} ax ax)) ,

     ((((((⇒L⇒L-assoc
     ∘ (~ (⇒L (≡to≗ (cut⇒L-cases++-assoc [] [] {Λ₀ = F ∷ Δ₀} {Ω = []} {f = IR} {g = IL {[]} {F ∷ Δ₀} f})) refl)))
     ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁))))
     ∘ (~ cut-cong₂ Γ₁ refl (≡to≗ (cut⇒L-cases++-assoc [] Γ₁))))
     ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ Γ₁ (D' ⇒ D'' ∷ Λ) [])))
     ∘ (~ cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ IR (⇒L {[]} ax ax) g'' refl ∘ ⇒L refl (cut⇒L≗ Γ₁ ax ax g'' refl ∘ ⇒L refl (cutaxA-left Γ₁ g'' refl)))))
     ∘ (~ ≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ (F ∷ Δ₀ ++ A' ⇒ B' ∷ Λ₀)))) ,

     (⇒R (⇒L refl (⇒L (cutaxA-left [] g' refl) refl)) ∘ ⇒R ⇒L⇒L-assoc)) refl)
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {F ∷ Γ₀} {Γ₁} {Δ₀} {Λ₂} {Λ₁} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl | inj₁ (.(A' ⇒ B') ∷ Λ₀ , refl , refl) | refl , eq2' | inj₂ ([] , refl , refl) 
  rewrite ++?-inj₁ [] (Γ₁ ++ F ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₂) (A ⇒ B ∷ Δ ++ Λ) |
          ++?-inj₁ [] (Γ₁ ++ F ∷ Γ₀ ++ B' ∷ Λ₂) (A ⇒ B ∷ Δ ++ Λ) |
          cases++-inj₁ (Γ₀ ++ Δ₀) Λ₀ [] (A' ⇒ B') = 
  let intrp D' g' h' = mip [] (F ∷ Γ₀ ++ B' ∷ Λ₂) [] f' refl
      intrp D'' g'' h'' = mip Γ₁ (B ∷ Δ) Λ f'' refl
  in intrp≗ (↝∷ (ax , 
     
     (⇒L⇒L-assoc {F ∷ Γ₀} ∘ (~ (cutaxA-left (Γ₁ ++ F ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (⇒L (⇒L f h') g'') refl))) , 
     
     refl) refl)
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₁ (.(A' ⇒ B') ∷ Ω , eq2 , refl) | refl , eq2' | inj₂ (x ∷ Ω' , eq3 , refl) with inj∷ eq3
... | refl , eq3' with cases++ Ω' Δ Λ₁ Λ eq3'
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {[]} {Γ₁} {[]} {.(Ω ++ E ∷ Ω')} {Λ₁} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl | inj₁ (.(A' ⇒ B') ∷ Ω , refl , refl) | refl , refl | inj₂ (E ∷ Ω' , refl , refl) | refl , refl | inj₁ (Φ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B' ∷ Ω) Ω' (A ⇒ B ∷ Φ ++ Λ) E |
          ++?-inj₂ (Γ₁ ++ A' ⇒ B' ∷ Ω) Ω' (A ⇒ B ∷ Φ ++ Λ) E |
          cases++-inj₂ (B' ∷ Ω) Γ₁ Ω' E |
          cases++-inj₂ (A' ⇒ B' ∷ Ω) Γ₁ Ω' E |
          cases++-inj₁ Ω' Φ Λ (A ⇒ B) = 
  let intrp D' g' h' = mip [] (B' ∷ Ω) (E ∷ Ω') f' refl
      intrp D'' g'' h'' = mip Γ₁ (B ∷ Φ) Λ f'' refl
  in intrp≗ (↝∷ (⇒R (⇒L {[]} {[]} IR (⇒L {[]} ax ax)) , 
  
     ((((((⇒L refl ((⇒L refl (~ cutaxA-left Γ₁ _ refl) 
                    ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
                    ∘ (~ (cut-cong₂ Γ₁ refl(cut⇒L≗ Γ₁ ax ax g'' refl)))) 
     ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
     ∘ (~ (cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ (IL f) h' (cut Γ₁ (⇒L ax ax) g'' refl) refl)))) 
     ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (D' ⇒ D'' ∷ Λ) [])))) 
     ∘ (~ (cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ IR (⇒L {[]} ax ax) g'' refl)))) 
     ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ (A' ⇒ B' ∷ Ω)))))) , 
  
     (⇒R (⇒L refl (⇒L (cutaxA-left [] g' refl) refl)) ∘ ⇒R ⇒L⇒L-assoc)) refl)
  
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {[]} {Γ₁} {F ∷ Δ₀} {.(Ω ++ E ∷ Ω')} {Λ₁} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl | inj₁ (.(A' ⇒ B') ∷ Ω , refl , refl) | refl , refl | inj₂ (E ∷ Ω' , refl , refl) | refl , refl | inj₁ (Φ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B' ∷ Ω) Ω' (A ⇒ B ∷ Φ ++ Λ) E |
          ++?-inj₂ (Γ₁ ++ F ∷ Δ₀ ++ A' ⇒ B' ∷ Ω) Ω' (A ⇒ B ∷ Φ ++ Λ) E |
          cases++-inj₂ (B' ∷ Ω) Γ₁ Ω' E |
          cases++-inj₂ (F ∷ Δ₀ ++ A' ⇒ B' ∷ Ω) Γ₁ Ω' E |
          cases++-inj₁ Ω' Φ Λ (A ⇒ B) |
          cases++-inj₁ Δ₀ Ω (E ∷ Ω') (A' ⇒ B') =
  let intrp D' g' h' = mip [] (B' ∷ Ω) (E ∷ Ω') f' refl
      intrp D'' g'' h'' = mip Γ₁ (B ∷ Φ) Λ f'' refl
  in intrp≗ (↝∷ (⇒R (⇒L {[]} {[]} IR (⇒L {[]} ax ax)) , 
  
     (((((⇒L refl ((⇒L refl (~ cutaxA-left Γ₁ _ refl) 
                    ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
                    ∘ (~ (cut-cong₂ Γ₁ refl(cut⇒L≗ Γ₁ ax ax g'' refl)))) 
     ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁)))) 
     ∘ (~ (cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ (IL f) h' (cut Γ₁ (⇒L ax ax) g'' refl) refl)))) 
     ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (D' ⇒ D'' ∷ Λ) [])))) 
     ∘ (~ (cut-cong₂ Γ₁ refl (cut⇒L≗ Γ₁ IR (⇒L {[]} ax ax) g'' refl)))) 
     ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ (F ∷ Δ₀ ++ A' ⇒ B' ∷ Ω))))) , 
  
     (⇒R (⇒L refl (⇒L (cutaxA-left [] g' refl) refl)) ∘ ⇒R ⇒L⇒L-assoc)) refl)
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {F ∷ Γ₀} {Γ₁} {Δ₀} {.(Ω ++ E ∷ Ω')} {Λ₁} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl | inj₁ (.(A' ⇒ B') ∷ Ω , refl , refl) | refl , refl | inj₂ (E ∷ Ω' , refl , refl) | refl , refl | inj₁ (Φ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ F ∷ Γ₀ ++ B' ∷ Ω) Ω' (A ⇒ B ∷ Φ ++ Λ) E |
          ++?-inj₂ (Γ₁ ++ F ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω) Ω' (A ⇒ B ∷ Φ ++ Λ) E |
          cases++-inj₂ (F ∷ Γ₀ ++ B' ∷ Ω) Γ₁ Ω' E |
          cases++-inj₂ (F ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω) Γ₁ Ω' E |
          cases++-inj₁ Ω' Φ Λ (A ⇒ B) |
          cases++-inj₁ (Γ₀ ++ Δ₀) Ω (E ∷ Ω') (A' ⇒ B') = 
  let intrp D' g' h' = mip [] (F ∷ Γ₀ ++ B' ∷ Ω) (E ∷ Ω') f' refl
      intrp D'' g'' h'' = mip Γ₁ (B ∷ Φ) Λ f'' refl
  in intrp≗ (g~ ⇒L⇒L-assoc)
  
mip≗⇒L⇒L-assoc ._ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {.(Ω ++ E ∷ Ω')} {Λ₁} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl | inj₁ (.(A' ⇒ B') ∷ Ω , refl , refl) | refl , refl | inj₂ (E ∷ Ω' , refl , refl) | refl , refl | inj₂ (Φ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Γ₀ ++ B' ∷ Ω) (Δ ++ Φ) (A ⇒ B ∷ Λ₁) E |
          ++?-inj₂ (Γ₁ ++ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω) (Δ ++ Φ) (A ⇒ B ∷ Λ₁) E |
          cases++-inj₂ (Γ₀ ++ B' ∷ Ω) Γ₁ (Δ ++ Φ) E |
          cases++-inj₂ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω) Γ₁ (Δ ++ Φ) E |
          cases++-inj₂ Φ Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ (A' ⇒ B' ∷ Ω) (Γ₀ ++ Δ₀) (E ∷ Δ ++ Φ) = 
  let intrp D' g' h' = mip (Γ₀ ++ B' ∷ Ω) (E ∷ Δ) Φ f' refl 
  in intrp≗ (g~ (⇒L⇒L-assoc {Λ₀ = Ω ++ D' ∷ Φ}))


mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (E₀ , Ω , eq1 , eq2)
  with ++? Γ Γ₁ (E₀ ∷ Ω) (Γ₀ ++ Δ₀) eq1
... | inj₁ (Ω' , eq3 , refl) 
  with cases++ Ω' Γ₀ Ω Δ₀ eq3 
... | inj₁ (Ω'' , refl , refl) 
  with  ++? Ω Δ (A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) Λ (inj∷ eq2 .proj₂) 
... | inj₁ (Ω''' , refl , eq4) 
  with  ++? Δ Ω'' Ω''' Δ₀ eq4
mip≗⇒L⇒L-assoc .(Γ₁ ++ Ω') (E ∷ Δ) .(Ω''' ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) {.(Ω' ++ E₀ ∷ Ω'')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {f'} {f''} refl | inj₂ (E₀ , .(Ω'' ++ Δ₀) , refl , refl) | inj₁ (Ω' , eq3 , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) | inj₁ (Ξ , refl , refl) 
  rewrite ++?-inj₂ (Γ₁ ++ Ω') (Ω'' ++ Ξ ++ Ω''' ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ Ω' Γ₁ (Ω'' ++ Ξ ++ Ω''' ++ A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (Ω''' ++ A' ⇒ B' ∷ Λ₀) (Ω'' ++ Ξ) Λ₁ (A ⇒ B) |
          ++?-inj₂ Ω' (Ω'' ++ Ξ ++ Ω''') (A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₁ Ω' Ω'' (Ξ ++ Ω''') E₀ |
          cases++-inj₂ Ω''' (Ω'' ++ Ξ) Λ₀ (A' ⇒ B') |
          ++?-inj₁ Ξ Ω'' Ω''' |
          cases++-inj₁ (Γ₁ ++ Ω') Ω'' (Ξ ++ Ω''') E₀ |
          cases++-inj₂ Ω'''  (Ω'' ++ Ξ) (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          ++?-inj₁ Ξ Ω'' Ω''' |
          ++?-inj₂ (Γ₁ ++ Ω') (Ω'' ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ Ω' Γ₁ (Ω'' ++ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (B' ∷ Λ₀) Ω'' Λ₁ (A ⇒ B) = 
  let intrp D g h = mip [] Ξ Ω''' f refl
      intrp D' g' h' = mip Ω' (E₀ ∷ Ω'') (B' ∷ Λ₀) f' refl
  in intrp≗ (g~ (⊗L {Γ₁ ++ Ω'} (⇒L⇒L-assoc {Ω' ++ D' ∷ []}) ∘ ⊗L⇒L-assoc {Γ₁} {Ω'} {Ω''' ++ A' ⇒ B' ∷ Λ₀}))

mip≗⇒L⇒L-assoc .(Γ₁ ++ Ω') (E ∷ Δ) .(Ω''' ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) {.(Ω' ++ E₀ ∷ Ω'')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h} refl | inj₂ (E₀ , .(Ω'' ++ Δ₀) , refl , refl) | inj₁ (Ω' , eq3 , refl) | inj₁ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) | inj₂ (E₁ , Ξ , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ E₁ ∷ Ξ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ (Γ₁ ++ Ω') (Δ ++ E₁ ∷ Ξ) Δ₀ E₀ |
          cases++-inj₂ Ω' Γ₁ (Δ ++ E₁ ∷ Ξ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (E₁ ∷ Ξ ++ Δ₀) Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₂ (E₁ ∷ Ξ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Ξ Δ₀ E₁ |
          ++?-inj₂ (Γ₁ ++ Ω') (Δ ++ E₁ ∷ Ξ ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          ++?-inj₂ Ω' (Δ ++ E₁ ∷ Ξ ++ Δ₀) (A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ Ω' Γ₁ (Δ ++ E₁ ∷ Ξ ++ B' ∷ Λ₀) E₀ |
          cases++-inj₁ Ω' (Δ ++ E₁ ∷ Ξ) Δ₀ E₀ |
          cases++-inj₂ (E₁ ∷ Ξ ++ B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          cases++-inj₂ (E₁ ∷ Ξ ++ Δ₀) Δ Λ₀ (A' ⇒ B') |
          ++?-inj₂ Δ Ξ Δ₀ E₁ =
  let intrp D g' h' = mip Ω' (E₀ ∷ Δ) (E₁ ∷ Ξ ++ B' ∷ Λ₀) g refl
  in intrp≗ (g~ (⇒L⇒L-assoc {Γ₀ = Ω' ++ D ∷ E₁ ∷ Ξ} {Γ₁ = Γ₁}))
 
mip≗⇒L⇒L-assoc .(Γ₁ ++ Ω') (E ∷ Δ) Λ {.(Ω' ++ E₀ ∷ Ω'')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (E₀ , .(Ω'' ++ Δ₀) , refl , eq2) | inj₁ (Ω' , eq3 , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (E₁ , Ω''' , refl , eq4)
  with cases++  Λ₀ Ω''' Λ₁ Λ  (sym (inj∷ eq4 .proj₂)) 
mip≗⇒L⇒L-assoc .(Γ₁ ++ Ω') (E ∷ .(Ω'' ++ Δ₀ ++ E₁ ∷ Ω''')) Λ {.(Ω' ++ E₀ ∷ Ω'')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h} refl | inj₂ (E₀ , .(Ω'' ++ Δ₀) , refl , refl) | inj₁ (Ω' , eq3 , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (E₁ , Ω''' , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Ω') Ω'' Δ₀ E₀ |
          ++?-inj₂ (Γ₁ ++ Ω') (Ω'' ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ (Ω'' ++ Δ₀) (Λ₀ ++ A ⇒ B ∷ Ξ) Λ (A' ⇒ B') |
          cases++-inj₂ Ω' Γ₁ (Ω'' ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₂ (Γ₁ ++ Ω') (Ω'' ++ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ (Ω'' ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Ξ Λ (A ⇒ B) |
          cases++-inj₂ Ω' Γ₁ (Ω'' ++ B' ∷ Λ₀) E₀ |
          cases++-inj₁ (Ω'' ++ B' ∷ Λ₀) Ξ Λ (A ⇒ B) =
  let intrp D g₁ h₁ = mip [] Ω' (E₀ ∷ Ω'' ++ B' ∷ Λ₀) g refl
      intrp D' g₂ h₂ = mip Γ₁ (B ∷ Ξ) Λ h refl
  in intrp≗
    (~-trans (h~ (⇒L⇒R ∘ ⇒R ⇒L⇒L-assoc))
      (⇒L~⇒ (~-sym (mip⇒L~Λ∷ [] Ω' E₀ Ω'' Λ₀ {Ω = Δ₀} {f = f} {g = g})) refl))
mip≗⇒L⇒L-assoc .(Γ₁ ++ Ω') (E ∷ .(Ω'' ++ Δ₀ ++ E₁ ∷ Ω''')) Λ {.(Ω' ++ E₀ ∷ Ω'')} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h} refl | inj₂ (E₀ , .(Ω'' ++ Δ₀) , refl , refl) | inj₁ (Ω' , eq3 , refl) | inj₁ (Ω'' , refl , refl) | inj₂ (E₁ , Ω''' , refl , refl) | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ Ω') Ω'' Δ₀ E₀ |
          cases++-inj₁ (Ω'' ++ Δ₀) Ω''' (Ξ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Ω') (Ω'' ++ Δ₀ ++ A' ⇒ B' ∷ Ω''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          ++?-inj₂ (Γ₁ ++ Ω') (Ω'' ++ B' ∷ Ω''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ Ω' Γ₁ (Ω'' ++ B' ∷ Ω''' ++ Ξ) E₀ |
          cases++-inj₂ Ξ (Ω'' ++ B' ∷ Ω''') Λ₁ (A ⇒ B) |
          cases++-inj₂ Ω' Γ₁ (Ω'' ++ Δ₀ ++ A' ⇒ B' ∷ Ω''' ++ Ξ) E₀ |
          cases++-inj₂ Ξ (Ω'' ++ Δ₀ ++ A' ⇒ B' ∷ Ω''') Λ₁ (A ⇒ B) |
          ++?-inj₂ Ω' (Ω'' ++ Δ₀) (A' ⇒ B' ∷ Ω''' ++ Ξ) E₀ |
          cases++-inj₁ Ω' Ω'' Δ₀ E₀ |
          cases++-inj₁ (Ω'' ++ Δ₀) Ω''' Ξ (A' ⇒ B') = intrp≗ refl
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (E₀ , Ω , eq1 , eq2) | inj₁ (Ω' , eq3 , refl) | inj₂ (Ω'' , refl , refl) 
  with ++? Ω Δ (A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) Λ (inj∷ eq2 .proj₂)
mip≗⇒L⇒L-assoc .(Γ₁ ++ Γ₀ ++ Ω'') (E ∷ Δ) Λ {Γ₀} {Γ₁} {.(Ω'' ++ E₀ ∷ Ω)} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E₀ , Ω , refl , refl) | inj₁ (.(Γ₀ ++ Ω'') , eq3 , refl) | inj₂ (Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl)
  rewrite cases++-inj₂ Ω'' (Γ₁ ++ Γ₀) (Δ ++ Ω''') E₀ |
          cases++-inj₂ Ω''' Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Γ₀ ++ Ω'') (Δ ++ Ω''' ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ (Γ₀ ++ Ω'') Γ₁ (Δ ++ Ω''' ++ A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (Ω''' ++ A' ⇒ B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₀ ++ Ω'') (Δ ++ Ω''') (A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ Ω'' Γ₀ (Δ ++ Ω''') E₀ |
          cases++-inj₂ Ω''' Δ Λ₀ (A' ⇒ B') = intrp≗ (g~ ⇒L⇒L-assoc)
... | inj₂ (E₁ , Ω''' , refl , eq5) 
  with cases++ Λ₀ Ω''' Λ₁ Λ (sym (inj∷ eq5 .proj₂))
mip≗⇒L⇒L-assoc .(Γ₁ ++ Γ₀ ++ Ω'') (E ∷ .(Ω ++ E₁ ∷ Ω''')) Λ {Γ₀} {Γ₁} {.(Ω'' ++ E₀ ∷ Ω)} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g = g} {h = h} refl | inj₂ (E₀ , Ω , refl , refl) | inj₁ (.(Γ₀ ++ Ω'') , eq3 , refl) | inj₂ (Ω'' , refl , refl) | inj₂ (E₁ , Ω''' , refl , refl) | inj₁ (Ω'''' , refl , refl)
  rewrite cases++-inj₂ Ω'' (Γ₁ ++ Γ₀) Ω E₀ |
          cases++-inj₁ Ω (Λ₀ ++ A ⇒ B ∷ Ω'''') Λ (A' ⇒ B') |
          ++?-inj₂ (Γ₁ ++ Γ₀) Λ₀ (A ⇒ B ∷ Ω'''' ++ Λ) B' |
          cases++-inj₂ Γ₀ Γ₁ Λ₀ B' |
          cases++-inj₁ Λ₀ Ω'''' Λ (A ⇒ B) |
          ++?-inj₂ (Γ₁ ++ Γ₀ ++ Ω'') (Ω ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Ω'''' ++ Λ) E₀ |
          cases++-inj₂ (Γ₀ ++ Ω'') Γ₁ (Ω ++ A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₁ (Ω ++ A' ⇒ B' ∷ Λ₀) Ω'''' Λ (A ⇒ B) =
  let F = mip [] Ω'' (E₀ ∷ Ω) f refl
      G = mip [] Γ₀ (B' ∷ Λ₀) g refl
      H = mip Γ₁ (B ∷ Ω'''') Λ h refl
  in intrp≗
    (~-trans
      (↜∷
        (⇒R (⇒R (⇒L {[]} (⊗R ax ax) ax)) ,
          (⇒L (≡to≗ (cut⊗Rcases++₂ [] [] Γ₀ {f = MIP.h F} {g = MIP.h G} {h = ax}))
             (~ (cutaxA-left Γ₁ (MIP.g H) refl))
          ∘
          ((~ (≡to≗ (cut⇒L-cases++-assoc Γ₀ Γ₁
             {Λ₀ = []} {Λ₁ = Λ} {Ω = Ω''}
             {f = MIP.h F} {g = ⊗R (MIP.h G) ax}
             {h = cut Γ₁ ax (MIP.g H) refl})))
          ∘
          (cut-cong₂ (Γ₁ ++ Γ₀)
             {f = MIP.h F}
             {g = ⇒L {Γ₁} {Γ₀ ++ MIP.D F ∷ []} {Λ}
                    (⊗R (MIP.h G) ax) (cut Γ₁ ax (MIP.g H) refl)}
             {g' = cut (Γ₁ ++ Γ₀) (⇒R (⇒L {[]} (⊗R ax ax) ax))
                     (⇒L {Γ₁} {Γ₀} {Λ} (MIP.h G) (MIP.g H)) refl}
             refl
             (((~ (≡to≗ (cut⇒L-cases++-assoc [] Γ₁
                 {Λ₀ = MIP.D F ∷ []} {Λ₁ = Λ} {Ω = Γ₀}
                 {f = MIP.h G} {g = ⊗R ax ax}
                 {h = cut Γ₁ ax (MIP.g H) refl})))
             ∘
             (cut-cong₂ Γ₁
                {f = MIP.h G}
                {g = ⇒L {Γ₁} {MIP.D G ∷ MIP.D F ∷ []} {Λ}
                       (⊗R ax ax) (cut Γ₁ ax (MIP.g H) refl)}
                {g' = cut Γ₁
                         (⇒L {[]} {MIP.D G ∷ MIP.D F ∷ []} {[]} (⊗R ax ax) ax)
                         (MIP.g H) refl}
                refl (~ (cut⇒L≗ Γ₁ (⊗R ax ax) ax (MIP.g H) refl))
             ∘
             (~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ Λ Γ₀
                 {f = ⇒L {[]} {MIP.D G ∷ MIP.D F ∷ []} {[]} (⊗R ax ax) ax}
                 {g = MIP.h G} {h = MIP.g H}))))))
          ∘
          (~ (≡to≗ (cut⇒R⇒Lcases++ (Γ₁ ++ Γ₀) Λ Ω''
              {f = ⇒R (⇒L {[]} (⊗R ax ax) ax)}
              {g = MIP.h F}
              {h = ⇒L {Γ₁} {Γ₀} {Λ} (MIP.h G) (MIP.g H)})))))) ,
          ⇒R
            ((⇒R (~ ⇒L⇒L-assoc) ∘ (~ ⇒L⇒R {[]}))
            ∘ ⇒L (cutaxA-left [] _ refl)
                  (⇒R (⇒L (cutaxA-left [] _ refl) refl))))
        refl)
      (⇒L~⇒ (~-sym (mip⇒L~⊗mid Γ₀ Ω'' E₀ Λ₀ {Ω = Ω} {f = f} {g = g})) refl))
mip≗⇒L⇒L-assoc .(Γ₁ ++ Γ₀ ++ Ω'') (E ∷ .(Ω ++ E₁ ∷ Ω''')) Λ {Γ₀} {Γ₁} {.(Ω'' ++ E₀ ∷ Ω)} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E₀ , Ω , refl , refl) | inj₁ (.(Γ₀ ++ Ω'') , eq3 , refl) | inj₂ (Ω'' , refl , refl) | inj₂ (E₁ , Ω''' , refl , refl) | inj₂ (Ω'''' , refl , refl)
  rewrite cases++-inj₂ Ω'' (Γ₁ ++ Γ₀) Ω E₀ |
          ++?-inj₂ (Γ₁ ++ Γ₀ ++ Ω'') (Ω ++ A' ⇒ B' ∷ Ω''' ++ Ω'''') (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Ω Ω''' (Ω'''' ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₂ (Γ₀ ++ Ω'') Γ₁ (Ω ++ A' ⇒ B' ∷ Ω''' ++ Ω'''') E₀ |
          ++?-inj₂ (Γ₁ ++ Γ₀) (Ω''' ++ Ω'''') (A ⇒ B ∷ Λ₁) B' |
          cases++-inj₂ Γ₀ Γ₁ (Ω''' ++ Ω'''') B' |
          cases++-inj₂ Ω'''' Ω''' Λ₁ (A ⇒ B) |
          cases++-inj₂ Ω'''' (Ω ++ A' ⇒ B' ∷ Ω''') Λ₁ (A ⇒ B) |
          ++?-inj₂ (Γ₀ ++ Ω'') Ω (A' ⇒ B' ∷ Ω''' ++ Ω'''') E₀ |
          cases++-inj₂ Ω'' Γ₀ Ω E₀ |
          cases++-inj₁ Ω Ω''' Ω'''' (A' ⇒ B') = intrp≗ (g~ ⇒L⇒L-assoc)
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (E₀ , Ω , eq1 , eq2) | inj₂ (E₁ , Ω' , refl , refl) 
  with  ++? Ω' Δ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) Λ (inj∷ eq2 .proj₂)
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {[]} {._} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , ._ , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ Δ Δ₀ E₀ |
          cases++-inj₂ Δ₀ Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          ++?-inj₂ Γ (Δ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Γ Δ (Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (Δ₀ ++ A' ⇒ B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Δ (Δ₀ ++ A' ⇒ B' ∷ Λ₀) |
          ++?-inj₁ [] Δ Δ₀ |
          ++?-inj₂ Γ (Δ ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Γ Δ (B' ∷ Λ₀) E₀ |
          cases++-inj₂ (B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Δ (B' ∷ Λ₀) =
  let H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
      k = ⊗L {Γ}
            (⇒L {Γ ++ MIP.D H ∷ []} {I ∷ B' ∷ Λ₀} {Λ₁}
              (IL {[]} {B' ∷ Λ₀} g) (MIP.g H))
      b = ⇒L {Γ ++ (MIP.D H ⊗ I) ∷ []} {I ∷ Δ₀} {Λ₀ ++ A ⇒ B ∷ Λ₁}
            (IL {[]} {Δ₀} f) k
      lhs = intrp ((MIP.D H ⊗ I) ⊗ I)
              (⊗L {Γ} b)
              (⊗R (⊗R (MIP.h H) IR) IR)
      rhs = intrp (MIP.D H ⊗ I)
              (⊗L {Γ}
                (⇒L {Γ ++ MIP.D H ∷ []} {I ∷ Δ₀ ++ A' ⇒ B' ∷ Λ₀} {Λ₁}
                  (IL {[]} {Δ₀ ++ A' ⇒ B' ∷ Λ₀}
                    (⇒L {[]} {Δ₀} {Λ₀} f g))
                  (MIP.g H)))
              (⊗R (MIP.h H) IR)
      eq = ∷↝ {n = rhs} {n' = lhs} {p = lhs}
            (⊗R ax IR ,
              (((((⊗L
                    (⇒L (IL⇒L-comm₁ {Γ = []} {Δ = Δ₀} {Λ = []} {Ω = Λ₀}) refl)
                  ∘ ⊗L
                    (~ (⇒L⇒L-assoc {Γ₀ = I ∷ []} {Γ₁ = Γ ++ MIP.D H ∷ []}
                         {Δ = Δ₀} {Λ₀ = Λ₀} {Λ₁ = Λ₁})))
                  ∘ ⊗L⇒L-comm₁ {Γ = Γ} {Δ = Δ₀} {Λ = []}
                       {Ω = Λ₀ ++ A ⇒ B ∷ Λ₁})
                  ∘ (~ (≡to≗
                       (cut⇒L-cases++-assoc [] (Γ ++ (MIP.D H ⊗ I) ∷ [])
                         {Λ₀ = Δ₀} {Λ₁ = Λ₀ ++ A ⇒ B ∷ Λ₁}
                         {f = IR} {g = IL {[]} {Δ₀} f} {h = k}))))
                  ∘ (~ cutaxA-left Γ
                       (cut (Γ ++ (MIP.D H ⊗ I) ∷ []) IR b refl) refl))
                  ∘ ≡to≗
                    (cut⊗R⊗Lcases++ Γ
                      (Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁)
                      {f = ax} {g = IR} {h = b})) ,
              refl)
            (refl {n = lhs})
  in intrp≗ eq
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {x ∷ Γ₀} {._} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , ._ , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ (Δ ++ x ∷ Γ₀) Δ₀ E₀ |
          cases++-inj₂ (x ∷ Γ₀ ++ Δ₀) Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          ++?-inj₂ Γ (Δ ++ x ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Γ Δ (x ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (x ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Δ (x ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) |
          ++?-inj₂ Ω' Γ₀ Δ₀ x |
          ++?-inj₂ Γ (Ω' ++ x ∷ Γ₀ ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Γ Ω' (x ∷ Γ₀ ++ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (x ∷ Γ₀ ++ B' ∷ Λ₀) Ω' Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Ω' (x ∷ Γ₀ ++ B' ∷ Λ₀) =
    let H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
    in intrp≗
      (g~
        (((~ (⊗L⇒L-comm₁ {Γ = Γ} {Δ = Δ₀} {Λ = x ∷ Γ₀}
                {Ω = Λ₀ ++ A ⇒ B ∷ Λ₁}))
          ∘ ⊗L (⇒L⇒L-assoc {Γ₀ = I ∷ x ∷ Γ₀}
                  {Γ₁ = Γ ++ MIP.D H ∷ []}))
         ∘ ⊗L
             (⇒L (~ (IL⇒L-comm₁ {Γ = []} {Δ = Δ₀}
                       {Λ = x ∷ Γ₀} {Ω = Λ₀}))
               refl)))
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {._} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , ._ , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₁ (x ∷ Ω'' , refl , refl)
  rewrite cases++-inj₁ Γ (Δ ++ x ∷ Ω'' ++ Γ₀) Δ₀ E₀ |
          cases++-inj₂ (x ∷ Ω'' ++ Γ₀ ++ Δ₀) Δ (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          ++?-inj₂ Γ (Δ ++ x ∷ Ω'' ++ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Γ (Δ ++ x ∷ Ω'') (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (x ∷ Ω'' ++ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ (Ω'' ++ Γ₀) Δ₀ x |
          ++?-inj₂ Δ Ω'' (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) x |
          ++?-inj₂ Γ (Δ ++ x ∷ Ω'' ++ Γ₀ ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Γ (Δ ++ x ∷ Ω'') (Γ₀ ++ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (x ∷ Ω'' ++ Γ₀ ++ B' ∷ Λ₀) Δ Λ₁ (A ⇒ B) |
          ++?-inj₂ Δ Ω'' (Γ₀ ++ B' ∷ Λ₀) x =
    let H = mip Γ (E₀ ∷ Δ) (x ∷ Ω'' ++ B ∷ Λ₁) h refl
    in intrp≗ (g~ (⇒L⇒L-assoc {Γ₀ = Γ₀}
                    {Γ₁ = Γ ++ MIP.D H ∷ x ∷ Ω''}))
mip≗⇒L⇒L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq | inj₂ (E₀ , Ω , eq1 , eq2) | inj₂ (E₁ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , eq4)
  with ++? (E₂ ∷ Ω'') Γ₀ Λ (Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) eq4
... | inj₁ (Ω''' , eq5 , eq6) 
  with ++? Ω''' Δ₀ Λ (A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁) eq5
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {[]} {.(Γ ++ E₀ ∷ Ω')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , .(Ω' ++ [] ++ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (Δ₀ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ Ω' (E₂ ∷ Ω'') E₀ |
          ++?-inj₂ Γ (Ω' ++ E₂ ∷ Ω'' ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ [] (Ω' ++ E₂ ∷ Ω'') (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (E₂ ∷ Ω'' ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₁ (E₂ ∷ Ω'') Ω' [] |
          cases++-inj₂ (A' ⇒ B' ∷ Λ₀) (Ω' ++ E₂ ∷ Ω'') Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ (Ω' ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          ++?-inj₁ (E₂ ∷ Ω'') Ω' (A' ⇒ B' ∷ Λ₀) |
          cases++-inj₁ Γ Ω' (B' ∷ Λ₀) E₀ |
          cases++-inj₂ [] Ω'' Λ₀ (A' ⇒ B') |
          cases++-inj₂ (B' ∷ Λ₀) Ω' Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Ω' (B' ∷ Λ₀) =
  let F = mip [] (E₂ ∷ Ω'') [] f refl
      H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
      body = ⇒L {Γ ++ MIP.D H ∷ []} {I ∷ B' ∷ Λ₀} {Λ₁}
               (IL {[]} {B' ∷ Λ₀} g) (MIP.g H)
      K = intrp (MIP.D H ⊗ I) (⊗L {Γ} body) (⊗R (MIP.h H) IR)
      L = ⇒L~Λ' {Γ = Γ} {Δ = E₀ ∷ Ω'} {Λ₀ = []} {Λ₁ = Λ₁} H g
      eqg =
        (((~ (≡to≗
             (cut⇒L-cases++-assoc [] (Γ ++ MIP.D H ∷ [])
               {Λ₀ = B' ∷ Λ₀} {Λ₁ = Λ₁}
               {f = IR} {g = IL {[]} {B' ∷ Λ₀} g} {h = MIP.g H})))
          ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D H ∷ []) IR body refl) refl))
          ∘ ≡to≗
              (cut⊗R⊗Lcases++ Γ (B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁)
                {f = ax} {g = IR} {h = body}))
      inner = ∷↝ {n = L} {n' = K} {p = K} (⊗R ax IR , eqg , refl) refl
  in intrp≗
       (~-trans (⇒L~⊗ refl inner)
         (g~ (⊗L (⇒L⇒L-assoc {Γ₀ = []}
                    {Γ₁ = Γ ++ MIP.D H ∷ []}))))
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {x ∷ Γ₀} {.(Γ ++ E₀ ∷ Ω')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , .(Ω' ++ (x ∷ Γ₀) ++ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (Δ₀ , refl , refl) | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ Γ (Ω' ++ x ∷ Γ₀) Δ₀ E₀ |
          ++?-inj₂ Γ (Ω' ++ x ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ [] (Ω' ++ x ∷ Γ₀ ++ Δ₀) (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (x ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₁ Δ₀ (Ω' ++ x ∷ Γ₀) [] |
          cases++-inj₂ (A' ⇒ B' ∷ Λ₀) (Ω' ++ x ∷ Γ₀ ++ Δ₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ (x ∷ Γ₀ ++ Δ₀) Ω' (A' ⇒ B' ∷ Λ₀) |
          ++?-inj₂ Γ (Ω' ++ x ∷ Γ₀ ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ [] (Γ₀ ++ Δ₀) Λ₀ (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (x ∷ Γ₀ ++ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (B' ∷ Λ₀) (Ω' ++ x ∷ Γ₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ Δ₀ Γ₀ [] |
          ++?-inj₁ (x ∷ Γ₀) Ω' (B' ∷ Λ₀) =
  let F = mip [] Δ₀ [] f refl
      G = mip [] (x ∷ Γ₀) (B' ∷ Λ₀) g refl
      H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
      assocGF = ⊗R (ax {A = MIP.D G}) (ax {A = MIP.D F})
      assocR = ⊗R (ax {A = MIP.D H}) assocGF
      assocL = ⊗L {[]} {MIP.D F ∷ []} assocR
      h12 = ⇒L {MIP.D G ∷ []} {MIP.D F ∷ []} {Λ₀}
              (MIP.g F) (MIP.g G)
      bodyF = ⊗L {[]} {A' ⇒ B' ∷ Λ₀} h12
      body = ⇒L {Γ ++ MIP.D H ∷ []}
                {MIP.D G ⊗ MIP.D F ∷ A' ⇒ B' ∷ Λ₀}
                {Λ₁}
                bodyF
                (MIP.g H)
      target = ⊗L {Γ} body
      hAssocProof =
        let qProof =
              ((~ (cutaxA-left (MIP.D G ∷ []) h12 refl))
               ∘ ((~ (cutaxA-left [] (cut (MIP.D G ∷ []) (ax {A = MIP.D F}) h12 refl) refl))
                  ∘ ≡to≗ (cut⊗R⊗Lcases++ [] (A' ⇒ B' ∷ Λ₀)
                       {f = ax {A = MIP.D G}} {g = ax {A = MIP.D F}} {h = h12})))
        in
        ((⇒L {Γ = Γ ++ MIP.D H ∷ []}
             {Δ = MIP.D G ∷ MIP.D F ∷ A' ⇒ B' ∷ Λ₀}
             {Λ = Λ₁}
             qProof refl
          ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] (Γ ++ MIP.D H ∷ [])
               {Λ₀ = A' ⇒ B' ∷ Λ₀} {Λ₁ = Λ₁}
               {f = assocGF} {g = bodyF} {h = MIP.g H}))))
         ∘ ((~ (cutaxA-left Γ (cut (Γ ++ MIP.D H ∷ []) assocGF body refl) refl))
            ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ (A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁)
                 {f = ax {A = MIP.D H}} {g = assocGF} {h = body})))
  in intrp≗
       (↝∷ (⊗L {[]} assocL ,
              ((⊗L
                  (~ (⊗L⇒L-comm₁ {Γ = Γ} {Δ = MIP.D F ∷ []} {Λ = []}
                        {Ω = Λ₀ ++ A ⇒ B ∷ Λ₁})))
               ∘ ((⊗L (⊗L (⇒L⇒L-assoc {Γ₀ = MIP.D G ∷ []}
                              {Γ₁ = Γ ++ MIP.D H ∷ []})))
                  ∘ ((⊗L (⊗L refl))
                     ∘ ((⊗L (⊗L hAssocProof))
                        ∘ ((⊗L (~ (cut⊗L≗ Γ [] (MIP.D F ∷ []) assocR
                                      target refl)))
                           ∘ (~ (cut⊗L≗ Γ [] [] assocL target refl))))))) ,
              refl)
             refl)
... | inj₁ (x ∷ Ω'''' , eq7 , refl) 
  with cases++  Λ₀ Ω'''' Λ₁ Λ  (sym (inj∷ eq7 .proj₂))
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {[]} {.(Γ ++ E₀ ∷ Ω')} {[]} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E₀ , .(Ω' ++ [] ++ []) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (.([] ++ x ∷ Ω'''') , refl , refl) | inj₁ (x ∷ Ω'''' , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite cases++-inj₁ Γ Ω' [] E₀ |
          ++?-inj₂ Γ (Ω' ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ Ω' (Λ₀ ++ A ⇒ B ∷ Ξ) Λ (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₂ Γ (Ω' ++ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ (Ω' ++ A' ⇒ B' ∷ Λ₀) Ξ Λ (A ⇒ B) |
          cases++-inj₁ Γ Ω' (B' ∷ Λ₀) E₀ |
          cases++-inj₁ (Ω' ++ B' ∷ Λ₀) Ξ Λ (A ⇒ B) =
    intrp≗ (h~ ⇒L⇒L-assoc)
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {[]} {.(Γ ++ E₀ ∷ Ω')} {x₁ ∷ Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E₀ , .(Ω' ++ [] ++ x₁ ∷ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (.((x₁ ∷ Δ₀) ++ x ∷ Ω'''') , refl , refl) | inj₁ (x ∷ Ω'''' , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite cases++-inj₁ Γ Ω' (x₁ ∷ Δ₀) E₀ |
          ++?-inj₂ Γ (Ω' ++ x₁ ∷ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ (Ω' ++ x₁ ∷ Δ₀) (Λ₀ ++ A ⇒ B ∷ Ξ) Λ (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (x₁ ∷ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₂ Γ (Ω' ++ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ Γ Ω' (B' ∷ Λ₀) E₀ |
          cases++-inj₁ (Ω' ++ B' ∷ Λ₀) Ξ Λ (A ⇒ B) |
          cases++-inj₁ (Ω' ++ x₁ ∷ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Ξ Λ (A ⇒ B) =
    intrp≗ (h~ ⇒L⇒L-assoc)
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {x₁ ∷ Γ₀} {.(Γ ++ E₀ ∷ Ω')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E₀ , .(Ω' ++ (x₁ ∷ Γ₀) ++ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (.(Δ₀ ++ x ∷ Ω'''') , refl , refl) | inj₁ (x ∷ Ω'''' , refl , refl) | inj₁ (Ξ , refl , refl)
  rewrite cases++-inj₁ Γ (Ω' ++ x₁ ∷ Γ₀) Δ₀ E₀ |
          ++?-inj₂ Γ (Ω' ++ x₁ ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ (Ω' ++ x₁ ∷ Γ₀ ++ Δ₀) (Λ₀ ++ A ⇒ B ∷ Ξ) Λ (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (x₁ ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₂ Γ (Ω' ++ x₁ ∷ Γ₀ ++ B' ∷ Λ₀) (A ⇒ B ∷ Ξ ++ Λ) E₀ |
          cases++-inj₁ Γ Ω' (x₁ ∷ Γ₀ ++ B' ∷ Λ₀) E₀ |
          cases++-inj₁ (Ω' ++ x₁ ∷ Γ₀ ++ B' ∷ Λ₀) Ξ Λ (A ⇒ B) |
          cases++-inj₁ (Ω' ++ x₁ ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Ξ Λ (A ⇒ B) =
    intrp≗ (h~ ⇒L⇒L-assoc)
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {[]} {.(Γ ++ E₀ ∷ Ω')} {[]} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f = f} {g} {h} refl | inj₂ (E₀ , .(Ω' ++ [] ++ []) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (.([] ++ x ∷ Ω'''') , refl , refl) | inj₁ (x ∷ Ω'''' , refl , refl) | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₁ Γ Ω' [] E₀ |
          ++?-inj₂ Γ (Ω' ++ A' ⇒ B' ∷ Ω'''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Ω' Ω'''' (Ξ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (A' ⇒ B' ∷ Ω'''' ++ Ξ) E₀ |
          ++?-inj₂ Γ (Ω' ++ B' ∷ Ω'''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ Ξ (Ω' ++ A' ⇒ B' ∷ Ω'''') Λ₁ (A ⇒ B) |
          cases++-inj₁ Γ Ω' (B' ∷ Ω'''' ++ Ξ) E₀ |
          ++?-inj₁ (A' ⇒ B' ∷ Ω'''') Ω' Ξ |
          cases++-inj₂ Ξ (Ω' ++ B' ∷ Ω'''') Λ₁ (A ⇒ B) |
          ++?-inj₁ (B' ∷ Ω'''') Ω' Ξ =
  let H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
      G = mip [] (B' ∷ Ω'''') Ξ g refl
      t' : (I ⇒ MIP.D G) ∷ [] ⊢ MIP.D G
      t' = ⇒L {[]} {[]} {[]} IR ax
      s : MIP.D H ∷ (I ⇒ MIP.D G) ∷ [] ⊢ MIP.D H ⊗ MIP.D G
      s = ⊗R ax t'
      t : (MIP.D H ⊗ (I ⇒ MIP.D G)) ∷ [] ⊢ MIP.D H ⊗ MIP.D G
      t = ⊗L {[]} s
      body : Γ ++ MIP.D H ∷ MIP.D G ∷ Ξ ++ A ⇒ B ∷ Λ₁ ⊢ C
      body = ⇒L {Γ ++ MIP.D H ∷ []} {MIP.D G ∷ Ξ} {Λ₁}
               (MIP.g G) (MIP.g H)
      p : cut [] t' (MIP.g G) refl ≗
          ⇒L {[]} {[]} {Ξ} IR (MIP.g G)
      p = cut⇒L≗ [] {Δ = []} {Δ₀ = []} {Δ₁ = []} {Λ = Ξ}
            IR ax (MIP.g G) refl
            ∘ ⇒L {Γ = []} {Δ = []} {Λ = Ξ}
                refl (cutaxA-left [] (MIP.g G) refl)
      eqg =
        (⊗L
          (((⇒L (~ p) refl
             ∘ (~ (≡to≗
                 (cut⇒L-cases++₁ [] (Γ ++ MIP.D H ∷ [])
                   {Λ = Ξ} {Λ₁ = Λ₁} {f = t'} {g = MIP.g G} {h = MIP.g H}))))
            ∘ (~ (cutaxA-left Γ (cut (Γ ++ MIP.D H ∷ []) t' body refl) refl)))
           ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ (Ξ ++ A ⇒ B ∷ Λ₁)
               {f = ax} {g = t'} {h = body})))
        ∘ (~ (cut⊗L≗ Γ [] [] s (⊗L body) refl))
      eqh = ~ ⇒L⊗R₂
  in intrp≗ (↜∷ (t , eqg , eqh) refl)
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {[]} {.(Γ ++ E₀ ∷ Ω')} {x₁ ∷ Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f = f} {g} {h} refl | inj₂ (E₀ , .(Ω' ++ [] ++ x₁ ∷ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (.((x₁ ∷ Δ₀) ++ x ∷ Ω'''') , refl , refl) | inj₁ (x ∷ Ω'''' , refl , refl) | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₁ Γ Ω' (x₁ ∷ Δ₀) E₀ |
          ++?-inj₂ Γ (Ω' ++ x₁ ∷ Δ₀ ++ A' ⇒ B' ∷ Ω'''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ (Ω' ++ x₁ ∷ Δ₀) Ω'''' (Ξ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (x₁ ∷ Δ₀ ++ A' ⇒ B' ∷ Ω'''' ++ Ξ) E₀ |
          ++?-inj₂ Γ (Ω' ++ B' ∷ Ω'''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ Ξ (Ω' ++ x₁ ∷ Δ₀ ++ A' ⇒ B' ∷ Ω'''') Λ₁ (A ⇒ B) |
          cases++-inj₁ Γ Ω' (B' ∷ Ω'''' ++ Ξ) E₀ |
          ++?-inj₁ (x₁ ∷ Δ₀ ++ A' ⇒ B' ∷ Ω'''') Ω' Ξ |
          cases++-inj₂ Ξ (Ω' ++ B' ∷ Ω'''') Λ₁ (A ⇒ B) |
          cases++-inj₁ Δ₀ Ω'''' Ξ (A' ⇒ B') |
          ++?-inj₁ (B' ∷ Ω'''') Ω' Ξ =
  let H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
      G = mip [] (B' ∷ Ω'''') Ξ g refl
      t' : (I ⇒ MIP.D G) ∷ [] ⊢ MIP.D G
      t' = ⇒L {[]} {[]} {[]} IR ax
      s : MIP.D H ∷ (I ⇒ MIP.D G) ∷ [] ⊢ MIP.D H ⊗ MIP.D G
      s = ⊗R ax t'
      t : (MIP.D H ⊗ (I ⇒ MIP.D G)) ∷ [] ⊢ MIP.D H ⊗ MIP.D G
      t = ⊗L {[]} s
      body : Γ ++ MIP.D H ∷ MIP.D G ∷ Ξ ++ A ⇒ B ∷ Λ₁ ⊢ C
      body = ⇒L {Γ ++ MIP.D H ∷ []} {MIP.D G ∷ Ξ} {Λ₁}
               (MIP.g G) (MIP.g H)
      p : cut [] t' (MIP.g G) refl ≗
          ⇒L {[]} {[]} {Ξ} IR (MIP.g G)
      p = cut⇒L≗ [] {Δ = []} {Δ₀ = []} {Δ₁ = []} {Λ = Ξ}
            IR ax (MIP.g G) refl
            ∘ ⇒L {Γ = []} {Δ = []} {Λ = Ξ}
                refl (cutaxA-left [] (MIP.g G) refl)
      eqg =
        (⊗L
          (((⇒L (~ p) refl
             ∘ (~ (≡to≗
                 (cut⇒L-cases++₁ [] (Γ ++ MIP.D H ∷ [])
                   {Λ = Ξ} {Λ₁ = Λ₁} {f = t'} {g = MIP.g G} {h = MIP.g H}))))
            ∘ (~ (cutaxA-left Γ (cut (Γ ++ MIP.D H ∷ []) t' body refl) refl)))
           ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ (Ξ ++ A ⇒ B ∷ Λ₁)
               {f = ax} {g = t'} {h = body})))
        ∘ (~ (cut⊗L≗ Γ [] [] s (⊗L body) refl))
      eqh = ~ ⇒L⊗R₂
  in intrp≗ (↜∷ (t , eqg , eqh) refl)
mip≗⇒L⇒L-assoc Γ (E ∷ ._) Λ {x₁ ∷ Γ₀} {.(Γ ++ E₀ ∷ Ω')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} refl | inj₂ (E₀ , .(Ω' ++ (x₁ ∷ Γ₀) ++ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (.(Δ₀ ++ x ∷ Ω'''') , refl , refl) | inj₁ (x ∷ Ω'''' , refl , refl) | inj₂ (Ξ , refl , refl)
  rewrite cases++-inj₁ Γ (Ω' ++ x₁ ∷ Γ₀) Δ₀ E₀ |
          ++?-inj₂ Γ (Ω' ++ x₁ ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω'''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ (Ω' ++ x₁ ∷ Γ₀ ++ Δ₀) Ω'''' (Ξ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (x₁ ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω'''' ++ Ξ) E₀ |
          ++?-inj₂ Γ (Ω' ++ x₁ ∷ Γ₀ ++ B' ∷ Ω'''' ++ Ξ) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ Ξ (Ω' ++ x₁ ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω'''') Λ₁ (A ⇒ B) |
          cases++-inj₁ Γ Ω' (x₁ ∷ Γ₀ ++ B' ∷ Ω'''' ++ Ξ) E₀ |
          ++?-inj₁ (x₁ ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω'''') Ω' Ξ |
          cases++-inj₂ Ξ (Ω' ++ x₁ ∷ Γ₀ ++ B' ∷ Ω'''') Λ₁ (A ⇒ B) |
          cases++-inj₁ (Γ₀ ++ Δ₀) Ω'''' Ξ (A' ⇒ B') |
          ++?-inj₁ (x₁ ∷ Γ₀ ++ B' ∷ Ω'''') Ω' Ξ =
    intrp≗ (h~ ⇒L⊗R₂)
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {[]} {.(Γ ++ E₀ ∷ Ω')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , .(Ω' ++ [] ++ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) | inj₂ (E₃ , Ω'''' , refl , refl)
  rewrite cases++-inj₁ Γ Ω' (E₂ ∷ Ω'' ++ E₃ ∷ Ω'''') E₀ |
          ++?-inj₂ Γ (Ω' ++ E₂ ∷ Ω'' ++ E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ (E₃ ∷ Ω'''') (Ω' ++ E₂ ∷ Ω'') (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (E₂ ∷ Ω'' ++ E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₁ (E₂ ∷ Ω'') Ω' (E₃ ∷ Ω'''') |
          cases++-inj₂ (E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) (Ω' ++ E₂ ∷ Ω'') Λ₁ (A ⇒ B) |
          ++?-inj₁ (E₂ ∷ Ω'') Ω' (E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) |
          ++?-inj₂ Γ (Ω' ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₁ Γ Ω' (B' ∷ Λ₀) E₀ |
          cases++-inj₂ (B' ∷ Λ₀) Ω' Λ₁ (A ⇒ B) |
          ++?-inj₁ [] Ω' (B' ∷ Λ₀) |
          cases++-inj₂ (E₃ ∷ Ω'''') Ω'' Λ₀ (A' ⇒ B') =
  let H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
      body = ⇒L {Γ ++ MIP.D H ∷ []} {I ∷ B' ∷ Λ₀} {Λ₁}
               (IL {[]} {B' ∷ Λ₀} g) (MIP.g H)
      K = intrp (MIP.D H ⊗ I) (⊗L {Γ} body) (⊗R (MIP.h H) IR)
      L = ⇒L~Λ' {Γ = Γ} {Δ = E₀ ∷ Ω'} {Λ₀ = []} {Λ₁ = Λ₁} H g
      eqg =
        (((~ (≡to≗
             (cut⇒L-cases++-assoc [] (Γ ++ MIP.D H ∷ [])
               {Λ₀ = B' ∷ Λ₀} {Λ₁ = Λ₁}
               {f = IR} {g = IL {[]} {B' ∷ Λ₀} g} {h = MIP.g H})))
          ∘ (~ cutaxA-left Γ (cut (Γ ++ MIP.D H ∷ []) IR body refl) refl))
          ∘ ≡to≗
              (cut⊗R⊗Lcases++ Γ (B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁)
                {f = ax} {g = IR} {h = body}))
      inner = ∷↝ {n = L} {n' = K} {p = K} (⊗R ax IR , eqg , refl) refl
  in intrp≗
       (~-trans (⇒L~⊗ refl inner)
         (g~ (⊗L (⇒L⇒L-assoc {Γ₀ = []}
                    {Γ₁ = Γ ++ MIP.D H ∷ []}))))
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {x ∷ Γ₀} {.(Γ ++ E₀ ∷ Ω')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , .(Ω' ++ (x ∷ Γ₀) ++ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₁ (Ω''' , refl , refl) | inj₂ (E₃ , Ω'''' , refl , refl)
  rewrite cases++-inj₁ Γ (Ω' ++ x ∷ Γ₀) (Ω''' ++ E₃ ∷ Ω'''') E₀ |
          ++?-inj₂ Γ (Ω' ++ x ∷ Γ₀ ++ Ω''' ++ E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ (E₃ ∷ Ω'''') (Ω' ++ x ∷ Γ₀ ++ Ω''') (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (x ∷ Γ₀ ++ Ω''' ++ E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₁ Ω''' (Ω' ++ x ∷ Γ₀) (E₃ ∷ Ω'''') |
          cases++-inj₂ (E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) (Ω' ++ x ∷ Γ₀ ++ Ω''') Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ (Ω' ++ x ∷ Γ₀ ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          ++?-inj₁ (x ∷ Γ₀ ++ Ω''') Ω' (E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀) |
          cases++-inj₁ Γ Ω' (x ∷ Γ₀ ++ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (E₃ ∷ Ω'''') (Γ₀ ++ Ω''') Λ₀ (A' ⇒ B') |
          cases++-inj₂ (B' ∷ Λ₀) (Ω' ++ x ∷ Γ₀) Λ₁ (A ⇒ B) |
          ++?-inj₁ Ω''' Γ₀ (E₃ ∷ Ω'''') |
          ++?-inj₁ (x ∷ Γ₀) Ω' (B' ∷ Λ₀) =
  let F = mip [] Ω''' (E₃ ∷ Ω'''') f refl
      G = mip [] (x ∷ Γ₀) (B' ∷ Λ₀) g refl
      H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
      assocGF = ⊗R (ax {A = MIP.D G}) (ax {A = MIP.D F})
      assocR = ⊗R (ax {A = MIP.D H}) assocGF
      assocL = ⊗L {[]} {MIP.D F ∷ []} assocR
      h12 = ⇒L {MIP.D G ∷ []} {MIP.D F ∷ E₃ ∷ Ω''''} {Λ₀}
              (MIP.g F) (MIP.g G)
      bodyF = ⊗L {[]} {E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀} h12
      body = ⇒L {Γ ++ MIP.D H ∷ []}
                {MIP.D G ⊗ MIP.D F ∷ E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀}
                {Λ₁}
                bodyF
                (MIP.g H)
      target = ⊗L {Γ} body
      hAssocProof =
        let qProof =
              ((~ (cutaxA-left (MIP.D G ∷ []) h12 refl))
               ∘ ((~ (cutaxA-left [] (cut (MIP.D G ∷ []) (ax {A = MIP.D F}) h12 refl) refl))
                  ∘ ≡to≗ (cut⊗R⊗Lcases++ [] (E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀)
                       {f = ax {A = MIP.D G}} {g = ax {A = MIP.D F}} {h = h12})))
        in
        ((⇒L {Γ = Γ ++ MIP.D H ∷ []}
             {Δ = MIP.D G ∷ MIP.D F ∷ E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀}
             {Λ = Λ₁}
             qProof refl
          ∘ (~ (≡to≗ (cut⇒L-cases++-assoc [] (Γ ++ MIP.D H ∷ [])
               {Λ₀ = E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀} {Λ₁ = Λ₁}
               {f = assocGF} {g = bodyF} {h = MIP.g H}))))
         ∘ ((~ (cutaxA-left Γ (cut (Γ ++ MIP.D H ∷ []) assocGF body refl) refl))
            ∘ ≡to≗ (cut⊗R⊗Lcases++ Γ (E₃ ∷ Ω'''' ++ A' ⇒ B' ∷ Λ₀ ++ A ⇒ B ∷ Λ₁)
                 {f = ax {A = MIP.D H}} {g = assocGF} {h = body})))
  in intrp≗
       (↝∷ (⊗L {[]} assocL ,
              ((⊗L
                  (~ (⊗L⇒L-comm₁ {Γ = Γ}
                        {Δ = MIP.D F ∷ E₃ ∷ Ω''''}
                        {Λ = []}
                        {Ω = Λ₀ ++ A ⇒ B ∷ Λ₁})))
               ∘ ((⊗L (⊗L (⇒L⇒L-assoc {Γ₀ = MIP.D G ∷ []}
                              {Γ₁ = Γ ++ MIP.D H ∷ []})))
                  ∘ ((⊗L (⊗L refl))
                     ∘ ((⊗L (⊗L hAssocProof))
                        ∘ ((⊗L (~ (cut⊗L≗ Γ [] (MIP.D F ∷ []) assocR
                                      target refl)))
                           ∘ (~ (cut⊗L≗ Γ [] [] assocL target refl))))))) ,
              refl)
             refl)
mip≗⇒L⇒L-assoc Γ (E ∷ .(Ω' ++ E₂ ∷ Ω'')) Λ {Γ₀} {.(Γ ++ E₀ ∷ Ω')} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl | inj₂ (E₀ , .(Ω' ++ Γ₀ ++ Δ₀) , refl , refl) | inj₂ (E₀ , Ω' , refl , refl) | inj₂ (E₂ , Ω'' , refl , refl) | inj₂ (E₃ , Ω''' , refl , refl)
  rewrite cases++-inj₁ Γ (Ω' ++ E₂ ∷ Ω'' ++ E₃ ∷ Ω''') Δ₀ E₀ |
          ++?-inj₂ Γ (Ω' ++ E₂ ∷ Ω'' ++ E₃ ∷ Ω''' ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          cases++-inj₂ (E₃ ∷ Ω''' ++ Δ₀) (Ω' ++ E₂ ∷ Ω'') (Λ₀ ++ A ⇒ B ∷ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ Ω' (E₂ ∷ Ω'' ++ E₃ ∷ Ω''' ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) E₀ |
          ++?-inj₂ (Ω' ++ E₂ ∷ Ω'') Ω''' Δ₀ E₃ |
          cases++-inj₂ (E₃ ∷ Ω''' ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (Ω' ++ E₂ ∷ Ω'') Λ₁ (A ⇒ B) |
          ++?-inj₂ Γ (Ω' ++ E₂ ∷ Ω'' ++ E₃ ∷ Ω''' ++ B' ∷ Λ₀) (A ⇒ B ∷ Λ₁) E₀ |
          ++?-inj₁ (E₂ ∷ Ω'') Ω' (E₃ ∷ Ω''' ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) |
          cases++-inj₁ Γ Ω' (E₂ ∷ Ω'' ++ E₃ ∷ Ω''' ++ B' ∷ Λ₀) E₀ |
          cases++-inj₂ (E₃ ∷ Ω''' ++ Δ₀) Ω'' Λ₀ (A' ⇒ B') |
          cases++-inj₂ (E₃ ∷ Ω''' ++ B' ∷ Λ₀) (Ω' ++ E₂ ∷ Ω'') Λ₁ (A ⇒ B) |
          ++?-inj₂ Ω'' Ω''' Δ₀ E₃ |
          ++?-inj₁ (E₂ ∷ Ω'') Ω' (E₃ ∷ Ω''' ++ B' ∷ Λ₀) =
  let G = mip [] (E₂ ∷ Ω'') (E₃ ∷ Ω''' ++ B' ∷ Λ₀) g refl
      H = mip Γ (E₀ ∷ Ω') (B ∷ Λ₁) h refl
  in intrp≗
       (g~
         ((~ (⊗L⇒L-comm₁ {Γ = Γ} {Δ = Δ₀}
                {Λ = E₃ ∷ Ω'''} {Ω = Λ₀ ++ A ⇒ B ∷ Λ₁}))
          ∘ ⊗L
              (⇒L⇒L-assoc {Γ₀ = MIP.D G ∷ E₃ ∷ Ω'''}
                {Γ₁ = Γ ++ MIP.D H ∷ []})))
