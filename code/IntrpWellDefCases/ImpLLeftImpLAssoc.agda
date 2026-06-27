{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLLeftImpLAssoc where

open import IntrpWellDefCases.Base

⇒L⇐L~assoc : ∀ {Γ Γ₀ Δ₀ Δ₁ Λ Λ₀ Λ₁ : Cxt} {A B A' B' C : Fma}
  → (n : MIP [] Δ₀ Δ₁ A')
  → (m : MIP Γ₀ (B' ∷ Λ₀) [] A)
  → (k : MIP Γ (Λ ++ B ∷ []) Λ₁ C)
  → ⇒L~⊗' n (⇐L~⇐' m k) ~ ⇐L~⇐' (⇒L~⇒' n m) k
⇒L⇐L~assoc {Γ} {Γ₀} {Δ₀} {Δ₁} {Λ} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C}
  (intrp D g h) (intrp E g' h') (intrp F g'' h'') =
    let t : ((F ⇐ E) ⊗ D) ∷ [] ⊢ F ⇐ (D ⇒ E)
        t = ⇐R (⊗L {[]}
              (⇐L {Γ = []} {Δ = D ∷ D ⇒ E ∷ []} {Λ = []}
                (⇒L {[]} {D ∷ []} {[]} ax ax) ax))
        p : ⇒L {[]} {D ∷ Δ₁} {Λ₀} g h' ≗
            cut (D ∷ []) (⇒R (⇒L {[]} {D ∷ Δ₁} {Λ₀} g h'))
              (⇒L {[]} {D ∷ []} {[]} ax ax) refl
        p = ⇒L (~ cutaxA-left [] g refl) refl
        impAx : D ∷ D ⇒ E ∷ [] ⊢ E
        impAx = ⇒L {[]} {D ∷ []} {[]} ax ax
        leftAx : F ⇐ E ∷ D ∷ D ⇒ E ∷ [] ⊢ F
        leftAx = ⇐L {[]} {D ∷ D ⇒ E ∷ []} {[]} impAx ax
        tensorLeftAx : (F ⇐ E) ⊗ D ∷ D ⇒ E ∷ [] ⊢ F
        tensorLeftAx = ⊗L {[]} {D ⇒ E ∷ []} {F ⇐ E} {D} leftAx
        eqg =
          ⊗L ⇒L⇐L-assoc
          ∘ ((⊗L (⇐L p refl)
              ∘ (⊗L
                ((~ (≡to≗ (cut⇐L-cases++-assoc (D ∷ []) Γ
                  {Λ₀ = []} {Λ₁ = Λ₁}
                  {Ω = Δ₁ ++ A' ⇒ B' ∷ Λ₀}
                  {A = E} {B = F} {C = C} {D = D ⇒ E}
                  {f = ⇒R (⇒L {[]} {D ∷ Δ₁} {Λ₀} g h')}
                  {g = ⇒L {[]} {D ∷ []} {[]} ax ax}
                  {h = g''})))
                 ∘ cut-cong₂ (Γ ++ F ⇐ E ∷ D ∷ [])
                      refl
                       ((~ (⇐L refl (cutaxA-left Γ g'' refl)))
                       ∘ (~ (cut⇐L≗ Γ impAx ax g'' refl))))
                ∘ (≡to≗ (cut⊗L-cases++₁ Γ [] Λ₁
                  {Δ = Δ₁ ++ A' ⇒ B' ∷ Λ₀}
                  {A = F ⇐ E} {B = D} {C = C} {D = D ⇒ E}
                  {f = ⇒R (⇒L {[]} {D ∷ Δ₁} {Λ₀} g h')}
                  {g = cut Γ leftAx g'' refl})
                  ∘ (~ (cut-cong₂
                    (Γ ++ (F ⇐ E) ⊗ D ∷ [])
                    {Δ = Δ₁ ++ A' ⇒ B' ∷ Λ₀}
                    {Λ = Λ₁}
                    {Ω = Γ ++ (F ⇐ E) ⊗ D ∷ D ⇒ E ∷ Λ₁}
                    {C = C} {D = D ⇒ E}
                    {f = ⇒R (⇒L {[]} {D ∷ Δ₁} {Λ₀} g h')}
                    {g = cut Γ tensorLeftAx g'' refl}
                    {g' = ⊗L (cut Γ leftAx g'' refl)}
                    refl
                    (cut⊗L≗ Γ [] (D ⇒ E ∷ [])
                      leftAx g'' refl))))))
             ∘ (~ (≡to≗ (cut⇐R⇐Lcases++ Γ Λ₁ (Δ₁ ++ A' ⇒ B' ∷ Λ₀)))))
        eqh =
          ⇐R ((≡to≗ (cut⇐L-cases++-assoc Γ₀ Λ))
            ∘ ⇐L
                (cut⇒L≗ Γ₀ h ax g' refl
                 ∘ ⇒L refl (cutaxA-left Γ₀ g' refl))
                refl)
    in ↝∷ (t , eqg , eqh) refl

⇒L⇐L~⇒⊗ : ∀ {Γ Γ₀ Δ₀ Δ₁ Δ₂ Λ Λ₀ : Cxt} {A B A' B' C : Fma}
  → (n : MIP [] Δ₀ Δ₁ A')
  → (m : MIP Γ₀ (B' ∷ Λ₀) [] A)
  → (k : MIP (Γ ++ B ∷ []) Δ₂ Λ C)
  → ⇒L~⇒' n (⇐L~⊗' {Γ₀ = Γ} {Γ₁ = Γ₀} m k)
      ~ ⇐L~⊗' {Γ₀ = Γ} {Γ₁ = Γ₀ ++ Δ₀} (⇒L~⇒' n m) k
⇒L⇐L~⇒⊗ {Γ} {Γ₀} {Δ₀} {Δ₁} {Δ₂} {Λ} {Λ₀} {A} {B} {C = C}
  (intrp D g h) (intrp E g' h') (intrp F g'' h'') =
    let Γa = Γ ++ B ⇐ A ∷ Γ₀
        t = ⇒R (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))
        body : Γa ++ E ∷ F ∷ Λ ⊢ C
        body = ⇐L {Γ} {Γ₀ ++ E ∷ []} {F ∷ Λ} g' g''
        mid :
          ⊗L {Γa ++ Δ₀}
            (⇒L {Γa} {Δ₀} {F ∷ Λ} {D} {E} h body)
          ≗
          cut Γa h
            (cut Γa (⊗L {_ ∷ []} (⇒L {[]} ax (⊗R ax ax)))
              (⊗L {Γa} {Λ} {E} {F} body) refl)
            refl
        mid =
          (⊗L {Γa ++ Δ₀}
            ((⇒L (~ cutaxA-right h) refl
              ∘ (~ ≡to≗ (cut⇒L-cases++₁ [] Γa)))
             ∘
             cut-cong₂ Γa refl
               (⇒L {Γa} {D ∷ []} {F ∷ Λ} {D} {E} refl
                 (((~ cutaxA-left Γa body refl)
                   ∘
                   cut-cong₂ Γa refl
                     (~ cutaxA-left
                       (Γa ++ E ∷ [])
                       body refl))
                  ∘
                  ≡to≗
                    (cut⊗R⊗Lcases++ Γa Λ
                      {f = ax} {ax} {body}))
                ∘
                (~ (cut⇒L≗ Γa
                  {Δ = D ∷ []} {Δ₀ = []} {Δ₁ = F ∷ []}
                  {Λ = Λ} {A = D} {B = E} {C = C} {D = E ⊗ F}
                  ax (⊗R ax ax) (⊗L {Γa} {Λ} {E} {F} body) refl))))
            ∘ ≡to≗ (cut⊗L-cases++₂ Γa [] Λ))
          ∘
          cut-cong₂ Γa refl
            (~ cut⊗L≗ Γa (_ ∷ []) []
              (⇒L {[]} ax (⊗R ax ax))
              (⊗L {Γa} {Λ} {E} {F} body) refl)
        eqg = ⊗L {Γa ++ Δ₀} (~ ⇒L⇐L-assoc)
          ∘ (mid ∘ (~ (≡to≗ (cut⇒R⇒Lcases++ Γa Λ Δ₀))))
        eqh = ⇒R (⊗R (⇒L (cutaxA-left [] _ refl) refl) refl ∘ (~ ⇒L⊗R₁))
    in ↜∷ (t , eqg , eqh) refl

⇒L⇐L~⇒Δ : ∀ {Γ Γ₁ Δ₀ Δ₁ Λ Λ₀ Λ₁ : Cxt} {A B A' B' C : Fma}
  → (n : MIP [] Δ₀ Δ₁ A')
  → (m : MIP Γ (B' ∷ Λ₀) Λ A)
  → (k : Γ₁ ++ B ∷ Λ₁ ⊢ C)
  → ⇒L~⇒' n (⇐L~Δ' m k) ~ ⇐L~Δ' (⇒L~⇒' n m) k
⇒L⇐L~⇒Δ (intrp D g h) (intrp E g' h') k = g~ ⇒L⇐L-assoc

mip≗⇒L⇐L-assoc : ∀ Γ Δ Λ
  {Γ₀ Γ₁ Δ₀ Λ₀ Λ₁ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ⊢ A'} {g : Γ₀ ++ B' ∷ Λ₀ ⊢ A} {h : Γ₁ ++ B ∷ Λ₁ ⊢ C}
  → (eq : Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⇒L {Γ₁ ++ B ⇐ A ∷ Γ₀} {Δ₀} {Λ₀ ++ Λ₁} f (⇐L {Γ₁} {Γ₀ ++ B' ∷ Λ₀} {Λ₁} g h)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁} {Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀} {Λ₁} (⇒L {Γ₀} {Δ₀} {Λ₀} f g) h) eq)
mip≗⇒L⇐L-assoc Γ [] Λ eq = mip[]≗ Γ Λ eq ⇒L⇐L-assoc
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  with ++? Γ (Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) (E ∷ Δ ++ Λ) (A' ⇒ B' ∷ Λ₀ ++ Λ₁) eq
... | inj₁ (Ω , eq₁ , eq₂)
  with cases∷ Ω eq₁
... | inj₁ (refl , refl , eq₃)
  with ++? Δ Λ₀ Λ Λ₁ (sym eq₃)
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) (.(A' ⇒ B') ∷ .(Λ₀ ++ Ω₀)) Λ
  {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω₀ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Λ₀ ++ Ω₀) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Γ₀ (B' ∷ Λ₀ ++ Ω₀) (B ⇐ A) |
          ++?-inj₁ Ω₀ (Γ₀ ++ B' ∷ Λ₀) Λ |
          ++?-inj₁ (B' ∷ Λ₀) Γ₀ Ω₀ |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₀) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀) (A' ⇒ B' ∷ Λ₀ ++ Ω₀) (B ⇐ A) |
          ++?-inj₁ Ω₀ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ |
          ++?-inj₁ (A' ⇒ B' ∷ Λ₀) (Γ₀ ++ Δ₀) Ω₀ |
          ++?-inj₁ [] (Γ₀ ++ Δ₀) (A' ⇒ B' ∷ Λ₀) =
    let F = mip [] Δ₀ [] f refl
        G = mip Γ₀ (B' ∷ Λ₀) [] g refl
        H = mip (Γ₁ ++ B ∷ []) Ω₀ Λ h refl
        t : ((MIP.D F ⇒ MIP.D G) ⊗ MIP.D H) ∷ [] ⊢
            MIP.D F ⇒ (MIP.D G ⊗ MIP.D H)
        t = ⇒R (⊗L {MIP.D F ∷ []}
              (⊗R (⇒L {[]} {MIP.D F ∷ []} {[]} ax ax) ax))
        Γa : Cxt
        Γa = Γ₁ ++ B ⇐ A ∷ Γ₀
        target : Γa ++ MIP.D G ∷ MIP.D H ∷ Λ ⊢ C
        target =
          ⇐L {Γ₁} {Γ₀ ++ MIP.D G ∷ []} {MIP.D H ∷ Λ}
            (MIP.g G) (MIP.g H)
        tensor : MIP.D F ∷ (MIP.D F ⇒ MIP.D G) ∷ MIP.D H ∷ [] ⊢
                 MIP.D G ⊗ MIP.D H
        tensor = ⊗R (⇒L {[]} {MIP.D F ∷ []} {[]} ax ax) ax
        insert :
          target ≗
          cut Γa ax (cut (Γa ++ MIP.D G ∷ []) ax target refl) refl
        insert =
          (~ cutaxA-left Γa target refl)
          ∘ cut-cong₂ Γa refl
              (~ cutaxA-left (Γa ++ MIP.D G ∷ []) target refl)
        inner :
          ⇐L {Γ₁} {Γ₀ ++ MIP.D F ∷ (MIP.D F ⇒ MIP.D G) ∷ []}
            {MIP.D H ∷ Λ}
            (⇒L {Γ₀} {MIP.D F ∷ []} {[]} ax (MIP.g G))
            (MIP.g H)
          ≗ cut Γa tensor (⊗L {Γa} target) refl
        inner =
          (((~ ⇒L⇐L-assoc)
            ∘ ⇒L refl insert)
            ∘ (~ cut⇒L≗ Γa ax ax
                (cut (Γa ++ MIP.D G ∷ []) ax target refl) refl))
          ∘ ≡to≗
              (cut⊗R⊗Lcases++ Γa Λ
                {f = ⇒L {[]} {MIP.D F ∷ []} {[]} ax ax}
                {ax} {target})
        p⇒ :
          ⇒L (MIP.h F) (MIP.g G) ≗
          cut Γ₀ (MIP.h F)
            (⇒L {Γ₀} {MIP.D F ∷ []} {[]} ax (MIP.g G)) refl
        p⇒ =
          ⇒L (~ cutaxA-right (MIP.h F)) refl
          ∘ (~ (≡to≗ (cut⇒L-cases++₁ [] Γ₀)))
        p⇐ :
          ⇐L {Γ₁} {Γ₀ ++ Δ₀ ++ MIP.D F ⇒ MIP.D G ∷ []}
            {MIP.D H ∷ Λ}
            (⇒L (MIP.h F) (MIP.g G)) (MIP.g H)
          ≗ cut Γa (MIP.h F)
              (⇐L {Γ₁} {Γ₀ ++ MIP.D F ∷ (MIP.D F ⇒ MIP.D G) ∷ []}
                {MIP.D H ∷ Λ}
                (⇒L {Γ₀} {MIP.D F ∷ []} {[]} ax (MIP.g G))
                (MIP.g H)) refl
        p⇐ =
          ⇐L {Γ₁} p⇒ refl
          ∘ (~ (≡to≗ (cut⇐L-cases++₁ Γ₀ Γ₁)))
        mid :
          ⊗L {Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀}
            (⇐L {Γ₁} {Γ₀ ++ Δ₀ ++ MIP.D F ⇒ MIP.D G ∷ []}
              {MIP.D H ∷ Λ}
              (⇒L (MIP.h F) (MIP.g G)) (MIP.g H))
          ≗
          cut (Γ₁ ++ B ⇐ A ∷ Γ₀) (MIP.h F)
            (cut (Γ₁ ++ B ⇐ A ∷ Γ₀)
              (⊗L {MIP.D F ∷ []}
                (⊗R (⇒L {[]} {MIP.D F ∷ []} {[]} ax ax) ax))
              (⊗L {Γ₁ ++ B ⇐ A ∷ Γ₀}
                (⇐L {Γ₁} {Γ₀ ++ MIP.D G ∷ []}
                  {MIP.D H ∷ Λ} (MIP.g G) (MIP.g H))) refl)
            refl
        mid =
          ((⊗L {Γa ++ Δ₀} p⇐
            ∘ ≡to≗ (cut⊗L-cases++₂ Γa [] Λ))
            ∘ cut-cong₂ Γa refl
                ((⊗L {Γa ++ MIP.D F ∷ []} inner)
                 ∘ (~ cut⊗L≗ Γa (MIP.D F ∷ []) [] tensor
                      (⊗L {Γa} target) refl)))
    in intrp≗ (↜∷ (t ,
         mid ∘ (~ (≡to≗
           (cut⇒R⇒Lcases++ (Γ₁ ++ B ⇐ A ∷ Γ₀) Λ Δ₀))) ,
          ⇒R (⊗R (⇒L (cutaxA-left [] (MIP.g F) refl) refl) refl
            ∘ (~ ⇒L⊗R₁))) refl)
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) (.(A' ⇒ B') ∷ Δ) .(F ∷ Ω₀ ++ Λ₁)
  {Γ₀} {Γ₁} {Δ₀} {.(Δ ++ F ∷ Ω₀)} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₁ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω₀ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Δ) (F ∷ Ω₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Γ₀ (B' ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ B' ∷ Δ) Ω₀ Λ₁ F |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Δ) (F ∷ Ω₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀) (A' ⇒ B' ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Δ) Ω₀ Λ₁ F |
          ++?-inj₁ [] (Γ₀ ++ Δ₀) (A' ⇒ B' ∷ Δ ++ F ∷ Ω₀) =
    intrp≗ (g~ ⇒L⇐L-assoc)
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , refl)
  with cases++ Ω' Λ₀ (Δ ++ Λ) Λ₁ eq₃
... | inj₁ (Ω₀ , eq₄ , eq₅)
  with ++? Δ Ω₀ Λ Λ₁ (sym eq₅)
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω') (E ∷ .(Ω₀ ++ Ω₁)) Λ
  {Γ₀} {Γ₁} {Δ₀} {.(Ω' ++ E ∷ Ω₀)} {.(Ω₁ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₁ (.(A' ⇒ B' ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Ω' ++ E ∷ Ω₀ ++ Ω₁) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Ω') (E ∷ Ω₀ ++ Ω₁) (B ⇐ A) |
          ++?-inj₁ Ω₁ (Γ₀ ++ B' ∷ Ω' ++ E ∷ Ω₀) Λ |
          ++?-inj₁ (E ∷ Ω₀) (Γ₀ ++ B' ∷ Ω') Ω₁ |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω' ++ E ∷ Ω₀ ++ Ω₁) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω') (E ∷ Ω₀ ++ Ω₁) (B ⇐ A) |
          ++?-inj₁ Ω₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω' ++ E ∷ Ω₀) Λ |
          ++?-inj₁ (E ∷ Ω₀) (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω') Ω₁ |
          ++?-inj₁ (A' ⇒ B' ∷ Ω') (Γ₀ ++ Δ₀) (E ∷ Ω₀) =
    intrp≗
      (g~ ((~ ⊗L⇒L-comm₂)
        ∘ ⊗L {Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω'} ⇒L⇐L-assoc))
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω') (E ∷ Δ) .(F ∷ Ω₁ ++ Λ₁)
  {Γ₀} {Γ₁} {Δ₀} {.(Ω' ++ E ∷ Δ ++ F ∷ Ω₁)} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₁ (.(A' ⇒ B' ∷ Ω') , refl , refl)
  | inj₂ (Ω' , refl , refl)
  | inj₁ (.(Δ ++ F ∷ Ω₁) , refl , refl)
  | inj₂ (F , Ω₁ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Ω' ++ E ∷ Δ) (F ∷ Ω₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Ω') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ B' ∷ Ω' ++ E ∷ Δ) Ω₁ Λ₁ F |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω' ++ E ∷ Δ) (F ∷ Ω₁ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω' ++ E ∷ Δ) Ω₁ Λ₁ F |
          ++?-inj₁ (A' ⇒ B' ∷ Ω') (Γ₀ ++ Δ₀) (E ∷ Δ ++ F ∷ Ω₁) =
    intrp≗ (g~ ⇒L⇐L-assoc)
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₀) (E ∷ Δ) Λ
  {Γ₀} {Γ₁} {Δ₀} {Λ₀} {.(Ω₀ ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₁ (.(A' ⇒ B' ∷ Λ₀ ++ Ω₀) , refl , refl)
  | inj₂ (.(Λ₀ ++ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Λ₀ ++ Ω₀ ++ E ∷ Δ) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Λ₀ ++ Ω₀) (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (Ω₀ ++ E ∷ Δ) (Γ₀ ++ B' ∷ Λ₀) Λ
  with Ω₀
... | [] rewrite ++?-inj₁ [] (Γ₀ ++ B' ∷ Λ₀) (E ∷ Δ) |
                 cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ E ∷ Δ) Λ (B ⇐ A) |
                 cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (E ∷ Δ) (B ⇐ A) |
                 ++?-inj₁ (E ∷ Δ) (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ |
                 ++?-inj₁ [] (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) (E ∷ Δ) =
    intrp≗
      (g~ ((~ ⊗L⇒L-comm₂)
        ∘ ⊗L {Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀}
            (⇒L⇐L-assoc
             ∘ ⇐L (~ IL⇒L-comm₂) refl)))
... | F ∷ Ω₁ rewrite ++?-inj₂ (Γ₀ ++ B' ∷ Λ₀) Ω₁ (E ∷ Δ) F |
                         cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ F ∷ Ω₁ ++ E ∷ Δ) Λ (B ⇐ A) |
                         cases++-inj₁ Γ₁ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ F ∷ Ω₁) (E ∷ Δ) (B ⇐ A) |
                         ++?-inj₁ (F ∷ Ω₁ ++ E ∷ Δ) (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ |
                         ++?-inj₂ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Ω₁ (E ∷ Δ) F =
    intrp≗ (g~ ⇒L⇐L-assoc)
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  with cases++ Γ (Γ₁ ++ B ⇐ A ∷ Γ₀) Ω Δ₀ eq₁
... | inj₁ (Ω₀ , eq₃ , refl)
  with cases++ Γ Γ₁ Ω₀ (B ⇐ A ∷ Γ₀) eq₃
... | inj₁ (Ω₁ , refl , refl)
  with cases++ (Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) Δ (Λ₀ ++ Λ₁) Λ (inj∷ eq₂ .proj₂)
... | inj₁ (Ω₂ , refl , eq₈)
  with ++? Ω₂ Λ₀ Λ Λ₁ eq₈
mip≗⇒L⇐L-assoc Γ (E ∷ .(Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₃)) Λ
  {Γ₀} {.(Γ ++ E ∷ Ω₁)} {Δ₀} {Λ₀} {.(Ω₃ ++ Λ)} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (E , .(Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) , refl , refl)
  | inj₁ (.(Ω₁ ++ B ⇐ A ∷ Γ₀) , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₁ (.(Λ₀ ++ Ω₃) , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  rewrite cases++-inj₁ (Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) (Λ₀ ++ Ω₃) Λ (A' ⇒ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) (Γ₀ ++ B' ∷ Λ₀ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₁) Γ (Γ₀ ++ B' ∷ Λ₀ ++ Ω₃) (B ⇐ A) |
          ++?-inj₁ Ω₃ (Γ₀ ++ B' ∷ Λ₀) Λ |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₃) Λ (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₁) Γ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₃) (B ⇐ A) |
          ++?-inj₁ Ω₃ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ =
    intrp≗ (h~ ⇒L⇐L-assoc)
mip≗⇒L⇐L-assoc Γ (E ∷ .(Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₂)) .(Ω₃ ∷ Ω₄ ++ Λ₁)
  {Γ₀} {.(Γ ++ E ∷ Ω₁)} {Δ₀} {.(Ω₂ ++ Ω₃ ∷ Ω₄)} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (E , .(Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) , refl , refl)
  | inj₁ (.(Ω₁ ++ B ⇐ A ∷ Γ₀) , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  | inj₂ (Ω₃ , Ω₄ , refl , refl)
  rewrite cases++-inj₁ (Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) Ω₂ (Ω₃ ∷ Ω₄ ++ Λ₁) (A' ⇒ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) (Γ₀ ++ B' ∷ Ω₂) (Ω₃ ∷ Ω₄ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₁) Γ (Γ₀ ++ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ B' ∷ Ω₂) Ω₄ Λ₁ Ω₃ |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₂) (Ω₃ ∷ Ω₄ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₁) Γ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₂) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₂) Ω₄ Λ₁ Ω₃ |
          ++?-inj₁ (A' ⇒ B' ∷ Ω₂) (Γ₀ ++ Δ₀) (Ω₃ ∷ Ω₄) =
    intrp≗ (h~ (⇒L⇐R ∘ ⇐R ⇒L⇐L-assoc))
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (Ω₂ , refl , eq₈)
  with ++? Δ (Ω₁ ++ B ⇐ A ∷ Γ₀) Ω₂ Δ₀ eq₈
mip≗⇒L⇐L-assoc Γ (E ∷ .(Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Ω₃)) .(Ω₂ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {Γ₀} {.(Γ ++ E ∷ Ω₁)} {.(Ω₃ ++ Ω₂)} {Λ₀} {Λ₁} {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (E , .(Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Ω₃ ++ Ω₂) , refl , refl)
  | inj₁ (.(Ω₁ ++ B ⇐ A ∷ Γ₀) , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  rewrite cases++-inj₂ Ω₂ (Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Ω₃) (Λ₀ ++ Λ₁) (A' ⇒ B') |
          ++?-inj₁ Ω₃ (Ω₁ ++ B ⇐ A ∷ Γ₀) Ω₂ |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) (Γ₀ ++ Ω₃) (Ω₂ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₁) Γ (Γ₀ ++ Ω₃) (B ⇐ A)
  with Ω₂
... | [] rewrite ++?-inj₂ (Γ₀ ++ Ω₃) Λ₀ Λ₁ (A' ⇒ B') |
                 cases++-inj₁ (Γ ++ E ∷ Ω₁) Γ₀ (B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₁) Γ Γ₀ (B ⇐ A) |
          ++?-inj₂ Γ₀ Λ₀ Λ₁ B' |
          ++?-inj₁ [] (Γ₀ ++ Ω₃) (A' ⇒ B' ∷ Λ₀) =
    intrp≗ (⇒L⇐L~assoc
      (mip [] Ω₃ [] f refl)
      (mip Γ₀ (B' ∷ Λ₀) [] g refl)
      (mip Γ (E ∷ Ω₁ ++ B ∷ []) Λ₁ h refl))
... | H ∷ Ω₄
  rewrite ++?-inj₂ (Γ₀ ++ Ω₃) (Ω₄ ++ A' ⇒ B' ∷ Λ₀) Λ₁ H |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) Γ₀ (B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω₁) Γ Γ₀ (B ⇐ A) |
          ++?-inj₂ Γ₀ Λ₀ Λ₁ B' |
          ++?-inj₂ (Γ₀ ++ Ω₃) Ω₄ (A' ⇒ B' ∷ Λ₀) H |
          cases++-inj₂ Ω₃ Γ₀ Ω₄ H |
          cases++-inj₁ Ω₄ Λ₀ [] (A' ⇒ B') =
    intrp≗ (⇒L⇐L~assoc
      (mip [] Ω₃ (H ∷ Ω₄) f refl)
      (mip Γ₀ (B' ∷ Λ₀) [] g refl)
      (mip Γ (E ∷ Ω₁ ++ B ∷ []) Λ₁ h refl))
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (Ω₂ , refl , eq₈)
  | inj₂ (Ω₃ , Ω₄ , eq₉ , refl)
  with cases++ Ω₁ Δ Γ₀ (Ω₃ ∷ Ω₄) (sym eq₉)
mip≗⇒L⇐L-assoc Γ (E ∷ .(Ω₁ ++ B ⇐ A ∷ Ω₅))
  .(Ω₃ ∷ Ω₄ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {.(Ω₅ ++ Ω₃ ∷ Ω₄)} {.(Γ ++ E ∷ Ω₁)} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (E , .(Ω₁ ++ B ⇐ A ∷ Ω₅ ++ Ω₃ ∷ Ω₄ ++ Δ₀) , refl , refl)
  | inj₁ (.(Ω₁ ++ B ⇐ A ∷ Ω₅ ++ Ω₃ ∷ Ω₄) , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (.(Ω₃ ∷ Ω₄ ++ Δ₀) , refl , refl)
  | inj₂ (Ω₃ , Ω₄ , refl , refl)
  | inj₁ (Ω₅ , refl , refl)
  rewrite cases++-inj₂ (Ω₃ ∷ Ω₄ ++ Δ₀) (Ω₁ ++ B ⇐ A ∷ Ω₅) (Λ₀ ++ Λ₁) (A' ⇒ B') |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) Ω₅
            (Ω₃ ∷ Ω₄ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          ++?-inj₂ (Ω₁ ++ B ⇐ A ∷ Ω₅) Ω₄ Δ₀ Ω₃ |
          cases++-inj₂ (E ∷ Ω₁) Γ Ω₅ (B ⇐ A) |
          cases++-inj₁ (Γ ++ E ∷ Ω₁) Ω₅
            (Ω₃ ∷ Ω₄ ++ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          ++?-inj₂ Ω₅ (Ω₄ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ₁ Ω₃ |
          cases++-inj₂ (E ∷ Ω₁) Γ Ω₅ (B ⇐ A) |
          ++?-inj₂ Ω₅ (Ω₄ ++ Δ₀) (A' ⇒ B' ∷ Λ₀) Ω₃ |
          ++?-inj₂ Ω₅ (Ω₄ ++ B' ∷ Λ₀) Λ₁ Ω₃ |
          cases++-inj₁ Ω₅ Ω₄ Δ₀ Ω₃ |
          cases++-inj₁ (Ω₄ ++ Δ₀) Λ₀ [] (A' ⇒ B') =
    intrp≗ (g~ ⇒L⇐L-assoc)
mip≗⇒L⇐L-assoc Γ (E ∷ Ω₁)
  .(B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {Γ₀} {.(Γ ++ E ∷ Ω₁)} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (E , .(Ω₁ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) , refl , refl)
  | inj₁ (.(Ω₁ ++ B ⇐ A ∷ Γ₀) , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Γ₀ ++ Δ₀) , refl , refl)
  | inj₂ (.(B ⇐ A) , Γ₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  rewrite cases++-inj₂ (B ⇐ A ∷ Γ₀ ++ Δ₀) Ω₁ (Λ₀ ++ Λ₁) (A' ⇒ B') |
          cases++-inj₂ [] (Γ ++ E ∷ Ω₁)
            (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          ++?-inj₂ Ω₁ Γ₀ Δ₀ (B ⇐ A) |
          cases++-inj₂ [] (Γ ++ E ∷ Ω₁)
            (Γ₀ ++ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) =
    intrp≗ (g~ (⇒L⇐L-assoc {Γ₀ = Γ₀}
      {Γ₁ = Γ ++ MIP.D (mip Γ (E ∷ Ω₁) (B ∷ Λ₁) h refl) ∷ []}
      {Δ = Δ₀} {Λ₀ = Λ₀} {Λ₁ = Λ₁}
      {A = A} {A' = A'} {B = B} {B' = B'}))
mip≗⇒L⇐L-assoc Γ (E ∷ Δ)
  .(Ω₃ ∷ Ω₅ ++ B ⇐ A ∷ Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {Γ₀} {.(Γ ++ E ∷ Δ ++ Ω₃ ∷ Ω₅)} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (E , .(Δ ++ Ω₃ ∷ Ω₅ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) , refl , refl)
  | inj₁ (.(Δ ++ Ω₃ ∷ Ω₅ ++ B ⇐ A ∷ Γ₀) , refl , refl)
  | inj₁ (.(Δ ++ Ω₃ ∷ Ω₅) , refl , refl)
  | inj₂ (.(Ω₃ ∷ Ω₅ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) , refl , refl)
  | inj₂ (Ω₃ , .(Ω₅ ++ B ⇐ A ∷ Γ₀) , refl , refl)
  | inj₂ (Ω₃ ∷ Ω₅ , refl , refl)
  rewrite cases++-inj₂ (Ω₃ ∷ Ω₅ ++ B ⇐ A ∷ Γ₀ ++ Δ₀) Δ
            (Λ₀ ++ Λ₁) (A' ⇒ B') |
          ++?-inj₂ Δ (Ω₅ ++ B ⇐ A ∷ Γ₀) Δ₀ Ω₃ |
          cases++-inj₂ (Ω₃ ∷ Ω₅) (Γ ++ E ∷ Δ)
            (Γ₀ ++ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (Ω₃ ∷ Ω₅) (Γ ++ E ∷ Δ)
            (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) =
    intrp≗ (g~ (⇒L⇐L-assoc {Γ₀ = Γ₀}
      {Γ₁ = Γ ++ MIP.D (mip Γ (E ∷ Δ) (Ω₃ ∷ Ω₅ ++ B ∷ Λ₁) h refl) ∷ Ω₃ ∷ Ω₅}
      {Δ = Δ₀} {Λ₀ = Λ₀} {Λ₁ = Λ₁}
      {A = A} {A' = A'} {B = B} {B' = B'}))
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₁ (Ω₀ , eq₃ , eq₄)
  | inj₂ (Ω₁ , eq₅ , eq₆)
  with cases∷ Ω₁ eq₅
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ
  {Γ₀} {.Γ} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} eq
  | inj₂ (.(B ⇐ A) , .(Γ₀ ++ Δ₀) , refl , eq₂)
  | inj₁ (Γ₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  with cases++ (Γ₀ ++ Δ₀) Δ (Λ₀ ++ Λ₁) Λ (inj∷ eq₂ .proj₂)
... | inj₁ (Ω₁ , eq₇ , eq₈)
  with ++? Ω₁ Λ₀ Λ Λ₁ eq₈
mip≗⇒L⇐L-assoc Γ (.(B ⇐ A) ∷ .(Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₂)) Λ
  {Γ₀} {.Γ} {Δ₀} {Λ₀} {.(Ω₂ ++ Λ)}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (.(B ⇐ A) , .(Γ₀ ++ Δ₀) , refl , refl)
  | inj₁ (Γ₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (.(Λ₀ ++ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite cases++-inj₁ Γ (Γ₀ ++ B' ∷ Λ₀ ++ Ω₂) Λ (B ⇐ A) |
          cases++-inj₁ Γ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₂) Λ (B ⇐ A) |
          cases++-inj₂ [] Γ (Γ₀ ++ B' ∷ Λ₀ ++ Ω₂) (B ⇐ A) |
          cases++-inj₂ [] Γ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₂) (B ⇐ A) |
          ++?-inj₁ Ω₂ (Γ₀ ++ B' ∷ Λ₀) Λ |
          ++?-inj₁ Ω₂ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ =
    intrp≗ (h~ (⇒L⇐L-assoc {Γ₀ = Γ₀} {Γ₁ = []}
      {Δ = Δ₀} {Λ₀ = Λ₀} {Λ₁ = Ω₂}
      {A = A} {A' = A'} {B = B} {B' = B'}))
mip≗⇒L⇐L-assoc Γ (.(B ⇐ A) ∷ .(Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₁))
  .(H ∷ Ω₂ ++ Λ₁)
  {Γ₀} {.Γ} {Δ₀} {.(Ω₁ ++ H ∷ Ω₂)} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (.(B ⇐ A) , .(Γ₀ ++ Δ₀) , refl , refl)
  | inj₁ (Γ₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (H , Ω₂ , refl , refl)
  rewrite cases++-inj₁ Γ (Γ₀ ++ B' ∷ Ω₁) (H ∷ Ω₂ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₁)
            (H ∷ Ω₂ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ (Γ₀ ++ B' ∷ Ω₁) (B ⇐ A) |
          cases++-inj₂ [] Γ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₁) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ B' ∷ Ω₁) Ω₂ Λ₁ H |
          ++?-inj₂ (Γ₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₁) Ω₂ Λ₁ H |
          ++?-inj₁ (A' ⇒ B' ∷ Ω₁) (Γ₀ ++ Δ₀) (H ∷ Ω₂) =
    intrp≗ (h~ (⇒L⇐R ∘ ⇐R ⇒L⇐L-assoc))
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ
  {Γ₀} {.Γ} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} eq
  | inj₂ (.(B ⇐ A) , .(Γ₀ ++ Δ₀) , refl , eq₂)
  | inj₁ (Γ₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (Ω₁ , refl , eq₈)
  with ++? Δ Γ₀ Ω₁ Δ₀ eq₈
... | inj₁ (Ω₂ , refl , refl)
  with inj∷ eq₂
mip≗⇒L⇐L-assoc Γ (.(B ⇐ A) ∷ .(Γ₀ ++ Ω₂))
  .(Ω₁ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {Γ₀} {.Γ} {.(Ω₂ ++ Ω₁)} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (.(B ⇐ A) , .(Γ₀ ++ Ω₂ ++ Ω₁) , refl , refl)
  | inj₁ (Γ₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  | refl , refl
  rewrite cases++-inj₁ Γ Γ₀ (B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ Γ₀ (B ⇐ A) |
          cases++-inj₁ Γ (Γ₀ ++ Ω₂)
            (Ω₁ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          ++?-inj₂ Γ₀ Λ₀ Λ₁ B' |
          cases++-inj₂ [] Γ (Γ₀ ++ Ω₂) (B ⇐ A)
  with Ω₁
... | [] rewrite ++?-inj₂ (Γ₀ ++ Ω₂) Λ₀ Λ₁ (A' ⇒ B') |
                 ++?-inj₁ [] (Γ₀ ++ Ω₂) (A' ⇒ B' ∷ Λ₀) =
    intrp≗ (⇒L⇐L~assoc
      (mip [] Ω₂ [] f refl)
      (mip Γ₀ (B' ∷ Λ₀) [] g refl)
      (mip Γ (B ∷ []) Λ₁ h refl))
... | H ∷ Ω₃
  rewrite ++?-inj₂ (Γ₀ ++ Ω₂) (Ω₃ ++ A' ⇒ B' ∷ Λ₀) Λ₁ H |
          ++?-inj₂ (Γ₀ ++ Ω₂) Ω₃ (A' ⇒ B' ∷ Λ₀) H |
          cases++-inj₂ Ω₂ Γ₀ Ω₃ H |
          cases++-inj₁ Ω₃ Λ₀ [] (A' ⇒ B') =
    intrp≗ (⇒L⇐L~assoc
      (mip [] Ω₂ (H ∷ Ω₃) f refl)
      (mip Γ₀ (B' ∷ Λ₀) [] g refl)
      (mip Γ (B ∷ []) Λ₁ h refl))
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) .(Ω₁ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {Γ₀} {Γ} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (.(B ⇐ A) , .(Γ₀ ++ Δ₀) , refl , refl)
  | inj₁ (Γ₀ , refl , refl)
  | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  | inj₂ (H , Ω₂ , refl , refl)
  rewrite cases++-inj₁ Γ Δ (H ∷ Ω₂ ++ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ Δ (H ∷ Ω₂ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ Δ (B ⇐ A) |
          ++?-inj₂ Δ (Ω₂ ++ B' ∷ Λ₀) Λ₁ H |
          ++?-inj₂ Δ (Ω₂ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ₁ H |
          ++?-inj₂ Δ (Ω₂ ++ Δ₀) (A' ⇒ B' ∷ Λ₀) H |
          cases++-inj₁ Δ Ω₂ Δ₀ H |
          cases++-inj₁ (Ω₂ ++ Δ₀) Λ₀ [] (A' ⇒ B') =
    intrp≗ (g~ ⇒L⇐L-assoc)
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ
  {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} eq
  | inj₂ (F , .(Ω₀ ++ Δ₀) , refl , eq₂)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ω₂) , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  with cases++ (Ω₀ ++ Δ₀) Δ (Λ₀ ++ Λ₁) Λ (inj∷ eq₂ .proj₂)
... | inj₁ (Ω₃ , refl , eq₈)
  with ++? Ω₃ Λ₀ Λ Λ₁ eq₈
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ω₂)
  (E ∷ .(Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₃)) Λ
  {.(Ω₂ ++ F ∷ Ω₀)} {Γ₁} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (F , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ω₂) , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  | inj₁ (Ω₄ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Ω₀ ++ B' ∷ Λ₀ ++ Ω₄) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₄) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Ω₀ ++ B' ∷ Λ₀ ++ Ω₄) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Ω₄) (B ⇐ A) |
          ++?-inj₁ Ω₄ (Ω₂ ++ F ∷ Ω₀ ++ B' ∷ Λ₀) Λ |
          ++?-inj₁ Ω₄ (Ω₂ ++ F ∷ Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ |
          ++?-inj₁ (F ∷ Ω₀ ++ B' ∷ Λ₀) Ω₂ Ω₄ |
          ++?-inj₁ (F ∷ Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Ω₂ Ω₄ |
          ++?-inj₂ Ω₂ (Ω₀ ++ Δ₀) (A' ⇒ B' ∷ Λ₀) F |
          cases++-inj₁ Ω₂ Ω₀ Δ₀ F |
          cases++-inj₁ (Ω₀ ++ Δ₀) Λ₀ [] (A' ⇒ B') =
    intrp≗ (h~ ⇒L⊗R₁)
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ω₂)
  (F ∷ .(Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₃)) .(H ∷ Ω₄ ++ Λ₁)
  {.(Ω₂ ++ F ∷ Ω₀)} {Γ₁} {Δ₀} {.(Ω₃ ++ H ∷ Ω₄)} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (F , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ω₂) , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  | inj₂ (H , Ω₄ , refl , refl)
  rewrite cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Ω₀ ++ B' ∷ Ω₃) (H ∷ Ω₄ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₃) (H ∷ Ω₄ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Ω₀ ++ B' ∷ Ω₃) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₃) (B ⇐ A) |
          ++?-inj₂ (Ω₂ ++ F ∷ Ω₀ ++ B' ∷ Ω₃) Ω₄ Λ₁ H |
          ++?-inj₂ (Ω₂ ++ F ∷ Ω₀ ++ Δ₀ ++ A' ⇒ B' ∷ Ω₃) Ω₄ Λ₁ H |
          ++?-inj₂ Ω₂ (Ω₀ ++ Δ₀) (A' ⇒ B' ∷ Ω₃ ++ H ∷ Ω₄) F |
          cases++-inj₁ Ω₂ Ω₀ Δ₀ F |
          cases++-inj₁ (Ω₀ ++ Δ₀) Ω₃ (H ∷ Ω₄) (A' ⇒ B') =
    intrp≗ refl
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ
  {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} eq
  | inj₂ (F , .(Ω₀ ++ Δ₀) , refl , eq₂)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ω₂) , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  | inj₂ (Ω₃ , eq₇ , eq₈)
  with ++? Δ Ω₀ Ω₃ Δ₀ eq₈
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ω₂)
  (F ∷ .(Ω₀ ++ Ω₄)) .(Ω₃ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {.(Ω₂ ++ F ∷ Ω₀)} {Γ₁} {.(Ω₄ ++ Ω₃)} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (F , .(Ω₀ ++ Ω₄ ++ Ω₃) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ω₂) , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  | inj₂ (Ω₃ , refl , refl)
  | inj₁ (Ω₄ , refl , refl)
  rewrite ++?-inj₁ Ω₄ Ω₀ Ω₃ |
          cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Ω₀) (B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Ω₀) (B ⇐ A) |
          ++?-inj₂ (Ω₂ ++ F ∷ Ω₀) Λ₀ Λ₁ B' |
          cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Ω₀ ++ Ω₄)
            (Ω₃ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Ω₀ ++ Ω₄) (B ⇐ A)
  with Ω₃
... | []
  rewrite ++?-inj₂ (Ω₂ ++ F ∷ Ω₀ ++ Ω₄) Λ₀ Λ₁ (A' ⇒ B') |
          ++?-inj₂ Ω₂ (Ω₀ ++ Ω₄) (A' ⇒ B' ∷ Λ₀) F |
          cases++-inj₁ Ω₂ Ω₀ Ω₄ F |
          cases++-inj₂ [] (Ω₀ ++ Ω₄) Λ₀ (A' ⇒ B') |
          ++?-inj₁ Ω₄ Ω₀ [] =
    intrp≗ (g~ ((⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Ω₂} ⇒L⇐L-assoc)
      ∘ ⊗L⇐L-assoc))
... | H ∷ Ω₅
  rewrite ++?-inj₂ (Ω₂ ++ F ∷ Ω₀ ++ Ω₄) (Ω₅ ++ A' ⇒ B' ∷ Λ₀) Λ₁ H |
          ++?-inj₂ Ω₂ (Ω₀ ++ Ω₄ ++ H ∷ Ω₅) (A' ⇒ B' ∷ Λ₀) F |
          cases++-inj₁ Ω₂ Ω₀ (Ω₄ ++ H ∷ Ω₅) F |
          cases++-inj₂ (H ∷ Ω₅) (Ω₀ ++ Ω₄) Λ₀ (A' ⇒ B') |
          ++?-inj₁ Ω₄ Ω₀ (H ∷ Ω₅) =
    intrp≗ (g~ ((⊗L {Γ = Γ₁ ++ B ⇐ A ∷ Ω₂} ⇒L⇐L-assoc)
      ∘ ⊗L⇐L-assoc))
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Ω₂)
  (F ∷ Δ) .(H ∷ Ω₄ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {.(Ω₂ ++ F ∷ Δ ++ H ∷ Ω₄)} {Γ₁} {Δ₀} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (F , .(Δ ++ H ∷ Ω₄ ++ Δ₀) , refl , refl)
  | inj₁ (.(Δ ++ H ∷ Ω₄) , refl , refl)
  | inj₂ (.(B ⇐ A ∷ Ω₂) , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  | inj₂ (.(H ∷ Ω₄ ++ Δ₀) , refl , refl)
  | inj₂ (H , Ω₄ , refl , refl)
  rewrite ++?-inj₂ Δ Ω₄ Δ₀ H |
          cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Δ) (H ∷ Ω₄ ++ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ω₂ ++ F ∷ Δ) (Ω₄ ++ B' ∷ Λ₀) Λ₁ H |
          cases++-inj₁ Γ₁ (Ω₂ ++ F ∷ Δ)
            (H ∷ Ω₄ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω₂ (F ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ω₂ ++ F ∷ Δ) (Ω₄ ++ Δ₀ ++ A' ⇒ B' ∷ Λ₀) Λ₁ H |
          ++?-inj₂ Ω₂ (Δ ++ H ∷ Ω₄ ++ Δ₀) (A' ⇒ B' ∷ Λ₀) F |
          cases++-inj₁ Ω₂ (Δ ++ H ∷ Ω₄) Δ₀ F |
          cases++-inj₂ (H ∷ Ω₄ ++ Δ₀) Δ Λ₀ (A' ⇒ B') |
          ++?-inj₂ Δ Ω₄ Δ₀ H =
    intrp≗ (g~ ⇒L⇐L-assoc)
mip≗⇒L⇐L-assoc Γ (E ∷ Δ) Λ {Γ₀} {Γ₁} {Δ₀} {Λ₀} {Λ₁} {A} {B} {A'} {B'} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₂ (Ω₀ , eq₃ , eq₄)
  with cases++ Ω Δ (Λ₀ ++ Λ₁) Λ (inj∷ eq₂ .proj₂)
... | inj₁ (Ω₁ , refl , eq₅)
  with ++? Ω₁ Λ₀ Λ Λ₁ eq₅
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Ω₀)
  .(F ∷ (Ω ++ ((A' ⇒ B') ∷ Λ₀ ++ Ω₂))) Λ
  {Γ₀} {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Λ₀} {.(Ω₂ ++ Λ)}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₀ ++ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite cases++-inj₁ Ω (Λ₀ ++ Ω₂) Λ (A' ⇒ B') |
          cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Λ₀ ++ Ω₂) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ Γ₀ (B' ∷ Λ₀ ++ Ω₂) (B ⇐ A) |
          ++?-inj₁ Ω₂ (Γ₀ ++ B' ∷ Λ₀) Λ |
          ++?-inj₁ (B' ∷ Λ₀) Γ₀ Ω₂ |
          cases++-inj₁ Γ₁
            (Γ₀ ++ Ω₀ ++ F ∷ Ω ++ (A' ⇒ B') ∷ Λ₀ ++ Ω₂) Λ (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ Ω₀)
            (F ∷ Ω ++ (A' ⇒ B') ∷ Λ₀ ++ Ω₂) (B ⇐ A) |
          ++?-inj₁ Ω₂ (Γ₀ ++ Ω₀ ++ F ∷ Ω ++ (A' ⇒ B') ∷ Λ₀) Λ |
          ++?-inj₁ (F ∷ Ω ++ (A' ⇒ B') ∷ Λ₀) (Γ₀ ++ Ω₀) Ω₂ |
          ++?-inj₂ (Γ₀ ++ Ω₀) Ω ((A' ⇒ B') ∷ Λ₀) F |
          cases++-inj₂ Ω₀ Γ₀ Ω F |
          cases++-inj₁ Ω Λ₀ [] (A' ⇒ B') =
    intrp≗ (⇒L⇐L~⇒⊗
      (mip [] Ω₀ (F ∷ Ω) f refl)
      (mip Γ₀ (B' ∷ Λ₀) [] g refl)
      (mip (Γ₁ ++ B ∷ []) Ω₂ Λ h refl))
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Ω₀)
  .(F ∷ (Ω ++ (A' ⇒ B') ∷ Ω₁)) .(H ∷ Ω₂ ++ Λ₁)
  {Γ₀} {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {.(Ω₁ ++ H ∷ Ω₂)} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (H , Ω₂ , refl , refl)
  rewrite cases++-inj₁ Ω Ω₁ (H ∷ Ω₂ ++ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ₁
            (Γ₀ ++ Ω₀ ++ F ∷ Ω ++ (A' ⇒ B') ∷ Ω₁)
            (H ∷ Ω₂ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ B' ∷ Ω₁)
            (H ∷ Ω₂ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ Ω₀)
            (F ∷ Ω ++ (A' ⇒ B') ∷ Ω₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Γ₀ (B' ∷ Ω₁) (B ⇐ A) |
          ++?-inj₂ (Γ₀ ++ Ω₀ ++ F ∷ Ω ++ (A' ⇒ B') ∷ Ω₁)
            Ω₂ Λ₁ H |
          ++?-inj₂ (Γ₀ ++ B' ∷ Ω₁) Ω₂ Λ₁ H |
          ++?-inj₂ (Γ₀ ++ Ω₀) Ω ((A' ⇒ B') ∷ Ω₁ ++ H ∷ Ω₂) F |
          cases++-inj₂ Ω₀ Γ₀ Ω F |
          cases++-inj₁ Ω Ω₁ (H ∷ Ω₂) (A' ⇒ B') =
    intrp≗ (⇒L⇐L~⇒Δ
      (mip [] Ω₀ (F ∷ Ω) f refl)
      (mip Γ₀ (B' ∷ Ω₁) (H ∷ Ω₂) g refl)
      h)
mip≗⇒L⇐L-assoc .(Γ₁ ++ B ⇐ A ∷ Γ₀ ++ Ω₀) (F ∷ Δ)
  .(Ω₁ ++ A' ⇒ B' ∷ Λ₀ ++ Λ₁)
  {Γ₀} {Γ₁} {.(Ω₀ ++ F ∷ Δ ++ Ω₁)} {Λ₀} {Λ₁}
  {A} {B} {A'} {B'} {C} {f} {g} {h} refl
  | inj₂ (F , .(Δ ++ Ω₁) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  rewrite cases++-inj₂ Ω₁ Δ (Λ₀ ++ Λ₁) (A' ⇒ B') |
          cases++-inj₁ Γ₁ (Γ₀ ++ Ω₀ ++ F ∷ Δ)
            (Ω₁ ++ (A' ⇒ B') ∷ Λ₀ ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ (Γ₀ ++ Ω₀) (F ∷ Δ) (B ⇐ A)
  with Ω₁
... | []
  rewrite ++?-inj₂ (Γ₀ ++ Ω₀ ++ F ∷ Δ) Λ₀ Λ₁ (A' ⇒ B') |
          ++?-inj₂ (Γ₀ ++ Ω₀) Δ ((A' ⇒ B') ∷ Λ₀) F |
          cases++-inj₂ Ω₀ Γ₀ Δ F |
          cases++-inj₂ [] Δ Λ₀ (A' ⇒ B') =
    intrp≗ (g~ ⇒L⇐L-assoc)
... | H ∷ Ω₂
  rewrite ++?-inj₂ (Γ₀ ++ Ω₀ ++ F ∷ Δ)
            (Ω₂ ++ (A' ⇒ B') ∷ Λ₀) Λ₁ H |
          ++?-inj₂ (Γ₀ ++ Ω₀) (Δ ++ H ∷ Ω₂)
            ((A' ⇒ B') ∷ Λ₀) F |
          cases++-inj₂ Ω₀ Γ₀ (Δ ++ H ∷ Ω₂) F |
          cases++-inj₂ (H ∷ Ω₂) Δ Λ₀ (A' ⇒ B') =
    intrp≗ (g~ ⇒L⇐L-assoc)
