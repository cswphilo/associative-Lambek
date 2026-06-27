{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.ImpLLeftImpLComm where

open import IntrpWellDefCases.Base

mip≗⇒L⇐L-comm : ∀ Γ Δ Λ
  {Γ₁ Δ₀ Δ₁ Λ₁ Ξ : Cxt} {A B A' B' C : Fma}
  {f : Δ₀ ⊢ A} {f' : Δ₁ ⊢ A'} {g : Γ₁ ++ B ∷ Λ₁ ++ B' ∷ Ξ ⊢ C}
  → (eq : Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ C
      (mip Γ Δ Λ (⇒L {Γ₁} {Δ₀} {Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ} f (⇐L {Γ₁ ++ B ∷ Λ₁} {Δ₁} {Ξ} f' g)) eq)
      (mip Γ Δ Λ (⇐L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁} {Δ₁} {Ξ} f' (⇒L {Γ₁} {Δ₀} {Λ₁ ++ B' ∷ Ξ} f g)) eq)
mip≗⇒L⇐L-comm Γ [] Λ eq = mip[]≗ Γ Λ eq ⇒L⇐L-comm
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  with ++? Γ (Γ₁ ++ Δ₀) (E ∷ Δ ++ Λ) (A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ) eq
... | inj₁ (Ω , eq₁ , eq₂)
  with cases∷ Ω eq₁
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₁ (eq₃ , eq₄ , eq₅)
  with cases++ Λ₁ Δ (Δ₁ ++ Ξ) Λ eq₅
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₁ (eq₃ , eq₄ , eq₅)
  | inj₁ (Ω₀ , eq₆ , eq₇)
  with ++? Ω₀ Δ₁ Λ Ξ eq₇
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀) (.(A ⇒ B) ∷ .(Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ω₁)) Λ
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {.(Ω₁ ++ Λ)} {A} {B} {A'} {B'} {f} {f'} {g} refl
  | inj₁ (.[] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (.(Δ₁ ++ Ω₁) , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Δ₁ ++ Ω₁) Λ (B' ⇐ A') |
          cases++-inj₂ (B ∷ Λ₁) Γ₁ (Δ₁ ++ Ω₁) (B' ⇐ A') |
          ++?-inj₁ Ω₁ Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Δ₁ ++ Ω₁) Λ (B' ⇐ A') |
          cases++-inj₂ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₀) (Δ₁ ++ Ω₁) (B' ⇐ A') |
          ++?-inj₁ Ω₁ Δ₁ Λ |
          ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₁ ++ Λ) =
    intrp≗ (h~ (⇒R ⇒L⇐L-comm ∘ (~ ⇐L⇒R)))
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀) (.(A ⇒ B) ∷ .(Λ₁ ++ B' ⇐ A' ∷ Ω₀)) .(F ∷ Ω₁ ++ Ξ)
  {Γ₁} {Δ₀} {.(Ω₀ ++ F ∷ Ω₁)} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f} {f'} {g} refl
  | inj₁ (.[] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (F , Ω₁ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Ω₀ (F ∷ Ω₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (B ∷ Λ₁) Γ₁ Ω₀ (B' ⇐ A') |
          ++?-inj₂ Ω₀ Ω₁ Ξ F |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₀ (F ∷ Ω₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₀) Ω₀ (B' ⇐ A') |
          ++?-inj₂ Ω₀ Ω₁ Ξ F |
          ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) =
    let n = mip [] Δ₀ [] f refl
        m = mip Γ₁ (B ∷ Λ₁ ++ B' ∷ []) Ξ g refl
        p = mip Ω₀ (F ∷ Ω₁) [] f' refl
        t = ⇒R (⇐R (⇐L {Γ = MIP.D n ∷ []} ax (⇒L {Γ = []} ax ax)))
        P = Γ₁ ++ MIP.D n ∷ ((MIP.D n ⇒ MIP.D m) ⇐ MIP.D p) ∷ []
        s1 =
          ⇐L {Γ = Γ₁ ++ Δ₀} {Δ = F ∷ Ω₁} {Λ = Ξ}
            {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
            refl
            (⇒L {Γ = Γ₁} {Δ = Δ₀} {Λ = Ξ}
              {A = MIP.D n} {B = MIP.D m}
              (~ cutaxA-right (MIP.h n)) refl)
        s2 =
          ⇐L {Γ = Γ₁ ++ Δ₀} {Δ = F ∷ Ω₁} {Λ = Ξ}
            {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
            refl
            (~ (≡to≗
              (cut⇒L-cases++₁ [] Γ₁ {Λ = []} {Λ₁ = Ξ}
                {A = MIP.D n} {B = MIP.D m} {C = C}
                {D = MIP.D n} {f = MIP.h n} {g = ax}
                {h = MIP.g m})))
        s3 = ~ (≡to≗ (cut⇐L-cases++-comm₂ Γ₁ []))
        s4 =
          cut-cong₂ Γ₁ refl
            (~ (≡to≗ (cut⇐L-cases++₁ [] (Γ₁ ++ MIP.D n ∷ []))))
        s5 =
          cut-cong₂ Γ₁ refl
            (cut-cong₂ P refl
              (⇐L {Γ = Γ₁ ++ MIP.D n ∷ []}
                {Δ = MIP.D p ∷ []} {Λ = Ξ}
                {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
                refl
                (⇒L {Γ = Γ₁} {Δ = MIP.D n ∷ []} {Λ = Ξ}
                  {A = MIP.D n} {B = MIP.D m}
                  refl (~ cutaxA-left Γ₁ (MIP.g m) refl))))
        s6 =
          cut-cong₂ Γ₁ refl
            (cut-cong₂ P refl
              (⇐L {Γ = Γ₁ ++ MIP.D n ∷ []}
                {Δ = MIP.D p ∷ []} {Λ = Ξ}
                {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
                refl
                (~ (cut⇒L≗ Γ₁ ax ax (MIP.g m) refl))))
        s7 =
          cut-cong₂ Γ₁ refl
            (cut-cong₂ P refl
              (~ (cut⇐L≗ Γ₁ ax
                (⇒L {Γ = []} {Δ = MIP.D n ∷ []} {Λ = []}
                  {A = MIP.D n} {B = MIP.D m}
                  ax ax)
                (MIP.g m) refl)))
        s8 =
          cut-cong₂ Γ₁ refl
            (~ (≡to≗ (cut⇐R⇐Lcases++ Γ₁ Ξ (F ∷ Ω₁))))
        s9 = ~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (F ∷ Ω₁ ++ Ξ) Δ₀))
    in
    intrp≗
      (↜∷
        (t ,
          ((((((((s1 ∘ s2) ∘ s3) ∘ s4) ∘ s5) ∘ s6) ∘ s7) ∘ s8) ∘ s9) ,
          ⇒R
            (((⇐R
              (cutaxA-left
                (MIP.D n ∷ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω₀)
                (⇐L (MIP.g p)
                  (⇒L {Γ = []} {Δ = MIP.D n ∷ []} {Λ = Λ₁ ++ B' ∷ []}
                    {A = A} {B = B}
                    (cut [] ax (MIP.g n) refl) (MIP.h m)))
                refl)
              ∘ ⇐R
                  (⇐L {Γ = MIP.D n ∷ A ⇒ B ∷ Λ₁}
                    {Δ = Ω₀ ++ MIP.D p ∷ []} {Λ = []}
                    {A = A'} {B = B'}
                    refl
                    (⇒L (cutaxA-left [] (MIP.g n) refl) refl)))
             ∘ ⇐R (~ ⇒L⇐L-comm))
            ∘ (~ ⇒L⇐R)))
        refl)
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₁ (eq₃ , eq₄ , eq₅)
  | inj₂ (Ω₀ , eq₆ , eq₇) with ++? Δ Λ₁ Ω₀ [] eq₇
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀) (.(A ⇒ B) ∷ Δ) .(B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {Γ₁} {Δ₀} {Δ₁} {.Δ} {Ξ} {A} {B} {A'} {B'} {C} {f} {f'} {g} refl
  | inj₁ (.[] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (.[] , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₂ [] (Γ₁ ++ B ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Δ ++ B' ∷ Ξ) =
    intrp≗ (g~ ⇒L⇐L-comm)
... | inj₁ (F ∷ Ω₁ , () , eq₉)
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀) (.(A ⇒ B) ∷ Δ) .(F ∷ Ω₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {Γ₁} {Δ₀} {Δ₁} {.(Δ ++ F ∷ Ω₁)} {Ξ} {A} {B} {A'} {B'} {C} {f} {f'} {g} refl
  | inj₁ (.[] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (.(F ∷ Ω₁) , refl , refl)
  | inj₂ (F , Ω₁ , refl , refl)
  rewrite cases++-inj₂ (F ∷ Ω₁) (Γ₁ ++ B ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (F ∷ Ω₁) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₁ [] (Γ₁ ++ Δ₀) (A ⇒ B ∷ Δ ++ F ∷ Ω₁ ++ B' ∷ Ξ) =
    intrp≗ (g~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , eq₄)
  with cases++ Λ₁ Ω' (Δ₁ ++ Ξ) (E ∷ Δ ++ Λ) (sym eq₃)
... | inj₁ (Ω'' , eq₅ , eq₆)
  with ++? (Ω'' ++ E ∷ Δ) Δ₁ Λ Ξ eq₆
... | inj₁ (Ω''' , eq₇ , eq₈)
  with ++? Δ₁ Ω'' Ω''' (E ∷ Δ) eq₈
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω'') (E ∷ Δ) Λ
  {Γ₁} {Δ₀} {Ω''} {Λ₁} {.(E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω'') , refl , refl)
  | inj₂ (.(Λ₁ ++ B' ⇐ A' ∷ Ω'') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (.(E ∷ Δ) , refl , refl)
  | inj₁ ([] , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Ω'' ++ E ∷ Δ) Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Ω'' ++ E ∷ Δ) Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Ω'' (E ∷ Δ) (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω'' (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₁ (E ∷ Δ) Ω'' Λ |
          ++?-inj₁ [] Ω'' (E ∷ Δ) |
          ++?-inj₁ (A ⇒ B ∷ Λ₁ ++ B' ∷ []) (Γ₁ ++ Δ₀) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ((~ (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₀} {Λ = Λ₁ ++ B' ⇐ A' ∷ Ω''}
      {Ω = Λ}
      {A' = I}
      {B' = MIP.D (mip (Γ₁ ++ B ∷ Λ₁ ++ B' ∷ []) (E ∷ Δ) Λ g refl)}))
      ∘ (⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω''}
        (⇒L⇐L-comm {Γ = Γ₁} {Δ₀ = Δ₀}
          {Δ₁ = Ω'' ++ I ∷ []}
          {Λ = Λ₁}
          {Ξ = MIP.D (mip (Γ₁ ++ B ∷ Λ₁ ++ B' ∷ []) (E ∷ Δ) Λ g refl) ∷ Λ}))))
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω'') (E ∷ .(Ω₅ ++ Ω₆)) Λ
  {Γ₁} {Δ₀} {.(Ω'' ++ E ∷ Ω₅)} {Λ₁} {.(Ω₆ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω'') , refl , refl)
  | inj₂ (.(Λ₁ ++ B' ⇐ A' ∷ Ω'') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω₆ , refl , refl)
  | inj₁ (E ∷ Ω₅ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Ω'' ++ E ∷ Ω₅ ++ Ω₆) Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Ω'' ++ E ∷ Ω₅ ++ Ω₆) Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Ω'' (E ∷ Ω₅ ++ Ω₆) (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω'' (E ∷ Ω₅ ++ Ω₆) (B' ⇐ A') |
          ++?-inj₁ Ω₆ (Ω'' ++ E ∷ Ω₅) Λ |
          ++?-inj₁ (E ∷ Ω₅) Ω'' Ω₆ =
    intrp≗
      (~-trans
        (g~ ((~ (⊗L⇒L-comm₂ {Γ = Γ₁} {Δ = Δ₀} {Λ = Λ₁ ++ B' ⇐ A' ∷ Ω''}
          {Ω = Λ}
          {A' = MIP.D (mip Ω'' (E ∷ Ω₅) [] f' refl)}
          {B' = MIP.D (mip (Γ₁ ++ B ∷ Λ₁ ++ B' ∷ []) Ω₆ Λ g refl)}))
          ∘ (⊗L {Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω''}
            (⇒L⇐L-comm {Γ = Γ₁} {Δ₀ = Δ₀}
              {Δ₁ = Ω'' ++ MIP.D (mip Ω'' (E ∷ Ω₅) [] f' refl) ∷ []}
              {Λ = Λ₁}
              {Ξ = MIP.D (mip (Γ₁ ++ B ∷ Λ₁ ++ B' ∷ []) Ω₆ Λ g refl) ∷ Λ}))))
        (~-sym
          (⇐L~⊗ {Γ₀ = Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁}
            {Γ₁ = Ω''} {Δ₀ = E ∷ Ω₅} {Δ₁ = Ω₆} {Λ = Λ}
            {A = A'} {B = B'}
            refl (mip⇒L~Γ Γ₁ (Λ₁ ++ B' ∷ []) Ω₆ Λ))))
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ F ∷ Ω'''') (E ∷ Δ) Λ
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {.(F ∷ Ω'''' ++ E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ F ∷ Ω'''') , refl , refl)
  | inj₂ (.(Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ F ∷ Ω'''') , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω'''') , refl , refl)
  | inj₁ (.(F ∷ Ω'''' ++ E ∷ Δ) , refl , refl)
  | inj₂ (F , Ω'''' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Δ₁ ++ F ∷ Ω'''' ++ E ∷ Δ) Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Δ₁ ++ F ∷ Ω'''' ++ E ∷ Δ) Λ (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Δ₁ ++ F ∷ Ω'''') (E ∷ Δ) (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Δ₁ ++ F ∷ Ω'''') (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₁ (F ∷ Ω'''' ++ E ∷ Δ) Δ₁ Λ |
          ++?-inj₂ Δ₁ Ω'''' (E ∷ Δ) F |
          ++?-inj₁ (A ⇒ B ∷ Λ₁ ++ B' ∷ F ∷ Ω'''') (Γ₁ ++ Δ₀) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω'') (E ∷ Δ) .(F ∷ Ω''' ++ Ξ)
  {Γ₁} {Δ₀} {.(Ω'' ++ E ∷ Δ ++ F ∷ Ω''')} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω'') , refl , refl)
  | inj₂ (.(Λ₁ ++ B' ⇐ A' ∷ Ω'') , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Ω'' ++ E ∷ Δ) (F ∷ Ω''' ++ Ξ) (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Ω'' ++ E ∷ Δ) (F ∷ Ω''' ++ Ξ) (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Ω'' (E ∷ Δ) (B' ⇐ A') |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω'' (E ∷ Δ) (B' ⇐ A') |
          ++?-inj₂ (Ω'' ++ E ∷ Δ) Ω''' Ξ F =
    intrp≗ (g~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , eq₄)
  | inj₂ (Ω'' , eq₅ , eq₆) with cases++ Ω'' (E ∷ Δ) (Δ₁ ++ Ξ) Λ eq₅
... | inj₁ (Ω₀ , eq₇ , eq₈) with cases∷ Ω'' eq₇
... | inj₁ (eq₉ , eq₁₀ , eq₁₁) with ++? Ω₀ Δ₁ Λ Ξ eq₈
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (.(B' ⇐ A') ∷ .(Δ₁ ++ Ω₂)) Λ
  {Γ₁} {Δ₀} {Δ₁} {Λ₁} {.(Ω₂ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₂ (Λ₁ , refl , refl)
  | inj₂ (.[] , refl , refl)
  | inj₁ (.(Δ₁ ++ Ω₂) , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Δ₁ ++ Ω₂) Λ (B' ⇐ A') |
          cases++-inj₂ [] (Γ₁ ++ B ∷ Λ₁) (Δ₁ ++ Ω₂) (B' ⇐ A') |
          ++?-inj₁ Ω₂ Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Δ₁ ++ Ω₂) Λ (B' ⇐ A') |
          cases++-inj₂ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Δ₁ ++ Ω₂) (B' ⇐ A') |
          ++?-inj₁ Ω₂ Δ₁ Λ |
          ++?-inj₁ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₀) (B' ∷ Ω₂ ++ Λ) =
    intrp≗ refl
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (.(B' ⇐ A') ∷ Δ) .(F ∷ Ω₂ ++ Ξ)
  {Γ₁} {Δ₀} {.(Δ ++ F ∷ Ω₂)} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₁) , refl , refl)
  | inj₂ (Λ₁ , refl , refl)
  | inj₂ (.[] , refl , refl)
  | inj₁ (Δ , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Δ (F ∷ Ω₂ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ [] (Γ₁ ++ B ∷ Λ₁) Δ (B' ⇐ A') |
          ++?-inj₂ Δ Ω₂ Ξ F |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ (F ∷ Ω₂ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ [] (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Δ (B' ⇐ A') |
          ++?-inj₂ Δ Ω₂ Ξ F |
          ++?-inj₁ (A ⇒ B ∷ Λ₁) (Γ₁ ++ Δ₀) (B' ∷ Ξ) =
    intrp≗ (g~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₁ (Ω , eq₁ , eq₂)
  | inj₂ (Ω' , eq₃ , eq₄)
  | inj₂ (Ω'' , eq₅ , eq₆)
  | inj₁ (Ω₀ , eq₇ , eq₈)
  | inj₂ (Ω₁ , eq₉ , eq₁₀) with ++? Ω₀ Δ₁ Λ Ξ eq₈
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀) (E ∷ .(Ω₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ω₂)) Λ
  {Γ₁} {Δ₀} {Δ₁} {.(Λ₀ ++ E ∷ Ω₁)} {.(Ω₂ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₀) , refl , refl)
  | inj₂ (Λ₀ , refl , refl)
  | inj₂ (.(E ∷ Ω₁) , refl , refl)
  | inj₁ (.(Δ₁ ++ Ω₂) , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₀ ++ E ∷ Ω₁) (Δ₁ ++ Ω₂) Λ (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₁) (Γ₁ ++ B ∷ Λ₀) (Δ₁ ++ Ω₂) (B' ⇐ A') |
          ++?-inj₁ Ω₂ Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀ ++ E ∷ Ω₁) (Δ₁ ++ Ω₂) Λ (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₁) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀) (Δ₁ ++ Ω₂) (B' ⇐ A') |
          ++?-inj₁ Ω₂ Δ₁ Λ |
          ++?-inj₁ (A ⇒ B ∷ Λ₀) (Γ₁ ++ Δ₀) (E ∷ Ω₁ ++ B' ∷ Ω₂ ++ Λ) =
    intrp≗ refl
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀) (E ∷ .(Ω₁ ++ B' ⇐ A' ∷ Ω₀)) .(F ∷ Ω₂ ++ Ξ)
  {Γ₁} {Δ₀} {.(Ω₀ ++ F ∷ Ω₂)} {.(Λ₀ ++ E ∷ Ω₁)} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₀) , refl , refl)
  | inj₂ (Λ₀ , refl , refl)
  | inj₂ (.(E ∷ Ω₁) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  | inj₂ (F , Ω₂ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₀ ++ E ∷ Ω₁) Ω₀ (F ∷ Ω₂ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₁) (Γ₁ ++ B ∷ Λ₀) Ω₀ (B' ⇐ A') |
          ++?-inj₂ Ω₀ Ω₂ Ξ F |
          cases++-inj₁ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀ ++ E ∷ Ω₁) Ω₀ (F ∷ Ω₂ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₁) (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀) Ω₀ (B' ⇐ A') |
          ++?-inj₂ Ω₀ Ω₂ Ξ F |
          ++?-inj₁ (A ⇒ B ∷ Λ₀) (Γ₁ ++ Δ₀) (E ∷ Ω₁ ++ B' ∷ Ξ) =
    intrp≗ (g~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm .(Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀) (E ∷ Δ) .(Ω₀ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {Γ₁} {Δ₀} {Δ₁} {.(Λ₀ ++ E ∷ Δ ++ Ω₀)} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₁ (.(A ⇒ B ∷ Λ₀) , refl , refl)
  | inj₂ (Λ₀ , refl , refl)
  | inj₂ (.(E ∷ Δ ++ Ω₀) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  rewrite cases++-inj₂ Ω₀ (Γ₁ ++ B ∷ Λ₀ ++ E ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ Ω₀ (Γ₁ ++ Δ₀ ++ A ⇒ B ∷ Λ₀ ++ E ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₁ (A ⇒ B ∷ Λ₀) (Γ₁ ++ Δ₀) (E ∷ Δ ++ Ω₀ ++ B' ∷ Ξ) =
    intrp≗ (g~ (⇒L⇐L-comm {Γ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁}
      {Λ = Λ₀ ++ MIP.D (mip (Γ₁ ++ B ∷ Λ₀) (E ∷ Δ) (Ω₀ ++ B' ∷ Ξ) g refl) ∷ Ω₀}
      {Ξ = Ξ}))
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₂ (F , Ω , eq₁ , eq₂) with cases++ Γ Γ₁ Ω Δ₀ eq₁
... | inj₁ (Ω₀ , refl , refl)
  with cases++ (Ω₀ ++ Δ₀) Δ (Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ) Λ (inj∷ eq₂ .proj₂)
... | inj₁ (Ω₁ , refl , eq₄)
  with cases++ Λ₁ Ω₁ (Δ₁ ++ Ξ) Λ (sym eq₄)
... | inj₁ (Ω₂ , refl , eq₅) with ++? Ω₂ Δ₁ Λ Ξ eq₅
mip≗⇒L⇐L-comm Γ (E ∷ .(Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ω₃)) Λ
  {.(Γ ++ E ∷ Ω₀)} {Δ₀} {Δ₁} {Λ₁} {.(Ω₃ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ω₃) , refl , refl)
  | inj₁ (.(Δ₁ ++ Ω₃) , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω₀ ++ B ∷ Λ₁) (Δ₁ ++ Ω₃) Λ (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₀ ++ B ∷ Λ₁) Γ (Δ₁ ++ Ω₃) (B' ⇐ A') |
          ++?-inj₁ Ω₃ Δ₁ Λ |
          cases++-inj₁ (Γ ++ E ∷ Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Δ₁ ++ Ω₃) Λ (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Γ (Δ₁ ++ Ω₃) (B' ⇐ A') |
          ++?-inj₁ Ω₃ Δ₁ Λ |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₃ ++ Λ) E |
          cases++-inj₁ Γ Ω₀ Δ₀ E |
          cases++-inj₁ (Ω₀ ++ Δ₀) (Λ₁ ++ B' ∷ Ω₃) Λ (A ⇒ B) =
    intrp≗ (h~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm Γ (E ∷ .(Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω₂)) .(F' ∷ Ω₃ ++ Ξ)
  {.(Γ ++ E ∷ Ω₀)} {Δ₀} {.(Ω₂ ++ F' ∷ Ω₃)} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₁ ++ B' ⇐ A' ∷ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  | inj₂ (F' , Ω₃ , refl , refl)
  rewrite cases++-inj₁ (Γ ++ E ∷ Ω₀ ++ B ∷ Λ₁) Ω₂ (F' ∷ Ω₃ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₀ ++ B ∷ Λ₁) Γ Ω₂ (B' ⇐ A') |
          ++?-inj₂ Ω₂ Ω₃ Ξ F' |
          cases++-inj₁ (Γ ++ E ∷ Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Ω₂ (F' ∷ Ω₃ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (E ∷ Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) Γ Ω₂ (B' ⇐ A') |
          ++?-inj₂ Ω₂ Ω₃ Ξ F' |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ Δ₀ E |
          cases++-inj₁ (Ω₀ ++ Δ₀) (Λ₁ ++ B' ∷ []) Ξ (A ⇒ B) =
    intrp≗ (h~ (⇒L⇐R ∘ ⇐R ⇒L⇐L-comm))
mip≗⇒L⇐L-comm Γ (E ∷ .(Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Ω₁)) .(Ω₂ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {.(Γ ++ E ∷ Ω₀)} {Δ₀} {Δ₁} {.(Ω₁ ++ Ω₂)} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Δ₀) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  rewrite cases++-inj₂ Ω₂ (Γ ++ E ∷ Ω₀ ++ B ∷ Ω₁) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ Ω₂ (Γ ++ E ∷ Ω₀ ++ Δ₀ ++ A ⇒ B ∷ Ω₁) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₂ Γ (Ω₀ ++ Δ₀) (A ⇒ B ∷ Ω₁ ++ Ω₂ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ Δ₀ E |
          cases++-inj₁ (Ω₀ ++ Δ₀) Ω₁ (Ω₂ ++ B' ∷ Ξ) (A ⇒ B) =
    intrp≗ refl
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , eq₄) with ++? Δ Ω₀ Ω₁ Δ₀ eq₄
mip≗⇒L⇐L-comm Γ (E ∷ .(Ω₀ ++ Ω₂)) .(Ω₁ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {.(Γ ++ E ∷ Ω₀)} {.(Ω₂ ++ Ω₁)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (E , .(Ω₀ ++ Ω₂ ++ Ω₁) , refl , refl)
  | inj₁ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  | inj₁ (Ω₂ , refl , refl) with Ω₁
... | []
  rewrite cases++-inj₂ (B ∷ Λ₁) (Γ ++ E ∷ Ω₀) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (A ⇒ B ∷ Λ₁) (Γ ++ E ∷ Ω₀ ++ Ω₂) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₂ Γ (Ω₀ ++ Ω₂) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ Ω₂ E |
          cases++-inj₂ [] (Ω₀ ++ Ω₂) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Ω₀ [] =
    intrp≗ (g~ ((⊗L ⇒L⇐L-comm) ∘ ⊗L⇐L-comm₁))
... | H ∷ Ω₃
  rewrite cases++-inj₂ (B ∷ Λ₁) (Γ ++ E ∷ Ω₀) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (H ∷ Ω₃ ++ A ⇒ B ∷ Λ₁) (Γ ++ E ∷ Ω₀ ++ Ω₂) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₂ Γ (Ω₀ ++ Ω₂ ++ H ∷ Ω₃) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ Ω₀ (Ω₂ ++ H ∷ Ω₃) E |
          cases++-inj₂ (H ∷ Ω₃) (Ω₀ ++ Ω₂) (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₁ Ω₂ Ω₀ (H ∷ Ω₃) =
    intrp≗ (g~ ((⊗L ⇒L⇐L-comm) ∘ ⊗L⇐L-comm₁))
mip≗⇒L⇐L-comm Γ (E ∷ Δ) .(F' ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {.(Γ ++ E ∷ Δ ++ F' ∷ Ω₂)} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (E , .(Δ ++ F' ∷ Ω₂ ++ Δ₀) , refl , refl)
  | inj₁ (.(Δ ++ F' ∷ Ω₂) , refl , refl)
  | inj₂ (.(F' ∷ Ω₂ ++ Δ₀) , refl , refl)
  | inj₂ (F' , Ω₂ , refl , refl)
  rewrite cases++-inj₂ (F' ∷ Ω₂ ++ B ∷ Λ₁) (Γ ++ E ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (F' ∷ Ω₂ ++ Δ₀ ++ A ⇒ B ∷ Λ₁) (Γ ++ E ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₂ Γ (Δ ++ F' ∷ Ω₂ ++ Δ₀) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) E |
          cases++-inj₁ Γ (Δ ++ F' ∷ Ω₂) Δ₀ E |
          cases++-inj₂ (F' ∷ Ω₂ ++ Δ₀) Δ (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) |
          ++?-inj₂ Δ Ω₂ Δ₀ F' =
    intrp≗ (g~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm Γ (E ∷ Δ) Λ {Γ₁} {Δ₀} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {f} {f'} {g} eq
  | inj₂ (F , Ω , eq₁ , eq₂)
  | inj₂ (Ω₀ , refl , refl)
  with cases++ Ω Δ (Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ) Λ (inj∷ eq₂ .proj₂)
... | inj₁ (Ω₁ , refl , eq₅) with cases++ Λ₁ Ω₁ (Δ₁ ++ Ξ) Λ (sym eq₅)
... | inj₁ (Ω₂ , refl , eq₆) with ++? Ω₂ Δ₁ Λ Ξ eq₆
mip≗⇒L⇐L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ .(Ω ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ω₃)) Λ
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {Λ₁} {.(Ω₃ ++ Λ)} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ω₃) , refl , refl)
  | inj₁ (.(Δ₁ ++ Ω₃) , refl , refl)
  | inj₁ (Ω₃ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) (Δ₁ ++ Ω₃) Λ (B' ⇐ A') |
          cases++-inj₂ (B ∷ Λ₁) Γ₁ (Δ₁ ++ Ω₃) (B' ⇐ A') |
          ++?-inj₁ Ω₃ Δ₁ Λ |
          cases++-inj₁ (Γ₁ ++ Ω₀ ++ F ∷ Ω ++ A ⇒ B ∷ Λ₁) (Δ₁ ++ Ω₃) Λ (B' ⇐ A') |
          cases++-inj₂ (F ∷ Ω ++ A ⇒ B ∷ Λ₁) (Γ₁ ++ Ω₀) (Δ₁ ++ Ω₃) (B' ⇐ A') |
          ++?-inj₁ Ω₃ Δ₁ Λ |
          ++?-inj₂ (Γ₁ ++ Ω₀) Ω (A ⇒ B ∷ Λ₁ ++ B' ∷ Ω₃ ++ Λ) F |
          cases++-inj₂ Ω₀ Γ₁ Ω F |
          cases++-inj₁ Ω (Λ₁ ++ B' ∷ Ω₃) Λ (A ⇒ B) =
    intrp≗ (h~ (⇒R ⇒L⇐L-comm ∘ (~ ⇐L⇒R)))
mip≗⇒L⇐L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ .(Ω ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω₂)) .(F' ∷ Ω₃ ++ Ξ)
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {.(Ω₂ ++ F' ∷ Ω₃)} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (.(Λ₁ ++ B' ⇐ A' ∷ Ω₂) , refl , refl)
  | inj₁ (Ω₂ , refl , refl)
  | inj₂ (F' , Ω₃ , refl , refl)
  rewrite cases++-inj₁ (Γ₁ ++ B ∷ Λ₁) Ω₂ (F' ∷ Ω₃ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (B ∷ Λ₁) Γ₁ Ω₂ (B' ⇐ A') |
          ++?-inj₂ Ω₂ Ω₃ Ξ F' |
          cases++-inj₁ (Γ₁ ++ Ω₀ ++ F ∷ Ω ++ A ⇒ B ∷ Λ₁) Ω₂ (F' ∷ Ω₃ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ (F ∷ Ω ++ A ⇒ B ∷ Λ₁) (Γ₁ ++ Ω₀) Ω₂ (B' ⇐ A') |
          ++?-inj₂ Ω₂ Ω₃ Ξ F' |
          ++?-inj₂ (Γ₁ ++ Ω₀) Ω (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) F |
          cases++-inj₂ Ω₀ Γ₁ Ω F |
          cases++-inj₁ Ω (Λ₁ ++ B' ∷ []) Ξ (A ⇒ B) =
    let n = mip [] Ω₀ (F ∷ Ω) f refl
        m = mip Γ₁ (B ∷ Λ₁ ++ B' ∷ []) Ξ g refl
        p = mip Ω₂ (F' ∷ Ω₃) [] f' refl
        t = ⇒R (⇐R (⇐L {Γ = MIP.D n ∷ []} ax (⇒L {Γ = []} ax ax)))
        P = Γ₁ ++ MIP.D n ∷ ((MIP.D n ⇒ MIP.D m) ⇐ MIP.D p) ∷ []
        s1 =
          ⇐L {Γ = Γ₁ ++ Ω₀} {Δ = F' ∷ Ω₃} {Λ = Ξ}
            {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
            refl
            (⇒L {Γ = Γ₁} {Δ = Ω₀} {Λ = Ξ}
              {A = MIP.D n} {B = MIP.D m}
              (~ cutaxA-right (MIP.h n)) refl)
        s2 =
          ⇐L {Γ = Γ₁ ++ Ω₀} {Δ = F' ∷ Ω₃} {Λ = Ξ}
            {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
            refl
            (~ (≡to≗
              (cut⇒L-cases++₁ [] Γ₁ {Λ = []} {Λ₁ = Ξ}
                {A = MIP.D n} {B = MIP.D m} {C = C}
                {D = MIP.D n} {f = MIP.h n} {g = ax}
                {h = MIP.g m})))
        s3 = ~ (≡to≗ (cut⇐L-cases++-comm₂ Γ₁ []))
        s4 =
          cut-cong₂ Γ₁ refl
            (~ (≡to≗ (cut⇐L-cases++₁ [] (Γ₁ ++ MIP.D n ∷ []))))
        s5 =
          cut-cong₂ Γ₁ refl
            (cut-cong₂ P refl
              (⇐L {Γ = Γ₁ ++ MIP.D n ∷ []}
                {Δ = MIP.D p ∷ []} {Λ = Ξ}
                {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
                refl
                (⇒L {Γ = Γ₁} {Δ = MIP.D n ∷ []} {Λ = Ξ}
                  {A = MIP.D n} {B = MIP.D m}
                  refl (~ cutaxA-left Γ₁ (MIP.g m) refl))))
        s6 =
          cut-cong₂ Γ₁ refl
            (cut-cong₂ P refl
              (⇐L {Γ = Γ₁ ++ MIP.D n ∷ []}
                {Δ = MIP.D p ∷ []} {Λ = Ξ}
                {A = MIP.D p} {B = MIP.D n ⇒ MIP.D m}
                refl
                (~ (cut⇒L≗ Γ₁ ax ax (MIP.g m) refl))))
        s7 =
          cut-cong₂ Γ₁ refl
            (cut-cong₂ P refl
              (~ (cut⇐L≗ Γ₁ ax
                (⇒L {Γ = []} {Δ = MIP.D n ∷ []} {Λ = []}
                  {A = MIP.D n} {B = MIP.D m}
                  ax ax)
                (MIP.g m) refl)))
        s8 =
          cut-cong₂ Γ₁ refl
            (~ (≡to≗ (cut⇐R⇐Lcases++ Γ₁ Ξ (F' ∷ Ω₃))))
        s9 = ~ (≡to≗ (cut⇒R⇒Lcases++ Γ₁ (F' ∷ Ω₃ ++ Ξ) Ω₀))
    in
    intrp≗
      (↜∷
        (t ,
          ((((((((s1 ∘ s2) ∘ s3) ∘ s4) ∘ s5) ∘ s6) ∘ s7) ∘ s8) ∘ s9) ,
          ⇒R
            (((⇐R
              (cutaxA-left
                (MIP.D n ∷ F ∷ Ω ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Ω₂)
                (⇐L (MIP.g p)
                  (⇒L {Γ = []} {Δ = MIP.D n ∷ F ∷ Ω} {Λ = Λ₁ ++ B' ∷ []}
                    {A = A} {B = B}
                    (cut [] ax (MIP.g n) refl) (MIP.h m)))
                refl)
              ∘ ⇐R
                  (⇐L {Γ = MIP.D n ∷ F ∷ Ω ++ A ⇒ B ∷ Λ₁}
                    {Δ = Ω₂ ++ MIP.D p ∷ []} {Λ = []}
                    {A = A'} {B = B'}
                    refl
                    (⇒L (cutaxA-left [] (MIP.g n) refl) refl)))
             ∘ ⇐R (~ ⇒L⇐L-comm))
            ∘ (~ ⇒L⇐R)))
        refl)
mip≗⇒L⇐L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ .(Ω ++ A ⇒ B ∷ Ω₁)) .(Ω₂ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {Γ₁} {.(Ω₀ ++ F ∷ Ω)} {Δ₁} {.(Ω₁ ++ Ω₂)} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (F , Ω , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₁ (Ω₁ , refl , refl)
  | inj₂ (Ω₂ , refl , refl)
  rewrite cases++-inj₂ Ω₂ (Γ₁ ++ B ∷ Ω₁) (Δ₁ ++ Ξ) (B' ⇐ A') |
          cases++-inj₂ Ω₂ (Γ₁ ++ Ω₀ ++ F ∷ Ω ++ A ⇒ B ∷ Ω₁) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₂ (Γ₁ ++ Ω₀) Ω (A ⇒ B ∷ Ω₁ ++ Ω₂ ++ B' ∷ Ξ) F |
          cases++-inj₂ Ω₀ Γ₁ Ω F |
          cases++-inj₁ Ω Ω₁ (Ω₂ ++ B' ∷ Ξ) (A ⇒ B) =
    intrp≗ (g~ ⇒L⇐L-comm)
mip≗⇒L⇐L-comm .(Γ₁ ++ Ω₀) (.(F) ∷ Δ) .(Ω₁ ++ A ⇒ B ∷ Λ₁ ++ B' ⇐ A' ∷ Δ₁ ++ Ξ)
  {Γ₁} {.(Ω₀ ++ F ∷ Δ ++ Ω₁)} {Δ₁} {Λ₁} {Ξ} {A} {B} {A'} {B'} {C} {f = f} {f'} {g} refl
  | inj₂ (F , .(Δ ++ Ω₁) , refl , refl)
  | inj₂ (Ω₀ , refl , refl)
  | inj₂ (Ω₁ , refl , refl)
  rewrite cases++-inj₂ (Ω₁ ++ A ⇒ B ∷ Λ₁) (Γ₁ ++ Ω₀ ++ F ∷ Δ) (Δ₁ ++ Ξ) (B' ⇐ A') |
          ++?-inj₂ (Γ₁ ++ Ω₀) (Δ ++ Ω₁) (A ⇒ B ∷ Λ₁ ++ B' ∷ Ξ) F |
          cases++-inj₂ Ω₀ Γ₁ (Δ ++ Ω₁) F |
          cases++-inj₂ Ω₁ Δ (Λ₁ ++ B' ∷ Ξ) (A ⇒ B) =
    intrp≗ (g~ ⇒L⇐L-comm)
